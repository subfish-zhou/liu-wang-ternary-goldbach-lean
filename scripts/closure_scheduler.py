"""Bounded cross-process Lean scheduler for a single writable project tree.

One compiler per caller, at most four globally. Module readers lock their entire
local import closure; writers are exclusive. The legacy build lock is shared,
so an old exclusive-lock caller cannot race new callers during migration.
"""
from contextlib import contextmanager, ExitStack
from pathlib import Path
from typing import Any
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import uuid


class BuildFailure(Exception):
    def __init__(self, message, code=1):
        super().__init__(message)
        self.code = code


def atomic_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2))
    os.replace(tmp, path)


@contextmanager
def locked(path, mode=fcntl.LOCK_EX, inherited=None):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a') as stream:
        fcntl.flock(stream, mode)
        if inherited is not None:
            inherited.add(stream.fileno())
        try:
            yield stream
        finally:
            if inherited is not None:
                inherited.discard(stream.fileno())
            fcntl.flock(stream, fcntl.LOCK_UN)


@contextmanager
def capacity(directory, limit, inherited=None):
    """OS locks survive until a killed caller's compiler also exits."""
    directory.mkdir(parents=True, exist_ok=True)
    handles = [(directory / f'{i}.lock').open('a') for i in range(limit)]
    selected = None
    try:
        while selected is None:
            for i, stream in enumerate(handles):
                try:
                    fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    selected = (i, stream)
                    break
                except BlockingIOError:
                    pass
            if selected is None:
                time.sleep(0.1)
        if inherited is not None:
            inherited.add(selected[1].fileno())
        yield selected[0]
    finally:
        if selected is not None and inherited is not None:
            inherited.discard(selected[1].fileno())
        for stream in handles:
            stream.close()


def uncomment(text):
    # Preserve line structure, handle nested Lean block comments and strings.
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; i += 2
            elif text.startswith('-/', i):
                depth -= 1; i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                i += 1; out.append(text[i])
            elif text[i] == '"':
                quoted = False
            i += 1
        elif text.startswith('/-', i):
            depth = 1; out.append(' '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            quoted = text[i] == '"'
            out.append(text[i]); i += 1
    return ''.join(out)


class Scheduler:
    def __init__(self, root, targets):
        self.root = root
        self.out = root / '.lake/local-closure'
        self.lib = root / '.lake/build/lib/lean'
        self.out.mkdir(parents=True, exist_ok=True)
        self.lib.mkdir(parents=True, exist_ok=True)
        self.request = uuid.uuid4().hex
        self.targets = targets
        self.inherited = set()
        self.hash_cache = {}
        self.records_stamp = None
        self.records = {}
        self.journal = self.out / 'modules.json'
        self.limit = 4
        self.progress: dict[str, Any] = dict(request=self.request, targets=targets, pid=os.getpid(),
                             scheduler='module-lock-v2', concurrency_limit=self.limit,
                             planned=0, passed=0, built=0, cached=0,
                             status='RUNNING', phase='DISCOVERY', started=time.time())
        self.save()
        self.modules = {}
        for directory, dirs, files in os.walk(root):
            dirs[:] = [d for d in dirs if d not in {'.lake', '.git', '__pycache__'}]
            for file in files:
                if file.endswith('.lean'):
                    p = Path(directory) / file
                    self.modules['.'.join(p.relative_to(root).with_suffix('').parts)] = p
        if not targets or any(m not in self.modules for m in targets):
            raise BuildFailure(f'unknown or empty targets: {targets}')
        self.order, self.deps, self.ancestors = [], {}, {}
        visited, visiting = set(), set()
        def visit(m):
            if m not in self.modules or m in visited:
                return
            if m in visiting:
                raise BuildFailure(f'cyclic imports: {m}')
            visiting.add(m)
            imports = []
            for line in uncomment(self.modules[m].read_text()).splitlines():
                match = re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*$', line)
                if match:
                    words = match.group(1).split()
                    if not all(re.fullmatch(r'[\w.]+', w) for w in words):
                        raise BuildFailure(f'unsupported import syntax: {m}: {line}')
                    imports.extend(words)
            self.deps[m] = imports
            ancestors = set()
            for d in imports:
                visit(d)
                if d in self.modules:
                    ancestors.add(d)
                    ancestors.update(self.ancestors[d])
            self.ancestors[m] = ancestors
            visiting.remove(m); visited.add(m); self.order.append(m)
        for m in targets:
            visit(m)
        self.sources = {m: self.digest(self.modules[m]) for m in self.order}
        self.base = self.digest(root / 'lean-toolchain') + self.digest(root / 'lake-manifest.json')
        self.keys = {}
        for m in self.order:
            self.keys[m] = hashlib.sha256((self.base + self.sources[m] +
                ''.join(self.keys.get(d, d) for d in self.deps[m])).encode()).hexdigest()
        self.progress['planned'] = len(self.order)
        self.env = dict(os.environ)
        self.env.pop('LEAN_PATH', None); self.env.pop('LEAN_SYSROOT', None)
        self.phase('WAIT_ENV')
        with locked(self.out / 'build.lock', fcntl.LOCK_SH, self.inherited):
            with locked(self.out / 'environment.lock'):
                for key, command in [('LEAN_PATH', ['printenv', 'LEAN_PATH']),
                                     ('lean', ['which', 'lean'])]:
                    value = subprocess.check_output(['lake', 'env'] + command, cwd=root,
                                                     env=self.env, text=True).strip()
                    if key == 'lean': self.lean = value
                    else: self.env[key] = value
        self.driver = root / 'scripts/ExactReplay.lean'
        self.driver_hash = self.digest(self.driver)
        self.gate_hash = self.digest(Path(__file__))
        self.core = Path(self.lean).resolve().parent.parent / 'lib/lean/LeanChecker.olean'
        self.core_hash = self.digest(self.core)

    def digest(self, p):
        s = p.stat()
        stamp = (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        old = self.hash_cache.get(p)
        if old and old[0] == stamp:
            return old[1]
        value = hashlib.sha256(p.read_bytes()).hexdigest()
        self.hash_cache[p] = (stamp, value)
        return value

    def save(self):
        self.progress['updated'] = time.time()
        atomic_json(self.out / 'requests' / (self.request + '.json'), self.progress)
        atomic_json(self.out / 'progress.json', self.progress)

    def phase(self, phase, **fields):
        self.progress.update(phase=phase, **fields)
        if phase != 'WAIT_MODULE' or time.time() - self.progress.get('updated', 0) > 0.5:
            self.save()

    def record_snapshot(self):
        if not self.journal.exists():
            return {}
        s = self.journal.stat()
        stamp = (s.st_ino, s.st_mtime_ns, s.st_size)
        if stamp != self.records_stamp:
            self.records = json.loads(self.journal.read_text())
            self.records_stamp = stamp
        return self.records

    def obj(self, m):
        return self.lib / (m.replace('.', '/') + '.olean')

    def module_lock(self, m):
        return self.out / 'module-locks' / (m + '.lock')

    def valid(self, m, records):
        r = records.get(m, {})
        if r.get('key') != self.keys[m] or not r.get('checked'):
            return False
        try:
            if self.digest(self.obj(m)) != r.get('object_sha256'):
                return False
            if any(self.digest(self.root / p) != h for p, h in r.get('companions', {}).items()):
                return False
            if r.get('check_log') and self.digest(self.root / r['check_log']) != r.get('check_log_sha256'):
                return False
            return self.digest(self.modules[m]) == self.sources[m]
        except FileNotFoundError:
            return False

    def update_record(self, m, record):
        # Reload under the short journal lock: concurrent writers must not lose entries.
        with locked(self.out / 'journal.lock'):
            records = json.loads(self.journal.read_text()) if self.journal.exists() else {}
            records[m] = record
            atomic_json(self.journal, records)
        self.records_stamp = None

    def build(self, m):
        self.phase('WAIT_MODULE', module=m)
        with locked(self.out / 'build.lock', fcntl.LOCK_SH, self.inherited):
            # Fast cache hits need no ancestry locks: no compiler reads the closure.
            with locked(self.module_lock(m), fcntl.LOCK_SH, self.inherited):
                if self.valid(m, self.record_snapshot()):
                    return False
            # Global lexical acquisition order prevents reader/writer lock cycles.
            with ExitStack() as stack:
                for d in sorted(self.ancestors[m] | {m}):
                    stack.enter_context(locked(self.module_lock(d),
                        fcntl.LOCK_EX if d == m else fcntl.LOCK_SH, self.inherited))
                records = self.record_snapshot()
                if self.valid(m, records):
                    return False
                for d in self.ancestors[m]:
                    if not self.valid(d, records):
                        raise BuildFailure(f'dependency changed or no longer checked: {d}; retry a fresh snapshot', 76)
                if self.digest(self.modules[m]) != self.sources[m]:
                    raise BuildFailure(f'source changed: {m}', 76)
                self.phase('WAIT_SLOT', module=m)
                with capacity(self.out / 'slots', self.limit, self.inherited) as slot:
                    self.compile_check(m, slot)
        return True

    def compile_check(self, m, slot):
        obj = self.obj(m)
        obj.parent.mkdir(parents=True, exist_ok=True)
        commands = [('compile', [self.lean, '--root=' + str(self.root), '-o', str(obj)] +
                     (['-DwarningAsError=true'] if m.startswith('LiuWang.') else []) + [str(self.modules[m])]),
                    ('check', [self.lean, '-DwarningAsError=true', str(self.driver)])]
        for mode, command in commands:
            if self.digest(self.driver) != self.driver_hash or self.digest(self.core) != self.core_hash:
                raise BuildFailure('checker implementation changed during request', 76)
            guard_key = hashlib.sha256((m + self.keys[m] + mode + self.driver_hash + self.gate_hash).encode()).hexdigest()
            guard_path = self.out / 'execution-guards' / (guard_key + '.json')
            if guard_path.exists() and json.loads(guard_path.read_text()).get('state') in {'RUNNING', 'RESOURCE_FAILED'}:
                raise BuildFailure(f'prior resource failure/missing terminal receipt: {m} {mode}', 75)
            guard = dict(module=m, mode=mode, key=self.keys[m], gate_sha256=self.gate_hash,
                         helper_sha256=self.driver_hash, request=self.request, pid=os.getpid(), state='RUNNING')
            atomic_json(guard_path, guard)
            log = self.out / (m + '.' + mode + '.' + self.request + '.log')
            env = dict(self.env)
            if mode == 'check': env['LIUWANG_EXACT_REPLAY_MODULE'] = m
            started = time.time()
            self.phase(mode.upper(), module=m, slot=slot, log=str(log.relative_to(self.root)))
            print('EXEC', self.request, m, mode, 'slot', slot, flush=True)
            with log.open('w') as stream:
                try:
                    result = subprocess.run(command, cwd=self.root, env=env, stdout=stream,
                        stderr=subprocess.STDOUT, timeout=600, pass_fds=tuple(self.inherited))
                    code = result.returncode
                except subprocess.TimeoutExpired:
                    code = 124
            atomic_json(self.out / 'timings' / (self.request + '.' + m + '.' + mode + '.json'),
                dict(request=self.request, module=m, mode=mode, slot=slot, started=started,
                     finished=time.time(), exit_code=code, pid=os.getpid()))
            guard.update(state='RESOURCE_FAILED' if code in {-9, -15, 124} else 'EXITED', exit_code=code)
            atomic_json(guard_path, guard)
            if code:
                raise BuildFailure(f'{mode} failed: {m}; {log}', code if code > 0 else 1)
            if mode == 'check':
                lines = log.read_text().splitlines()
                if [s for s in lines if s.startswith('OFFICIAL_CORE_EXACT_PASS ')] != ['OFFICIAL_CORE_EXACT_PASS ' + m]:
                    raise BuildFailure(f'missing/incorrect exact replay marker: {m}')
                if 'OFFICIAL_CORE_EXACT_BEGIN ' + m + ' ' + str(obj) not in lines:
                    raise BuildFailure(f'wrong replay object path: {m}')
        if self.digest(self.modules[m]) != self.sources[m]:
            raise BuildFailure(f'source changed during compilation: {m}', 76)
        parts = [obj, Path(str(obj) + '.server'), Path(str(obj) + '.private'), obj.with_suffix('.ir'), obj.with_suffix('.ir.sig')]
        companions = {str(p.relative_to(self.root)): self.digest(p) for p in parts if p.is_file()}
        check_log = self.out / (m + '.check.' + self.request + '.log')
        self.update_record(m, dict(key=self.keys[m], source_sha256=self.sources[m],
            object_sha256=self.digest(obj), checked=True,
            check_mode='official-core-exact-replayFromImports', helper_sha256=self.driver_hash,
            official_core_object_sha256=self.core_hash, companions=companions,
            check_log=str(check_log.relative_to(self.root)), check_log_sha256=self.digest(check_log),
            scheduler='module-lock-v2', request=self.request))

    def run(self):
        print('REQUEST', self.request, 'START', len(self.order), 'modules; bounded module locks; slots', self.limit, flush=True)
        for index, m in enumerate(self.order, 1):
            built = self.build(m)
            self.progress['built' if built else 'cached'] += 1
            self.progress['passed'] = index
            if built or index % 100 == 0:
                self.save()
                print('PASS' if built else 'CACHE', index, '/', len(self.order), m, flush=True)
        # Lock the full local closure for the final stable object/source snapshot.
        self.phase('FINAL_SNAPSHOT')
        with locked(self.out / 'build.lock', fcntl.LOCK_SH, self.inherited):
            with ExitStack() as stack:
                for m in sorted(self.order):
                    stack.enter_context(locked(self.module_lock(m), fcntl.LOCK_SH, self.inherited))
                records = self.record_snapshot()
                if self.digest(self.root / 'lean-toolchain') + self.digest(self.root / 'lake-manifest.json') != self.base:
                    raise BuildFailure('toolchain/manifest changed', 76)
                for m in self.order:
                    if not self.valid(m, records):
                        raise BuildFailure(f'final snapshot changed: {m}', 76)
        self.progress.update(status='PASSED', phase='DONE', elapsed_seconds=time.time() - self.progress['started'])
        self.save()
        print('DONE', json.dumps(self.progress, ensure_ascii=False), flush=True)


def main():
    scheduler = None
    try:
        scheduler = Scheduler(Path(__file__).resolve().parents[1], sys.argv[1:])
        scheduler.run()
        return 0
    except (BuildFailure, AssertionError, OSError, subprocess.SubprocessError) as error:
        code = error.code if isinstance(error, BuildFailure) else 1
        if scheduler:
            scheduler.progress.update(status='BLOCKED_PREVIOUS_INTERRUPTION' if code == 75 else 'FAILED',
                                      error=str(error), exit_code=code)
            scheduler.save()
        print('FAILED', str(error), flush=True)
        return code
