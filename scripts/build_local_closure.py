#!/usr/bin/env python3
"""在当前主工作树串行编译指定模块的本地依赖闭包；不构建共享 packages。"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/local-closure'
LIB = ROOT / '.lake/build/lib/lean'
OUT.mkdir(parents=True, exist_ok=True)
LIB.mkdir(parents=True, exist_ok=True)
modules = {
    '.'.join(p.relative_to(ROOT).with_suffix('').parts): p
    for p in ROOT.rglob('*.lean') if '.lake' not in p.relative_to(ROOT).parts
}
targets = sys.argv[1:]
assert targets and all(m in modules for m in targets), targets
order, visiting, visited, deps = [], set(), set(), {}
def visit(m):
    if m not in modules or m in visited:
        return
    assert m not in visiting, ('cyclic imports', m)
    visiting.add(m)
    imports = re.findall(r'^(?:public\s+)?import\s+([\w.]+)', modules[m].read_text(), re.M)
    deps[m] = imports
    for d in imports:
        visit(d)
    visiting.remove(m)
    visited.add(m)
    order.append(m)
for m in targets:
    visit(m)

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

sources = {m: digest(modules[m]) for m in order}
base = digest(ROOT/'lean-toolchain') + digest(ROOT/'lake-manifest.json')
keys = {}
for m in order:
    keys[m] = hashlib.sha256((base + sources[m] + ''.join(keys.get(d, d) for d in deps[m])).encode()).hexdigest()
env = dict(os.environ)
env.pop('LEAN_PATH', None)
env.pop('LEAN_SYSROOT', None)
lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, env=env, text=True).strip()
lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=ROOT, env=env, text=True).strip()
checker = subprocess.check_output(['lake', 'env', 'which', 'leanchecker'], cwd=ROOT, env=env, text=True).strip()
env['LEAN_PATH'] = lean_path
journal = OUT/'modules.json'
records = json.loads(journal.read_text()) if journal.exists() else {}
progress = {'targets': targets, 'planned': len(order), 'passed': 0, 'status': 'RUNNING', 'started': time.time()}
def save():
    (OUT/'progress.json').write_text(json.dumps(progress, ensure_ascii=False, indent=2))
    journal.write_text(json.dumps(records, ensure_ascii=False, indent=2))
save()
print('START', len(order), 'local modules; single tree, serial compiler/checker', flush=True)
for index, m in enumerate(order, 1):
    assert digest(modules[m]) == sources[m], ('source changed', m)
    obj = LIB / (m.replace('.', '/') + '.olean')
    previous = records.get(m, {})
    if previous.get('key') == keys[m] and previous.get('checked') and obj.is_file() and digest(obj) == previous.get('object_sha256'):
        progress['passed'] = index
        save()
        continue
    obj.parent.mkdir(parents=True, exist_ok=True)
    commands = [
        ('compile', [lean, '--root='+str(ROOT), '-o', str(obj)] +
         (['-DwarningAsError=true'] if m.startswith('LiuWang.') else []) + [str(modules[m])]),
        ('check', [checker, m])
    ]
    for mode, command in commands:
        log = OUT/(m+'.'+mode+'.log')
        with log.open('w') as stream:
            try:
                result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=600)
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = 124
        if code:
            progress.update(status='FAILED', module=m, mode=mode, exit_code=code, log=str(log.relative_to(ROOT)))
            save()
            print('FAILED', json.dumps(progress, ensure_ascii=False), flush=True)
            sys.exit(code)
    assert digest(modules[m]) == sources[m], ('source changed during compile', m)
    records[m] = {'key': keys[m], 'source_sha256': sources[m], 'object_sha256': digest(obj), 'checked': True}
    progress['passed'] = index
    save()
    print('PASS', index, '/', len(order), m, flush=True)
for m in order:
    assert digest(modules[m]) == sources[m], ('source changed after compilation', m)
progress.update(status='PASSED', elapsed_seconds=time.time()-progress['started'])
save()
print('DONE', json.dumps(progress, ensure_ascii=False), flush=True)
