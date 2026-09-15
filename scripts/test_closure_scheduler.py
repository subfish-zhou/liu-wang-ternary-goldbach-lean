"""Real OS-process tests for locking, not mathematical theorem evidence."""
from pathlib import Path
from contextlib import ExitStack
import fcntl
import json
import multiprocessing as mp
import os
import subprocess
import sys
import time
import uuid

from closure_scheduler import locked, capacity, atomic_json, uncomment, Scheduler

ROOT = Path(__file__).resolve().parents[1]
D = ROOT / '.lake/local-closure/scheduler-upgrade' / ('tests-' + uuid.uuid4().hex)


def job(folder, index, same=False):
    folder = Path(folder)
    with locked(folder / ('one.lock' if same else f'module-{index}.lock')):
        with capacity(folder / 'slots', 4) as slot:
            start = time.time()
            time.sleep(0.35)
            atomic_json(folder / f'{index}.json', dict(start=start, end=time.time(), slot=slot))


def journal_writer(folder, index):
    s = Scheduler.__new__(Scheduler)
    s.out = Path(folder)
    s.journal = s.out / 'modules.json'
    s.update_record(f'module-{index}', {'value': index})


def reader(folder, ready):
    with locked(Path(folder) / 'dep.lock', fcntl.LOCK_SH):
        ready.set()
        time.sleep(0.4)


def inherited_parent(folder, ready):
    handles = set()
    # Simulate an interrupted caller with a compiler that still owns the lock.
    with locked(Path(folder) / 'inherit.lock', inherited=handles):
        p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(1.5)'], pass_fds=tuple(handles))
        atomic_json(Path(folder) / 'child.json', {'pid': p.pid})
        ready.set()
        time.sleep(20)


def maximum_overlap(rows):
    events = sorted([(r['start'], 1) for r in rows] + [(r['end'], -1) for r in rows])
    current = peak = 0
    for _, change in events:
        current += change; peak = max(peak, current)
    return peak


def main():
    D.mkdir(parents=True)
    summary = {}
    for name, same in [('parallel', False), ('same-module', True)]:
        folder = D / name
        folder.mkdir()
        ps = [mp.Process(target=job, args=(str(folder), i, same)) for i in range(8)]
        for p in ps: p.start()
        for p in ps:
            p.join(10); assert p.exitcode == 0
        rows = [json.loads((folder / f'{i}.json').read_text()) for i in range(8)]
        peak = maximum_overlap(rows)
        assert peak == (1 if same else 4), (name, peak)
        summary[name] = {'peak': peak, 'jobs': len(rows)}
    folder = D / 'journal'; folder.mkdir()
    ps = [mp.Process(target=journal_writer, args=(str(folder), i)) for i in range(16)]
    for p in ps: p.start()
    for p in ps:
        p.join(10); assert p.exitcode == 0
    records = json.loads((folder / 'modules.json').read_text())
    assert len(records) == 16
    summary['journal_no_lost_updates'] = len(records)
    ready = mp.Event()
    p = mp.Process(target=reader, args=(str(D), ready)); p.start(); assert ready.wait(5)
    with (D / 'dep.lock').open('a') as f:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            summary['dependency_reader_blocks_writer'] = True
        else:
            raise AssertionError('writer raced reader')
    p.join(5); assert p.exitcode == 0
    ready = mp.Event()
    p = mp.Process(target=inherited_parent, args=(str(D), ready)); p.start(); assert ready.wait(5)
    p.terminate(); p.join(5)
    with (D / 'inherit.lock').open('a') as f:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            summary['orphan_child_keeps_lock'] = True
        else:
            raise AssertionError('lock released while compiler survived')
        fcntl.flock(f, fcntl.LOCK_EX)
    summary['orphan_lock_eventually_released'] = True
    text = '/- import Fake\n/- import Nested -/ -/\npublic import Actual.One Actual.Two -- comment\n'
    parsed = uncomment(text)
    assert 'Fake' not in parsed and 'Nested' not in parsed and 'public import Actual.One Actual.Two' in parsed
    summary['nested_comments'] = True
    atomic_json(D / 'summary.json', summary)
    print(json.dumps({'status': 'PASSED', 'results': summary, 'evidence': str(D)}, indent=2))


if __name__ == '__main__':
    main()
