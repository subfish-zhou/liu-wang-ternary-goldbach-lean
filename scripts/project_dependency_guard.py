"""Reject a worker build that crosses into an unaccepted source owner."""
from pathlib import Path
import hashlib
import json
import os
import re


def check_owner_imports(root, owner, targets):
    from closure_scheduler import uncomment
    root = Path(root).resolve()
    prefix = 'LiuWang.Proof.Campaign20260915.'
    accepted = json.loads((root/'verification/checkpoint-latest.json').read_text())['source_manifest']
    seen = set()
    def visit(module):
        if module in seen:
            return
        seen.add(module)
        rel = module.replace('.', '/') + '.lean'
        path = root / rel
        if not path.is_file():
            return
        data = path.read_bytes()
        if module.startswith(prefix):
            other = module[len(prefix):].split('.')[0]
            if other != owner:
                if accepted.get(rel) != hashlib.sha256(data).hexdigest():
                    raise RuntimeError('CROSS_OWNER_HANDOFF_REQUIRED: ' + owner + ' -> ' + module)
        for line in uncomment(data.decode()).splitlines():
            m = re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*$', line)
            if m:
                for child in m[1].split():
                    visit(child)
    for target in targets:
        if not target.startswith(prefix + owner + '.'):
            raise RuntimeError('WORKER_TARGET_OUTSIDE_OWNER: ' + target)
        visit(target)
    return len(seen)


def enforce_worker_imports(root, targets):
    root = Path(root).resolve()
    campaign = root/'.lake/campaign-20260915'
    plan_path = campaign/'expansion-review/dispatch-plan.json'
    if not plan_path.exists():
        return
    pid_owners = {}
    for item in json.loads(plan_path.read_text()):
        folder = campaign/item['task']
        path = folder/('current.json' if (folder/'current.json').exists() else 'started.json')
        if path.exists():
            record = json.loads(path.read_text())
            pid_owners[int(record['pid'])] = (item['owner'], record['session_id'])
    pid = os.getpid()
    while pid > 1:
        try:
            proc = Path('/proc')/str(pid)
            if pid in pid_owners:
                owner, sid = pid_owners[pid]
                args = (proc/'cmdline').read_bytes().decode(errors='replace').split('\0')
                if sid in args or '--resume='+sid in args:
                    count = check_owner_imports(root, owner, targets)
                    print('OWNER_IMPORT_ADMISSION_PASS', owner, count, flush=True)
                    return
            stat = (proc/'stat').read_text().rsplit(')',1)[1].split()
            pid = int(stat[1])
        except (FileNotFoundError, ProcessLookupError):
            return
    # A parent-owned validation command has no worker ancestor and may accept a new handoff.
