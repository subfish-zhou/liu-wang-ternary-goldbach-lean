#!/usr/bin/env python3
"""当前主树逐模块串行编译/内核检查；多请求共享锁与缓存，不构建 packages。"""
from pathlib import Path
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/local-closure'
LIB = ROOT / '.lake/build/lib/lean'
OUT.mkdir(parents=True, exist_ok=True)
LIB.mkdir(parents=True, exist_ok=True)
REQUESTS = OUT/'requests'
REQUESTS.mkdir(exist_ok=True)
request = uuid.uuid4().hex
modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p
           for p in ROOT.rglob('*.lean') if '.lake' not in p.relative_to(ROOT).parts}
targets = sys.argv[1:]
assert targets and all(m in modules for m in targets), targets
order, visiting, visited, deps = [], set(), set(), {}
def visit(m):
    if m not in modules or m in visited:
        return
    assert m not in visiting, ('cyclic imports', m)
    visiting.add(m)
    deps[m] = re.findall(r'^(?:public\s+)?import\s+([\w.]+)', modules[m].read_text(), re.M)
    for d in deps[m]:
        visit(d)
    visiting.remove(m)
    visited.add(m)
    order.append(m)
for m in targets:
    visit(m)
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic_json(path, data):
    tmp = path.with_name(path.name+'.'+request+'.tmp')
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2))
    os.replace(tmp, path)
sources = {m: digest(modules[m]) for m in order}
base = digest(ROOT/'lean-toolchain') + digest(ROOT/'lake-manifest.json')
keys = {}
for m in order:
    keys[m] = hashlib.sha256((base + sources[m] + ''.join(keys.get(d, d) for d in deps[m])).encode()).hexdigest()
env = dict(os.environ)
env.pop('LEAN_PATH', None)
env.pop('LEAN_SYSROOT', None)
# Serialize Lake's environment initialization as well as project compilers.
lock = (OUT/'build.lock').open('a')
fcntl.flock(lock, fcntl.LOCK_EX)
try:
    lean_path = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,env=env,text=True).strip()
    lean = subprocess.check_output(['lake','env','which','lean'],cwd=ROOT,env=env,text=True).strip()
    checker = subprocess.check_output(['lake','env','which','leanchecker'],cwd=ROOT,env=env,text=True).strip()
finally:
    fcntl.flock(lock, fcntl.LOCK_UN)
env['LEAN_PATH'] = lean_path
exact_driver = ROOT/'scripts/ExactReplay.lean'
assert exact_driver.is_file()
exact_driver_hash = digest(exact_driver)
gate_hash = digest(Path(__file__))
guards = OUT/'execution-guards'
guards.mkdir(exist_ok=True)
core_object = Path(lean).resolve().parent.parent/'lib/lean/LeanChecker.olean'
assert core_object.is_file()
core_object_hash = digest(core_object)
journal = OUT/'modules.json'
progress = {'request': request, 'targets': targets, 'planned': len(order),
            'passed': 0, 'status': 'RUNNING', 'started': time.time()}
def save():
    atomic_json(REQUESTS/(request+'.json'), progress)
    atomic_json(OUT/'progress.json', progress)
save()
print('REQUEST',request,'START',len(order),'modules; one global compile/check lock',flush=True)
for index,m in enumerate(order,1):
    fcntl.flock(lock, fcntl.LOCK_EX)
    try:
        assert digest(modules[m]) == sources[m], ('source changed',m)
        records = json.loads(journal.read_text()) if journal.exists() else {}
        obj = LIB/(m.replace('.','/')+'.olean')
        previous = records.get(m,{})
        companion_match = all((ROOT/p).is_file() and digest(ROOT/p) == h
                              for p,h in previous.get('companions',{}).items())
        if previous.get('key') == keys[m] and previous.get('checked') and obj.is_file() and digest(obj) == previous.get('object_sha256') and companion_match:
            progress['passed'] = index
            save()
            continue
        obj.parent.mkdir(parents=True,exist_ok=True)
        commands = [('compile',[lean,'--root='+str(ROOT),'-o',str(obj)] +
                     (['-DwarningAsError=true'] if m.startswith('LiuWang.') else []) + [str(modules[m])]),
                    ('check',[lean,'-DwarningAsError=true',str(exact_driver)])]
        for mode,command in commands:
            log = OUT/(m+'.'+mode+'.'+request+'.log')
            command_env = dict(env)
            if mode == 'check':
                assert digest(exact_driver) == exact_driver_hash
                assert digest(core_object) == core_object_hash
                command_env['LIUWANG_EXACT_REPLAY_MODULE'] = m
            guard_key = hashlib.sha256((m+keys[m]+mode+exact_driver_hash+gate_hash).encode()).hexdigest()
            guard_path = guards/(guard_key+'.json')
            if guard_path.exists() and json.loads(guard_path.read_text()).get('state') in {'RUNNING','RESOURCE_FAILED'}:
                progress.update(status='BLOCKED_PREVIOUS_INTERRUPTION',module=m,mode=mode,
                                guard=str(guard_path.relative_to(ROOT)))
                save()
                print('BLOCKED: prior resource failure or missing terminal receipt for identical execution',m,mode,flush=True)
                sys.exit(75)
            guard = {'module':m,'mode':mode,'key':keys[m],'gate_sha256':gate_hash,
                     'helper_sha256':exact_driver_hash,'request':request,'pid':os.getpid(),'state':'RUNNING'}
            atomic_json(guard_path,guard)
            with log.open('w') as stream:
                try:
                    result = subprocess.run(command,cwd=ROOT,env=command_env,stdout=stream,stderr=subprocess.STDOUT,timeout=600)
                    code = result.returncode
                except subprocess.TimeoutExpired:
                    code = 124
            guard.update(state='RESOURCE_FAILED' if code in {-9,-15,124} else 'EXITED',exit_code=code)
            atomic_json(guard_path,guard)
            if mode == 'check' and code == 0:
                lines = log.read_text().splitlines()
                assert [s for s in lines if s.startswith('OFFICIAL_CORE_EXACT_PASS ')] == ['OFFICIAL_CORE_EXACT_PASS '+m]
                assert 'OFFICIAL_CORE_EXACT_BEGIN '+m+' '+str(obj) in lines
            if code:
                progress.update(status='FAILED',module=m,mode=mode,exit_code=code,log=str(log.relative_to(ROOT)))
                save()
                print('FAILED',json.dumps(progress,ensure_ascii=False),flush=True)
                sys.exit(code)
        assert digest(modules[m]) == sources[m], ('source changed during compile',m)
        companions = {str(p.relative_to(ROOT)):digest(p) for p in
                      [obj,Path(str(obj)+'.server'),Path(str(obj)+'.private'),obj.with_suffix('.ir'),obj.with_suffix('.ir.sig')]
                      if p.is_file()}
        check_log_path = OUT/(m+'.check.'+request+'.log')
        records[m] = {'key':keys[m],'source_sha256':sources[m],'object_sha256':digest(obj),'checked':True,
                      'check_mode':'official-core-exact-replayFromImports','helper_sha256':exact_driver_hash,
                      'official_core_object_sha256':core_object_hash,'companions':companions,
                      'check_log':str(check_log_path.relative_to(ROOT)),'check_log_sha256':digest(check_log_path)}
        atomic_json(journal,records)
        progress['passed'] = index
        save()
        print('PASS',index,'/',len(order),m,flush=True)
    finally:
        fcntl.flock(lock,fcntl.LOCK_UN)
for m in order:
    assert digest(modules[m]) == sources[m], ('source changed after compilation',m)
progress.update(status='PASSED',elapsed_seconds=time.time()-progress['started'])
save()
print('DONE',json.dumps(progress,ensure_ascii=False),flush=True)
