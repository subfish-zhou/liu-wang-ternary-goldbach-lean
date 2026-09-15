#!/usr/bin/env python3
"""启动一个单主树、独占新模块目录的 Copilot CLI；不做自动 Git 集成。"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
config_path=Path(sys.argv[1]).resolve()
config=json.loads(config_path.read_text())
assert Path(config['cwd'])==ROOT
D=Path(config['directory'])
assert D.is_relative_to(ROOT/'.lake/campaign-20260915')
branch=subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()
assert branch=='main'
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
brief=Path(config['brief']).read_text()
# Route only this fresh CLI session's journal into its task-owned directory.
session=D/'session'
session.mkdir(exist_ok=False)
link=Path.home()/'.copilot/session-state'/config['session_id']
assert not os.path.lexists(link)
link.symlink_to(session,target_is_directory=True)
available='view,apply_patch,bash,read_bash,list_bash,rg,glob,web_fetch'
argv=['copilot','--model',config['model'],'--reasoning-effort',config['reasoning_effort'],
      '--session-id',config['session_id'],'--name','ternary-main-'+config['task'],
      '--available-tools='+available,'--allow-all-tools','--allow-all-urls',
      '--disable-builtin-mcps','--no-auto-update','--no-ask-user','--no-color',
      '--no-remote','--no-remote-export',
      '--add-dir','/home/azureuser/goldbach-v1-release/.lake/packages',
      '--log-dir',str(D/'logs'),'--usage-output-file',str(D/'usage.json'),
      '--mode','autopilot','--max-autopilot-continues','20']
for tool in ['shell(git push)','shell(git commit)','shell(git add)','shell(git worktree)',
             'shell(git checkout)','shell(git switch)','shell(git reset)','shell(git clean)',
             'shell(git branch)','shell(rm)','shell(scp)','shell(gh)']:
    argv += ['--deny-tool',tool]
argv += ['-p',brief]
with (D/'output.log').open('w') as out:
    p=subprocess.Popen(argv,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
    record={'task':config['task'],'pid':p.pid,'session_id':config['session_id'],
            'cwd':str(ROOT),'head_at_start':head,'model':config['model'],
            'reasoning_effort':config['reasoning_effort'],
            'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'brief_sha256':hashlib.sha256(brief.encode()).hexdigest(),
            'gap_ids':config['gap_ids'],'source_prefix':config['source_prefix']}
    (D/'started.json').write_text(json.dumps(record,ensure_ascii=False,indent=2))
    print('CLI_STARTED',json.dumps(record,ensure_ascii=False),flush=True)
    code=p.wait()
    result={'task':config['task'],'cli_exit_code':code,
            'finished':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'artifacts':{name:(D/name).is_file() for name in ['REPORT.md','result.json','done.json']},
            'accepted_by_parent':False}
    (D/'exit.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
    print('CLI_EXIT',json.dumps(result,ensure_ascii=False),flush=True)
    sys.exit(code if code else (0 if all(result['artifacts'].values()) else 2))
