#!/usr/bin/env python3
"""在用户授权后恢复原 CLI 会话；保留初始日志和历史交付。"""
from pathlib import Path
import datetime
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
cfg = json.loads(Path(sys.argv[1]).read_text())
D = Path(cfg['directory'])
assert Path(cfg['cwd']) == ROOT and D.is_relative_to(ROOT/'.lake/campaign-20260915')
sid = cfg['session_id']
assert (Path.home()/'.copilot/session-state'/sid).resolve() == D/'session'
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip() == 'main'
for p in Path('/proc').iterdir():
    if not p.name.isdigit():
        continue
    try:
        args = (p/'cmdline').read_bytes().decode(errors='replace').split('\0')
    except OSError:
        continue
    assert sid not in args and '--resume='+sid not in args, ('existing session process',p.name)
attempt = D/('resume-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%d-%H%M%S'))
attempt.mkdir(exist_ok=False)
for name in ['REPORT.md','result.json','done.json']:
    p = D/name
    if p.exists():
        (attempt/('before-'+name)).write_bytes(p.read_bytes())
focus = {
    'totient': '先验收现有NuArithmetic、M6、PrimePowers、Cutoff、Audit。不要把有限段/素数幂子类算作M06全域闭合。W03实际编译与消费者接线通过后单独报清；继续原Rosser–Schoenfeld全整数输入。',
    'high-sums': '继续M08、M09、S04：验收已有HeightCompensation等本任务模块，保留真实phi归一化、transferRemainder、累计零点尾及所有有号补偿。不用改印式/删余项/改变参数域冒充原高零和完成。'
}.get(cfg['task'], '按原BRIEF继续本任务已分配的缺口，先核已有模块和消费者，禁止把条件接口或局部子类算作全域闭合。')
prompt = f'''父级按用户继续并行攻关及恢复中断工作的授权恢复本任务。先前批次已由systemd/kernel日志确认为任务cgroup内存耗尽，不是用户主动停止，也不是数学失败。续用现有草稿及全部已核缓存，不从头重复研究。
父级已修复统一gate：原leanchecker CLI把模块名作前缀并并发调度整族；现在精确调用当前工具链未修改的官方replayFromImports，只检查本次指定模块，保留全部运行时parts。未提高内存限额，未跳过内核检查。新回执须标official-core-exact，而非原CLI或--fresh；旧成功缓存继续复用。
先读 {D}/BRIEF.md、REPORT.md、result.json 以及自己已有模块。所有原写域、数学目标与单main约定保持。
你的旧构建请求标记RUNNING可能只是中断留下的状态，先检查是否确有对应build_local_closure进程；活着则收集原请求，不再启动副本。确无对应进程时，允许通过唯一编译入口重新请求自己的目标，复用现成缓存，不删除缓存或重做成功前缀。
全局 gate 一次只编译/检查一个模块。不要循环空等：等待时推进本任务原文/Lean推导，或者处理其他不冲突的本任务模块。
{focus} 修复只限你自己的目录。
不得修改旧源码、其他工作者、公共脚本或AGENTS.md，不新增分支、worktree、CLI、子代理。最终更新本任务REPORT.md、result.json、done.json，以新的真实检查结果为准；旧报告不自动算本次完成。
'''
(attempt/'BRIEF.md').write_text(prompt)
argv = ['copilot','--resume='+sid,'--model',cfg['model'],'--reasoning-effort',cfg['reasoning_effort'],
        '--available-tools=view,apply_patch,bash,read_bash,list_bash,rg,glob,web_fetch',
        '--allow-all-tools','--allow-all-urls','--disable-builtin-mcps','--no-auto-update',
        '--no-ask-user','--no-color','--no-remote','--no-remote-export',
        '--add-dir','/home/azureuser/goldbach-v1-release/.lake/packages',
        '--log-dir',str(attempt/'logs'),'--usage-output-file',str(attempt/'usage.json'),
        '--mode','autopilot','--max-autopilot-continues','20']
for tool in ['shell(git push)','shell(git commit)','shell(git add)','shell(git worktree)',
             'shell(git checkout)','shell(git switch)','shell(git reset)','shell(git clean)',
             'shell(git branch)','shell(rm)','shell(scp)','shell(gh)']:
    argv += ['--deny-tool',tool]
argv += ['-p',prompt]
started = time.time()
with (attempt/'output.log').open('w') as stream:
    p = subprocess.Popen(argv,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
    record = {'task':cfg['task'],'pid':p.pid,'session_id':sid,'attempt':str(attempt),
              'cwd':str(ROOT),'started_epoch':started,'mode':'resume','accepted':False}
    (attempt/'started.json').write_text(json.dumps(record,ensure_ascii=False,indent=2))
    (D/'current.json').write_text(json.dumps(record,ensure_ascii=False,indent=2))
    print('CLI_RESUMED',json.dumps(record,ensure_ascii=False),flush=True)
    code = p.wait()
    artifacts = {name:(D/name).exists() and (D/name).stat().st_mtime >= started
                 for name in ['REPORT.md','result.json','done.json']}
    result = {'task':cfg['task'],'cli_exit_code':code,'fresh_artifacts':artifacts,'accepted':False}
    (attempt/'exit.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
    print('CLI_EXIT',json.dumps(result,ensure_ascii=False),flush=True)
    sys.exit(code if code else (0 if all(artifacts.values()) else 2))
