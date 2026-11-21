"""Stdlib-only wall/CPU/RSS telemetry for an already admitted bounded script.
No scientific functions, assertions, source files or resource caps are changed.
"""
import argparse,json,resource,runpy,sys,time
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--profile',type=Path,required=True)
parser.add_argument('script',type=Path)
parser.add_argument('args',nargs=argparse.REMAINDER)
options=parser.parse_args()
started=time.perf_counter();events=[]
def usage():
    u=resource.getrusage(resource.RUSAGE_SELF)
    return {'wall_seconds':time.perf_counter()-started,'user_cpu_seconds':u.ru_utime,
            'system_cpu_seconds':u.ru_stime,'max_rss_kib_linux':u.ru_maxrss}
class ObserveStdout:
    def __init__(self,stream):self.stream=stream;self.pending=''
    def write(self,text):
        result=self.stream.write(text);self.pending+=text
        while '\n' in self.pending:
            line,self.pending=self.pending.split('\n',1)
            try:record=json.loads(line)
            except (ValueError,TypeError):continue
            if isinstance(record,dict) and record.get('event') in ('loop-controls-complete','loop-pilot-built','loop-pilot-result','loop-terminal-failure'):
                events.append({'event':record['event'],**usage()})
        return result
    def flush(self):return self.stream.flush()
    def __getattr__(self,name):return getattr(self.stream,name)
previous_stdout=sys.stdout;previous_argv=sys.argv[:];previous_path=sys.path[:]
status=0;error=None
try:
    script=options.script.resolve();sys.argv=[str(script),*options.args]
    sys.path.insert(0,str(script.parent));sys.stdout=ObserveStdout(previous_stdout)
    runpy.run_path(str(script),run_name='__main__')
except SystemExit as exc:
    status=exc.code if isinstance(exc.code,int) else 1
    if status:error=type(exc).__name__
    raise
except BaseException as exc:
    status=1;error=type(exc).__name__;raise
finally:
    sys.stdout=previous_stdout;sys.argv=previous_argv;sys.path[:]=previous_path
    child=resource.getrusage(resource.RUSAGE_CHILDREN)
    result={'scope':'single already-admitted bounded experiment; no full harder-channel or lattice scaling inference',
       'script':options.script.name,'arguments':options.args,'exit_code':status,'error':error,
       'python_optimize':sys.flags.optimize,**usage(),'events':events,
       'child_max_rss_kib_linux':child.ru_maxrss,
       'rss_definition':'Linux ru_maxrss cumulative process high-water mark, not instantaneous or sum of concurrent RSS'}
    options.profile.write_text(json.dumps(result,indent=2)+'\n')
