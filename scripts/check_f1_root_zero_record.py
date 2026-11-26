"""Verify portable root evidence against repository sources, without /tmp reads."""
import argparse,base64,hashlib,json,re,zlib
from pathlib import Path

def need(x,m):
 if not x:raise ValueError(m)
def digest(data):return hashlib.sha256(data).hexdigest()
def unique(pairs):
 r={}
 for k,v in pairs:need(k not in r,'duplicate JSON key');r[k]=v
 return r
def loads(x):return json.loads(x,object_pairs_hook=unique)
def parse_audits(text):
 text=re.sub(r'\[([^\]]*)\]',lambda m:'['+' '.join(m.group(1).split())+']',text);r={}
 for line in text.splitlines():
  if not line.strip():continue
  m=re.fullmatch(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",line.strip());need(m,'unexpected audit line')
  n,aa=m.groups();need(n not in r,'duplicate audit');r[n]=[] if not aa else [x.strip() for x in aa.split(',')]
  need(len(r[n])==len(set(r[n])) and set(r[n])<={'propext','Classical.choice','Quot.sound'},'foreign axiom')
 return r

def lean_imports(source):
    """Read the pinned files' import declarations, ignoring comments and strings."""
    code = []
    i, depth, string, line = 0, 0, False, False
    while i < len(source):
        c, pair = source[i], source[i:i + 2]
        if line:
            code.append('\n' if c == '\n' else ' ')
            if c == '\n': line = False
            i += 1
        elif string:
            if c == '\\' and i + 1 < len(source):
                code.extend([' ', ' ']); i += 2
            else:
                if c == '"': string = False
                code.append('\n' if c == '\n' else ' '); i += 1
        elif depth:
            if pair in ('/-', '-/'):
                depth += 1 if pair == '/-' else -1
                code.extend([' ', ' ']); i += 2
            else:
                code.append('\n' if c == '\n' else ' '); i += 1
        elif pair in ('/-', '--'):
            depth, line = (1, False) if pair == '/-' else (0, True)
            code.extend([' ', ' ']); i += 2
        elif c == '"':
            string = True; code.append(' '); i += 1
        else:
            code.append(c); i += 1
    need(depth == 0 and not string, 'Unterminated Lean comment/string')
    imports = []
    for line in ''.join(code).splitlines():
        match = re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*', line)
        if match:
            names = match.group(1).split()
            need(all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', name) for name in names),
                    'Unsupported Lean import syntax')
            imports.extend(names)
    need(len(set(imports)) == len(imports), 'Duplicate direct Lean import')
    return imports


def check(r,repo):
 p=r['portable_evidence'];raw=zlib.decompress(base64.b64decode(p['payload'],validate=True));need(digest(raw)==p['uncompressed_sha256'],'archive digest')
 e=loads(raw);need(len(e['paths'])==p['path_count'] and len(e['blobs'])==p['unique_text_blobs'],'archive counts')
 for h,t in e['blobs'].items():need(digest(t.encode())==h,'blob digest')
 for path,h in e['paths'].items():need(h in e['blobs'],'missing blob')
 def text(pin):
  need(e['paths'].get(pin['path'])==pin['sha256'],'missing or wrong archived pin '+pin['path']);return e['blobs'][pin['sha256']]
 def obj(pin):return loads(text(pin))
 closure=obj(r['source_closure']);need(len(closure['project_modules'])==284,'closure count')
 sources={x['module']:x for x in closure['project_modules']};need(len(sources)==284,'duplicate closure module')
 for row in sources.values():
  raw_source=(repo/row['repository_relative']).read_bytes()
  need(digest(raw_source)==row['source']['sha256'],'source drift '+row['module'])
  need(lean_imports(raw_source.decode())==row['imports'],'source imports differ from recorded dependencies: '+row['module'])
 for f,h in r['source_sha256'].items():need(digest((repo/f).read_bytes())==h,'integrated source drift')
 acceptance=r['acceptance']
 for k in ['actual_repository_build','actual_repository156_audit','prior_original_weighted121','generic_original815_assembly']:need(acceptance[k] is True,'lost accepted scope')
 for k in ['full815_numerical_constant','all37_slots122_in_this_record','geometric_GW_invariant','full722_actual_repository_rebuild','full_project_build']:need(acceptance[k] is False,'scope overstatement')
 v=r['actual_repository_validation'];ledger=obj(v['serial_ledger']);manifest=obj(r['integration_manifest']);plan=obj(manifest['serial_missing_artifact_plan'])
 config_names={'lakefile.toml','lake-manifest.json','lean-toolchain'}
 config_rows=[x for x in ledger['config'] if Path(x['path']).name in config_names]
 need(len(config_rows)==3 and {Path(x['path']).name for x in config_rows}==config_names,'incomplete or duplicate project configuration pins')
 config={Path(x['path']).name:x for x in config_rows}
 for name,pin in config.items():need(digest((repo/name).read_bytes())==pin['sha256'],'configuration drift '+name)
 for key,name in [('toolchain','lean-toolchain'),('lake_manifest','lake-manifest.json')]:
  need(Path(closure[key]['path']).name==name and closure[key]['sha256']==config[name]['sha256'],'closure configuration differs '+name)
 need(ledger['status']=='all54_repository_targets_passed_audit_pending','ledger not passed');steps=ledger['steps'];need(len(steps)==54,'build count')
 need([s['module'] for s in steps]==[x['module'] for x in plan['absent_olean_modules']],'build coverage/order')
 observed=0;peak=0;warnings=[]
 for i,s in enumerate(steps):
  need(s['index']==i and s['status']=='passed','unpassed step');mod=s['module'];need(s['source']['sha256']==sources[mod]['source']['sha256'],'step source')
  for key in ['prerequisites','build']:
   md=obj(s[key]);log=text(md['log']);need(md['status']=='passed' and md['exit_code']==0,'failed process')
   need(md['max_sampled_concurrent_lean_children']<=1 and md['peak_sampled_lean_rss_bytes']<=2147483648,'resource violation')
   need(md['elapsed_seconds']<=md['timeout_seconds']+10,'bound mismatch')
   tail=md['command'][1:]
   want=['--no-ansi','--no-cache','--no-build','build',*sources[mod]['imports']] if key=='prerequisites' else ['--no-ansi','--no-cache','build',mod]
   need(tail==want,'wrong actual command')
   ws=s['prerequisite_warnings'] if key=='prerequisites' else s['reviewed_warnings']
   for w in ws:
    need(w['kind'] in ['preexisting_maxHeartbeats_comment','preexisting_unscoped_maxHeartbeats','preexisting_long_line'],'unreviewed warning kind');need(w['message'] in log,'unbound warning')
    need(w['message'].startswith(f"warning: {w['path']}:{w['line']}:{w['column']}: "),'warning location')
    actual=(repo/w['path']).read_text().splitlines()[w['line']-1]
    if w['kind']=='preexisting_maxHeartbeats_comment':need('set_option maxHeartbeats 0' in actual,'wrong heartbeat line')
    else:need(actual==w['source_line'],'frozen warning source line')
    log=log.replace(w['message'],'')
   need(not re.search(r'\b(?:warning|error):|sorryAx|memory_exception',log),'unreviewed diagnostics')
   need('Build completed successfully' in log or 'All targets up-to-date' in log,'no success marker')
   if key=='build':
    rebuilt=bool(re.search(r'(?m)^.*\bBuilt '+re.escape(mod)+r' \(',log));positive=md['max_sampled_concurrent_lean_children']>0
    need(not rebuilt or positive,'rebuilt without Lean sample');need(s['resource_observation']=={'target_rebuilt':rebuilt,'positive_lean_observation':positive},'observation mismatch')
    observed+=rebuilt;peak=max(peak,md['peak_sampled_lean_rss_bytes']);warnings.extend(ws)
 need(observed==v['fresh_build_count']==51 and 54-observed==v['up_to_date_count']==3,'fresh count')
 need(peak==v['peak_sampled_lean_rss_bytes'] and len(warnings)==v['warning_occurrences_in_build_logs'],'resource/warning summary')
 audit=obj(v['audit_acceptance']);need(audit['serial_ledger']==v['serial_ledger'],'audit ledger binding')
 md=obj(audit['metadata']);need(md['status']=='passed' and md['exit_code']==0 and md['max_sampled_concurrent_lean_children']==1 and md['peak_sampled_lean_rss_bytes']<=2147483648,'audit process')
 actual=parse_audits(text(audit['log']));prior=obj(r['prior_validation']['evidence'])['audits'];need(len(actual)==156 and actual==audit['axioms'] and actual==prior,'audit coverage/dependencies')
 names=re.findall(r'(?m)^#print axioms (\S+)$',text(audit['audit_source']));need(len(names)==156 and set(names)==set(actual),'audit source coverage')
 review=obj(v['exact_outer_style_review']);need(review['source']['sha256']==r['source_sha256']['AxiomaticGW/Surfaces/Fixtures/BlowupF1H121OuterReplay.lean'],'style source pin')
 need(obj(v['prior_stopped_ledger'])['status']=='stopped_at_failure','failed history hidden')
 return {'status':'passed','project_sources':284,'repository_builds':54,'rebuilt_observed':51,'exact_audits':156,'standard_axioms_only':True,'temporary_files_read':False,'source_import_lists_checked':284,'configuration_files_checked':3}

def main():
 p=argparse.ArgumentParser();p.add_argument('record',type=Path);p.add_argument('--repo',type=Path,default=Path.cwd());a=p.parse_args();print(json.dumps(check(loads(a.record.read_text()),a.repo)))
if __name__=='__main__':main()
