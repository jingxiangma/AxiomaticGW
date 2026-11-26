"""Verify the portable285-audit follow-up using the established bounded evidence reader."""
import argparse,hashlib,importlib.util,json,re
from pathlib import Path
COMMON_SHA='fe8c4f9d8d67a8557d69e0e51aa3cb0da9515cc9aba762964d9d11e0d4203208'
PLAN_SHA='43e4ee7b2b7a90505df321d79618fe5edbcb5f4808a7b2888d5f3218cc82e159'
LEDGER_SHA='fba6e55e5606b848ab16bb722300eb4c8e4adbe2709b82e81fd3d495348916bb'
ISOLATED_SHA='5c87c459a98f993eeab1343469e2a14c9d1114777b9456ec19935856d20f240c'
def check_record(record,repository,common_path=None):
 repository=Path(repository);p=Path(common_path)if common_path else repository/'scripts/check_f1_actual_numeric_record.py'
 raw=p.read_bytes()
 if hashlib.sha256(raw).hexdigest()!=COMMON_SHA:raise ValueError('Established reader changed')
 sp=importlib.util.spec_from_file_location('verified_f1_numeric_reader',p);c=importlib.util.module_from_spec(sp);sp.loader.exec_module(c)
 need=c.need;helper=c.load_helper(repository);b=c.Blobs(record['blobs'])
 need(type(record['schema_version']) is int and record['schema_version']==1,'Schema version')
 need(record['mathematical_scope']=={'indices':list(range(126,131)),'weighted_values':[[0,1]]*5,'slot_claims':185,'selected_caches':5,'component_caches_preserve_fallback':True,'geometric_claim':'Only original formal evaluator rows, not geometric GW identification.'},'Mathematical scope drift')
 need(record['proof_source_changes']==[],'Unexpected proof changes')
 need(record['status']=='actual10_builds_and285_audits_passed' and record['kind']=='f1_actual_rows126_to130_followup','Wrong scope')
 for key,sha in [('plan',PLAN_SHA),('ledger',LEDGER_SHA),('isolated_acceptance',ISOLATED_SHA)]:need(record[key]['sha256']==sha,'Changed authoritative frame')
 plan,ledger,isolated=[b.json(record[k])for k in ['plan','ledger','isolated_acceptance']]
 need(plan['target_count']==10 and plan['distinct_exact_audit_count']==285,'Wrong target scope')
 need(ledger['status']=='all10_repository_targets_passed_audit_and_warning_review_pending','Incomplete actual ledger')
 need(isolated['status']=='selected_caches_and_original37_slot_rows126_130_kernel_accepted','Missing isolated history')
 source=record['source_closure'];rows=source['modules'];need(len(rows)==572 and len(ledger['source_sha256'])==572,'Wrong source closure size')
 bymodule={};bypath={};seen=set();external=set()
 for row in rows:
  mod=row['module'];need(row['path']==mod.replace('.','/')+'.lean' and mod not in seen,'Invalid source identity')
  data=c.relative(repository,row['path']).read_bytes();need(c.sha(data)==row['sha256']==ledger['source_sha256'].get(row['path']),'Source or authoritative build-source drift')
  need(b.get({'sha256':row['sha256']})==data,'Archived source differs')
  need(helper.lean_imports(data.decode())==row['imports'],'Changed lexical imports')
  for dep in row['imports']:
   if dep.startswith(('AxiomaticGW.','AxiomaticGWTest.')):need(dep in seen,'Non-topological import closure')
   else:external.add(dep)
  bymodule[mod]=row;bypath[row['path']]=data.decode().splitlines();seen.add(mod)
 roots=[x['module']for x in plan['targets']];need(source['roots']==roots,'Wrong roots')
 reachable=set()
 def visit(m):
  if m in reachable:return
  need(m in bymodule,'Missing dependency');reachable.add(m)
  for dep in bymodule[m]['imports']:
   if dep.startswith(('AxiomaticGW.','AxiomaticGWTest.')):visit(dep)
 for m in roots:visit(m)
 need(reachable==seen and sorted(external)==source['external_imports'],'Extraneous closure')
 need(len(record['configuration'])==3 and {p['path']for p in record['configuration']}==c.CONFIG,'Config scope')
 expected_config={Path(p['path']).name:p['sha256']for p in ledger['config']if Path(p['path']).name in c.CONFIG}
 need({p['path']:p['sha256']for p in record['configuration']}==expected_config,'Configuration differs from authoritative ledger')
 for pin in record['configuration']:
  data=c.relative(repository,pin['path']).read_bytes();need(c.sha(data)==pin['sha256'] and b.get(pin)==data,'Config drift')
 need([s['module']for s in ledger['steps']]==roots and len(record['runs'])==10,'Actual build coverage')
 warning_categories={};warning_occurrences=0;peak=0
 def classify(block):
  if block in warning_categories:return
  match=re.fullmatch(r'warning: ([^:\n]+):(\d+):(\d+): (.*)',block,re.S);need(match is not None,'Warning format')
  path,line,column,body=match.groups();need(path in bypath and 1<=int(line)<=len(bypath[path]),'Warning outside closure')
  actual=bypath[path][int(line)-1];m=re.search(r'`set_option (linter\.style\.[A-Za-z]+) false`$',body);need(m is not None,'Warning category')
  category=m[1]
  if category=='linter.style.maxHeartbeats':need(body.startswith('Please, add a comment explaining the need for modifying the maxHeartbeat limit, as in\n') and re.fullmatch(r'\s*set_option maxHeartbeats \d+ in\s*',actual),'Heartbeat source binding')
  elif category=='linter.style.setOption':need(body.startswith('Unscoped option maxHeartbeats is not allowed:\n') and re.fullmatch(r'\s*set_option maxHeartbeats \d+\s*',actual),'Option source binding')
  elif category=='linter.style.longLine':need(body.startswith('This line exceeds the 100 character limit, please shorten it!\n') and int(column)==100 and len(actual)>100,'Long-line source binding')
  else:raise ValueError('Unreviewed warning category')
  warning_categories[block]=category
 for step,run,target in zip(ledger['steps'],record['runs'],plan['targets']):
  mod=step['module'];need(step['status']=='passed' and run['module']==mod,'Unaccepted target')
  need(step['source']['sha256']==bymodule[mod]['sha256']==target['repository_source_sha256_required'],'Built source mismatch')
  need(target['source_imports']==bymodule[mod]['imports'],'Target import mismatch')
  for phase,cap_seconds,compiling in [('prerequisites',30,False),('build',120,True)]:
   need(run[phase+'_metadata']==step[phase],'Unbound actual metadata');meta=b.json(run[phase+'_metadata']);log=b.get(run[phase+'_log']).decode()
   need(meta['log']==run[phase+'_log'],'Wrong actual log pin');need(meta['status']=='passed' and meta['exit_code']==0 and not meta['violations'],'Failed actual command')
   cmd=meta['command'];need(Path(cmd[0]).name=='lake','Wrong executable')
   expected=[cmd[0],'--no-ansi','--no-cache']+(['build',mod]if compiling else['--no-build','build',*target['source_imports']])
   need(cmd==expected and meta['timeout_seconds']==cap_seconds and meta['rss_limit_bytes']==3*1024**3,'Changed actual command/resource cap')
   need(meta['max_sampled_concurrent_lean_children']==int(compiling) and 0<=meta['peak_sampled_lean_rss_bytes']<=3*1024**3,'Resource observation')
   if compiling:need(meta['peak_sampled_lean_rss_bytes']>0,'Missing compilation observation')
   peak=max(peak,meta['peak_sampled_lean_rss_bytes'])
   need('Build completed successfully' in log or 'All targets up-to-date' in log,'No build completion')
   need(not re.search(r'\berror:|sorryAx|memory_exception|declaration uses .sorry.',log),'Proof diagnostic')
   blocks=c.warning_blocks(log);warning_occurrences+=len(blocks)
   for block in blocks:classify(block)
 need(record['actual_audit']['metadata']['sha256']=='cd5820036b5f189f09c8a05d1e49ae150360b02b1f313116a100d4de8968d687' and record['actual_audit']['log']['sha256']=='50c1612b3c163d6df1a749350d89afee22d7c448d47d45b91c1e4ce859d4ae8d','Changed actual audit evidence')
 audit=record['actual_audit'];meta=b.json(audit['metadata']);text=b.get(audit['log']).decode();src=b.get(audit['source']).decode();expected=b.json(audit['expected'])
 need(meta['status']=='passed' and meta['exit_code']==0 and meta['command']==plan['combined_audit']['command'],'Actual audit failed')
 need(audit['source']==plan['combined_audit']['source'] and audit['expected']==plan['combined_audit']['expected'],'Changed audit frame')
 names=[n for row in plan['targets']for n in row['audit_names']]
 need(len(names)==len(set(names))==285 and expected['names']==names,'Audit scope')
 need(helper.lean_imports(src)==roots and re.findall(r'^#print axioms (\S+)$',src,re.M)==names,'Audit source scope')
 actual=helper.parse_audits(text);need(list(actual)==names and actual==expected['expected_axioms']==isolated['audits'],'Changed actual/isolated axioms')
 need(len(isolated['runs'])==10,'Historical isolated run count')
 for run in isolated['runs']:
  manifest=b.json(run['manifest']);details=b.json(run['details']);meta=b.json(run['metadata']);lines=b.get(run['log']).decode().splitlines()
  need(meta['status']=='passed' and meta['exit_code']==0 and details['status']=='passed','Historical failure')
  need(len(details['commands'])==2 and all(x['exit_code']==0 and '--memory=2048' in x['command']for x in details['commands']),'Historical resource/command scope')
  need(c.loads(lines[0])['start']==manifest['public_modules'][0]['destination'] and c.loads(lines[-1])==details,'Historical exact log boundaries')
  observed=helper.parse_audits('\n'.join(lines[1:-1]));need(list(observed)==manifest['audit_names'] and observed==run['audits'],'Historical audit mismatch')
 need(record['full815_constant_accepted'] is False and record['geometric_CohFT_accepted'] is False,'Scope overstatement')
 return {'actual_targets':10,'exact_axiom_audits':285,'sources':572,'distinct_reviewed_style_warnings':len(warning_categories),'warning_occurrences':warning_occurrences,'peak_sampled_lean_rss_bytes':peak,'historical_isolated_runs':10}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('record',type=Path);a.add_argument('--repository',type=Path,required=True);a.add_argument('--common-checker',type=Path);x=a.parse_args()
 print(json.dumps(check_record(json.loads(x.record.read_text()),x.repository,x.common_checker)))
