import copy,importlib.util,json,unittest,base64,zlib,hashlib
from pathlib import Path
import argparse
p=argparse.ArgumentParser();p.add_argument('--checker',type=Path,default=Path('scripts/check_f1_root_zero_record.py'));p.add_argument('--record',type=Path,default=Path('environments/genus-two-f1-root-zero-validation.json'));p.add_argument('--repo',type=Path,default=Path.cwd());cfg,rest=p.parse_known_args()
s=importlib.util.spec_from_file_location('check',cfg.checker);c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
R=c.loads(cfg.record.read_text());REPO=cfg.repo
def changed_object(r,pin,edit):
 e=c.loads(zlib.decompress(base64.b64decode(r['portable_evidence']['payload'])));old=pin['sha256'];data=c.loads(e['blobs'][old]);edit(data);text=json.dumps(data);new=c.digest(text.encode());e['blobs'][new]=text;e['paths'][pin['path']]=new;pin['sha256']=new
 raw=json.dumps(e).encode();r['portable_evidence'].update(payload=base64.b64encode(zlib.compress(raw)).decode(),uncompressed_sha256=c.digest(raw),unique_text_blobs=len(e['blobs']))
class Controls(unittest.TestCase):
 def test_original_no_tmp_reads(self):
  orig=Path.read_bytes;orig_text=Path.read_text
  def read(p):
   if str(p).startswith('/tmp/') or str(p).startswith('/private/tmp/'):raise AssertionError('temporary evidence read')
   return orig(p)
  def read_text(p,*args,**kwargs):
   if str(p).startswith('/tmp/') or str(p).startswith('/private/tmp/'):raise AssertionError('temporary evidence read')
   return orig_text(p,*args,**kwargs)
  from unittest.mock import patch
  with patch.object(Path,'read_bytes',read),patch.object(Path,'read_text',read_text):self.assertEqual(c.check(copy.deepcopy(R),REPO)['exact_audits'],156)
 def test_scope_overstatement(self):
  r=copy.deepcopy(R);r['acceptance']['full722_actual_repository_rebuild']=True
  with self.assertRaises(ValueError):c.check(r,REPO)
 def test_wrong_source(self):
  r=copy.deepcopy(R);r['source_sha256'][next(iter(r['source_sha256']))]='0'*64
  with self.assertRaises(ValueError):c.check(r,REPO)
 def test_bad_archive(self):
  r=copy.deepcopy(R);r['portable_evidence']['uncompressed_sha256']='0'*64
  with self.assertRaises(ValueError):c.check(r,REPO)
 def test_missing_build(self):
  r=copy.deepcopy(R);changed_object(r,r['actual_repository_validation']['serial_ledger'],lambda j:j['steps'].pop())
  with self.assertRaises(ValueError):c.check(r,REPO)
 def test_build_scope_substitution(self):
  r=copy.deepcopy(R);changed_object(r,r['actual_repository_validation']['serial_ledger'],lambda j:j['steps'][53].update(module=j['steps'][52]['module']))
  with self.assertRaises(ValueError):c.check(r,REPO)
 def test_unobserved_rebuild_claim(self):
  r=copy.deepcopy(R);changed_object(r,r['actual_repository_validation']['serial_ledger'],lambda j:j['steps'][53]['resource_observation'].update(positive_lean_observation=False))
  with self.assertRaises(ValueError):c.check(r,REPO)
 def test_hide_failed_history(self):
  r=copy.deepcopy(R);changed_object(r,r['actual_repository_validation']['prior_stopped_ledger'],lambda j:j.update(status='passed'))
  with self.assertRaises(ValueError):c.check(r,REPO)
 def test_foreign_axiom(self):
  with self.assertRaises(ValueError):c.parse_audits("'A.x' depends on axioms: [sorryAx]")
 def test_duplicate_audit(self):
  with self.assertRaises(ValueError):c.parse_audits("'A.x' does not depend on any axioms\n'A.x' does not depend on any axioms")
 def test_altered_imports_preserve_sources_and_reachability(self):
  r=copy.deepcopy(R)
  def edit(j):
   before={x['module']:x['source']['sha256'] for x in j['project_modules']}
   target=next(x for x in j['project_modules'] if x['module']=='AxiomaticGW.Surfaces.GenusTwoResidualLookup')
   dependency='AxiomaticGW.Combinatorics.StableArity'
   self.assertIn(dependency,before);self.assertNotIn(dependency,target['imports'])
   graph={x['module']:x['imports'] for x in j['project_modules']}
   def reachable(start):
    seen=set();todo=[start]
    while todo:
     name=todo.pop()
     if name in seen:continue
     seen.add(name);todo.extend(graph.get(name,[]))
    return seen
   previous=reachable(target['module']);self.assertIn(dependency,previous)
   target['imports'].append(dependency);self.assertEqual(reachable(target['module']),previous)
   self.assertEqual(len(j['project_modules']),284);self.assertEqual(before,{x['module']:x['source']['sha256'] for x in j['project_modules']})
  changed_object(r,r['source_closure'],edit)
  with self.assertRaisesRegex(ValueError,'source imports differ'):c.check(r,REPO)
 def test_import_order_is_bound(self):
  r=copy.deepcopy(R)
  def edit(j):
   target=next(x for x in j['project_modules'] if len(x['imports'])>1);target['imports'].reverse()
  changed_object(r,r['source_closure'],edit)
  with self.assertRaisesRegex(ValueError,'source imports differ'):c.check(r,REPO)
 def test_lexer_ignores_nested_comments_and_strings(self):
  source='-- import Fake.A\n/- import Fake.B /- import Fake.C -/ -/\npublic import Real.A Real.B\ndef text := "import Fake.D"\nprivate meta import Real.C\n'
  self.assertEqual(c.lean_imports(source),['Real.A','Real.B','Real.C'])
 def test_lexer_rejects_duplicate_import(self):
  with self.assertRaisesRegex(ValueError,'Duplicate direct Lean import'):c.lean_imports('import A.B\npublic import A.B\n')
 def test_each_recorded_project_config_pin_is_checked(self):
  for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
   with self.subTest(name=name):
    r=copy.deepcopy(R)
    def edit(j):next(x for x in j['config'] if Path(x['path']).name==name)['sha256']='0'*64
    changed_object(r,r['actual_repository_validation']['serial_ledger'],edit)
    with self.assertRaisesRegex(ValueError,'configuration drift '+name):c.check(r,REPO)
 def test_each_current_project_config_is_checked(self):
  from unittest.mock import patch
  orig=Path.read_bytes
  for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
   with self.subTest(name=name):
    def read(p):return b'changed configuration' if p==REPO/name else orig(p)
    with patch.object(Path,'read_bytes',read):
     with self.assertRaisesRegex(ValueError,'configuration drift '+name):c.check(copy.deepcopy(R),REPO)
 def test_closure_config_agrees_with_build_config(self):
  r=copy.deepcopy(R);changed_object(r,r['source_closure'],lambda j:j['toolchain'].update(sha256='0'*64))
  with self.assertRaisesRegex(ValueError,'closure configuration differs lean-toolchain'):c.check(r,REPO)
if __name__=='__main__':unittest.main(argv=[__file__,*rest])
