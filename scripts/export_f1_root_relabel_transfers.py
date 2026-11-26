"""Generate source-bound outer-label transfers; never evaluate component backends."""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'AxiomaticGW/Tautological/L24Gluing.lean'
CLAIMS = 'AxiomaticGW/Tautological/Fixtures/L24Claims.lean'
# The held packet selects the original nonzero lower-genus frame only. Its slot
# values are deliberately never read or used to generate equality proofs.
PINS = {'AxiomaticGW/Tautological/L24Gluing.lean': '0bf7a0b35982faddbb69520c594a1e12061b3867121db9926daf090f278433c1', 'AxiomaticGW/Tautological/Fixtures/L24Claims.lean': '5727452cb886c8d9deb5d583c7f6293b037803a431b6c74fb4e272129042a74e', 'packet': '2504ec594a5e2d45fa8c74c98d837b8a35d53faa8019b09389b2a4240e4778a2'}

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def declaration(source: str, name: str) -> str:
    match = re.search(r'^def ' + re.escape(name) + r' :.*?:=\n(.*?)(?=\n/--|\Z)', source, re.M | re.S)
    if not match:
        raise ValueError('Missing exact declaration: ' + name)
    return match[1].strip()

def strip_outer(text: str) -> str:
    text = text.strip()
    while text.startswith('('):
        depth = 0
        for position, char in enumerate(text):
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
                if depth == 0:
                    break
        else:
            raise ValueError('Unbalanced expression')
        if position != len(text) - 1:
            break
        text = text[1:-1].strip()
    return text

def split_tuple(text: str) -> list[str]:
    stack, pieces, start = [], [], 0
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    for index, char in enumerate(text):
        if char in '([{⟨':
            stack.append(char)
        elif char in ')]}⟩':
            if not stack or stack.pop() != pairs[char]:
                raise ValueError('Unbalanced tuple')
        elif char == ',' and not stack:
            pieces.append(text[start:index].strip())
            start = index + 1
    if stack:
        raise ValueError('Unbalanced tuple')
    return pieces + [text[start:].strip()]

def normalized(text: str) -> str:
    return re.sub(r'\s+', '', strip_outer(text))

class CoordinateParser:
    """Parse only the held rational/if tree, without importing or executing source."""
    def __init__(self, text: str):
        prefix = 'fun i ↦'
        if not text.startswith(prefix):
            raise ValueError('Unexpected coordinate function')
        text = text[len(prefix):]
        token_pattern = r'i\.val|if\b|then\b|else\b|[0-9]+|[()/<-]'
        self.tokens = re.findall(token_pattern, text)
        if ''.join(self.tokens) != re.sub(r'\s+', '', text):
            raise ValueError('Unsupported coordinate syntax')
        self.position = 0
    def take(self, expected: str | None = None) -> str:
        token = self.tokens[self.position]
        self.position += 1
        if expected is not None and token != expected:
            raise ValueError((expected, token))
        return token
    def peek(self) -> str | None:
        return self.tokens[self.position] if self.position < len(self.tokens) else None
    def atom(self):
        token = self.take()
        if token == '(':
            result = self.expression()
            self.take(')')
            return result
        if token == '-':
            return ('neg', self.atom())
        if token == 'if':
            self.take('i.val'); self.take('<'); bound = int(self.take()); self.take('then')
            yes = self.expression(); self.take('else'); no = self.expression()
            return ('if', bound, yes, no)
        if token.isdigit():
            return ('literal', Fraction(int(token)))
        raise ValueError('Unsupported coordinate atom: ' + token)
    def expression(self):
        result = self.atom()
        while self.peek() == '/':
            self.take('/')
            result = ('div', result, self.atom())
        return result
    def parse(self):
        result = self.expression()
        if self.peek() is not None:
            raise ValueError('Trailing coordinate syntax')
        return result

def coordinate(tree, index: int) -> Fraction:
    op = tree[0]
    if op == 'literal': return tree[1]
    if op == 'neg': return -coordinate(tree[1], index)
    if op == 'div': return coordinate(tree[1], index) / coordinate(tree[2], index)
    if op == 'if': return coordinate(tree[2] if index < tree[1] else tree[3], index)
    raise ValueError(op)

def analyze(source: str, claims: str, packet: dict):
    tree = CoordinateParser(declaration(claims, 'fullClaim')).parse()
    permutations = {}
    for match in re.finditer(r'^def flagPermutation(\d+) : Equiv.Perm \(Fin (\d+)\) where\n  toFun := !\[([^\]]+)\]', source, re.M):
        values = [int(x.strip()) for x in match[3].split(',')]
        if sorted(values) != list(range(int(match[2]))):
            raise ValueError('Invalid source permutation')
        permutations[int(match[1])] = values
    rows = packet['rows']
    if len(rows) != 815 or any(row['held_index'] != i for i, row in enumerate(rows)):
        raise ValueError('Original815 frame changed')
    records, groups = [], defaultdict(list)
    for index, row in enumerate(rows):
        coefficient = coordinate(tree, index)
        if coefficient != Fraction(*row['coefficient']):
            raise ValueError('Packet coefficient differs from actual fullClaim at ' + str(index))
        term = declaration(source, 'term' + str(index))
        if not term.startswith('⟨') or not term.endswith('⟩'):
            raise ValueError('Unexpected term constructor')
        fields = split_tuple(term[1:-1])
        if len(fields) != 3 or not re.fullmatch(r'expression\d+', fields[0]):
            raise ValueError('Unexpected term fields')
        expression = declaration(source, fields[0])
        core = strip_outer(expression)
        outer = None
        match = re.fullmatch(r'(.*)\.relabel\s+flagPermutation(\d+)', core, re.S)
        if match:
            core, outer = strip_outer(match[1]), int(match[2])
        permutation = permutations[outer] if outer is not None else list(range(4))
        if len(permutation) != 4:
            raise ValueError('Outer labels changed')
        assignment = [0 if i == 0 else 1 for i in permutation]
        signature = [normalized(core), normalized(fields[1]), normalized(fields[2]), assignment]
        key = json.dumps(signature, separators=(',', ':'))
        record = dict(index=index, coefficient=coefficient, core=core, outer=outer,
                      expression=fields[0], decoration=fields[1], labels=fields[2],
                      transported_assignment=assignment, signature=key)
        records.append(record)
        if row['evaluated']:
            if not coefficient:
                raise ValueError('Evaluated coefficient is zero')
            groups[key].append(index)
    classes = sorted(groups.values(), key=lambda group: group[0])
    transfers = [(group[0], index) for group in classes for index in group[1:]]
    if sum(map(len, classes)) != 694 or len(classes) != 280 or len(transfers) != 414:
        raise ValueError('Held structural partition changed')
    return records, classes, transfers

def rational(value: Fraction) -> str:
    return '(' + str(value.numerator) + ' / ' + str(value.denominator) + ' : ℚ)'

def equiv(record: dict) -> str:
    return '(Equiv.refl (Fin 4))' if record['outer'] is None else 'L24Gluing.flagPermutation' + str(record['outer'])

HEADER = '''/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointRelabel
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly

/-!
# Source-bound reuse of original F1 external assignments

Only identical gluing cores, cotangent decorations and label decisions are
shared. The actual pulled-back HEEE assignments are checked at all four labels.
Original relation coordinates remain outside each contraction. Component
backends and sampled slot values are never evaluated or assumed here.
-/

@[expose] public section
set_option Elab.async false

'''

def module_text(name: str, pairs: list[tuple[int, int]], records: list[dict]):
    if len(pairs) > 25:
        raise ValueError('Module exceeds25 transfers')
    namespace = 'AxiomaticGW.BlowupF1RootRelabelTransfers.' + name
    chunks = [HEADER, 'namespace ' + namespace + '\n\n',
              'open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing\n\n']
    audits = []
    representatives = sorted({a for a, _ in pairs})
    for rep in representatives:
        chunks.append(f'private def core{rep} : GluingExpression 2 (Fin 4) :=\n  {records[rep]["core"]}\n\n')
    for index in sorted({i for pair in pairs for i in pair}):
        chunks.append(f'theorem coefficient{index} : L24CorrectionsReplay.fullClaim {index} =\n    {rational(records[index]["coefficient"])} := by decide +kernel\n\n')
        audits.append(namespace + '.coefficient' + str(index))
    for rep, target in pairs:
        a, b = records[rep], records[target]
        if a['signature'] != b['signature'] or not a['coefficient']:
            raise ValueError('Unsupported structural transfer')
        chunks.append(f'''/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels{rep}_{target} :
    insertions ∘ {equiv(a)} =
      insertions ∘ {equiv(b)} := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar{rep}_eq{target} (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term {rep}).expression.scalarPointContraction X v
      (L24Gluing.term {rep}).decoration (L24Gluing.term {rep}).labels beta n insertions =
    (L24Gluing.term {target}).expression.scalarPointContraction X v
      (L24Gluing.term {target}).decoration (L24Gluing.term {target}).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core{rep} L24Gluing.term{rep}.decoration L24Gluing.term{rep}.labels
    {equiv(a)} {equiv(b)} beta n insertions labels{rep}_{target}

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded{rep}_eq{target} (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term {rep}) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term {target}) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term {rep}) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term {target}) (by decide +kernel)]
  exact scalar{rep}_eq{target} _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted{target}_eq{rep} : originalWeighted {target} =
    {rational(b['coefficient'] / a['coefficient'])} * originalWeighted {rep} := by
  rw [originalWeighted, originalWeighted, ← guarded{rep}_eq{target},
    coefficient{target}, coefficient{rep}]
  ring

''')
        audits.extend(namespace + '.' + label for label in
                      [f'labels{rep}_{target}', f'scalar{rep}_eq{target}',
                       f'guarded{rep}_eq{target}', f'weighted{target}_eq{rep}'])
    chunks.append('end ' + namespace + '\n')
    return ''.join(chunks), audits

def generate(repository: Path, packet_path: Path, output: Path):
    raw = {SOURCE: (repository / SOURCE).read_bytes(), CLAIMS: (repository / CLAIMS).read_bytes(),
           'packet': packet_path.read_bytes()}
    for key, data in raw.items():
        if digest(data) != PINS[key]:
            raise ValueError('Source pin mismatch before parsing: ' + key)
    if output.exists():
        raise ValueError('Output must be a new directory')
    records, classes, transfers = analyze(raw[SOURCE].decode(), raw[CLAIMS].decode(), json.loads(raw['packet']))
    pilot = [(121, 140), (121, 155), (122, 141), (122, 156), (744, 762), (744, 788)]
    if not set(pilot) <= set(transfers):
        raise ValueError('Pilot differs from structural partition')
    output.mkdir(parents=True)
    modules = []
    for name, pairs in [('Pilot', pilot)] + [('Batch' + str(i // 25).zfill(2), transfers[i:i+25]) for i in range(0, len(transfers), 25)]:
        text, audits = module_text(name, pairs, records)
        relative = 'AxiomaticGW/Surfaces/Fixtures/BlowupF1RootRelabelTransfers/' + name + '.lean'
        path = output / relative; path.parent.mkdir(parents=True, exist_ok=True);path.write_text(text)
        modules.append(dict(destination=relative, source=str(path), sha256=digest(path.read_bytes()),
                            transfers=[{'representative':a, 'target':b,
                            'coefficient_ratio':[(records[b]['coefficient'] / records[a]['coefficient']).numerator,
                                                 (records[b]['coefficient'] / records[a]['coefficient']).denominator],
                            'signature_sha256':digest(records[a]['signature'].encode())} for a,b in pairs], audit_names=audits))
    manifest={'status':'source_bound_staging_not_Lean_accepted','pins':PINS,'classes':classes,
              'evaluated_rows':694,'class_count':280,'transfer_count':414,'modules':modules,
              'pilot_module':modules[0]['destination'],'batch_member_bound':25,
              'method':'Exact core/decorations/label decisions plus finite equality of transportedHEEE only; source fullClaim tree parsed without execution and matched against all815packet coefficients. Packet slot values are never read.',
              'geometric_or_vertex_equivariance_hypothesis':False,'backend_evaluation':False}
    (output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository',type=Path,default=ROOT)
    parser.add_argument('--packet',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args()
    result=generate(args.repository.resolve(),args.packet.resolve(),args.output_dir.resolve())
    print(json.dumps({'transfer_count':result['transfer_count'],'module_count':len(result['modules']),'pilot_count':len(result['modules'][0]['transfers'])}))

if __name__=='__main__':
    main()
