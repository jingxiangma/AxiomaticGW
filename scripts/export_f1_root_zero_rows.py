"""Stage kernel proofs for all original F1 zero-coordinate and genus-guarded rows.

The packet selects proof obligations only. Neither sampled slot values nor native
totals enter any generated proposition or proof. Generation is not Lean acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import types

ROOT = Path(__file__).resolve().parents[1]
SOURCE = "AxiomaticGW/Tautological/L24Gluing.lean"
CLAIMS = "AxiomaticGW/Tautological/Fixtures/L24Claims.lean"
ASSEMBLY = "AxiomaticGW/Surfaces/Fixtures/BlowupF1RootAssembly.lean"
HELPER = "scripts/export_f1_root_relabel_transfers.py"
PINS = {
    SOURCE: "0bf7a0b35982faddbb69520c594a1e12061b3867121db9926daf090f278433c1",
    CLAIMS: "5727452cb886c8d9deb5d583c7f6293b037803a431b6c74fb4e272129042a74e",
    ASSEMBLY: "fef5c11e89db05732e2efc9a35101099808748929e935ab81245d50d860aa47d",
    HELPER: "b6c3c2463a4b2b380790120702190c1b6e7f8fe7b015ca0aaf877dad81ebd02e",
    "packet": "2504ec594a5e2d45fa8c74c98d837b8a35d53faa8019b09389b2a4240e4778a2",
}
EXPECTED_QUERY = {
    "target": "F1", "curve_basis": ["E", "F"], "source_curve": [1, 1],
    "added_points": 1,
    "labels": ["hyperplane", "exceptional:0", "exceptional:0", "exceptional:0"],
    "original_frame_size": 815, "nonzero_relation_terms": 721,
    "low_genus_nonzero_terms": 694, "guarded_nonzero_terms": 27,
    "zero_coefficient_terms": 94,
}
ACCEPTED_REPRESENTATIVES = [121, 122, 744]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def checked_inputs(repository: Path, packet_path: Path, helper_path: Path):
    """Check every pin before executing even the pure parser helper."""
    raw = {relative: (repository / relative).read_bytes()
           for relative in [SOURCE, CLAIMS, ASSEMBLY]}
    raw["packet"] = packet_path.read_bytes()
    raw[HELPER] = helper_path.read_bytes()
    for name, data in raw.items():
        if digest(data) != PINS[name]:
            raise ValueError("Source pin mismatch before helper execution: " + name)
    helper = types.ModuleType("pinned_f1_relabel_exporter")
    helper.__file__ = str(helper_path)
    # Execute exactly the checked bytes, avoiding a second filesystem read.
    exec(compile(raw[HELPER], str(helper_path), "exec"), helper.__dict__)
    return raw, helper


def analyze(source: str, claims: str, packet: dict, helper):
    if packet.get("query") != EXPECTED_QUERY:
        raise ValueError("Original F1 query changed")
    records, classes, transfers = helper.analyze(source, claims, packet)
    coefficient_zero, genus_guard = [], []
    for i, (record, row) in enumerate(zip(records, packet["rows"])):
        for key in ["coefficient_zero", "genus_guard", "evaluated"]:
            if type(row[key]) is not bool:
                raise ValueError("Non-boolean classification at " + str(i))
        degree = row["maximum_component_genus"]
        if type(degree) is not int or degree < 0:
            raise ValueError("Invalid candidate maximum genus at " + str(i))
        zero = record["coefficient"] == 0
        if row["coefficient_zero"] != zero:
            raise ValueError("Coefficient-zero flag differs from actual source at " + str(i))
        if row["genus_guard"] != (degree >= 2):
            raise ValueError("Inconsistent candidate genus guard at " + str(i))
        if row["evaluated"] != (not zero and not row["genus_guard"]):
            raise ValueError("Inconsistent candidate evaluated flag at " + str(i))
        # Zero coefficient takes precedence: these predicates overlap in the packet.
        if zero:
            coefficient_zero.append(i)
        elif row["genus_guard"]:
            genus_guard.append(i)
    reps = [group[0] for group in classes]
    if not set(ACCEPTED_REPRESENTATIVES) <= set(reps):
        raise ValueError("Accepted representatives changed")
    groups = {
        "accepted_representatives": ACCEPTED_REPRESENTATIVES,
        "remaining_representatives": [i for i in reps if i not in ACCEPTED_REPRESENTATIVES],
        "structural_transfer_targets": [target for _, target in transfers],
        "coefficient_zero": coefficient_zero,
        "nonzero_coefficient_genus_guard": genus_guard,
    }
    if list(map(len, groups.values())) != [3, 277, 414, 94, 27]:
        raise ValueError("Original815 coverage counts changed")
    flattened = [i for indices in groups.values() for i in indices]
    if sorted(flattened) != list(range(815)):
        raise ValueError("Original815 coverage is not a disjoint exhaustive partition")
    if sorted(coefficient_zero + genus_guard) != list(range(121)):
        raise ValueError("Original zero/guard prefix changed")
    return records, groups


HEADER = '''/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly

/-!
# Original F1 rows killed by exact coordinates or the existing genus guard

Each original relation coordinate and required genus bound is checked against
the actual definitions. The statements concern the existing guarded contraction;
they do not assert vanishing of the unguarded contraction.
No sampled component value, native zero, or geometric premise is used.
-/

@[expose] public section
set_option Elab.async false

'''


def module_text(name: str, kind: str, indices: list[int], records: list[dict]):
    if not indices or len(indices) > 25 or len(set(indices)) != len(indices):
        raise ValueError("Each module requires 1–25 distinct original rows")
    if kind not in ["coefficient_zero", "nonzero_coefficient_genus_guard"]:
        raise ValueError("Unsupported zero reason")
    namespace = "AxiomaticGW.BlowupF1RootZeroRows." + name
    chunks = [HEADER, "namespace " + namespace + "\n\n", "open BlowupF1RootAssembly\n\n"]
    audits, obligations = [], []
    for index in indices:
        coefficient = records[index]["coefficient"]
        if kind == "coefficient_zero":
            if coefficient:
                raise ValueError("Nonzero source coordinate in coefficient-zero module")
            chunks.append(f'''/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient{index} : L24CorrectionsReplay.fullClaim {index} = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted{index} : originalWeighted {index} = 0 :=
  originalWeighted_eq_zero_of_coefficient {index} coefficient{index}

''')
            local = [f"coefficient{index}", f"weighted{index}"]
        else:
            if not coefficient:
                raise ValueError("Zero source coordinate in nonzero guarded module")
            chunks.append(f'''/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient{index}_nonzero : L24CorrectionsReplay.fullClaim {index} ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard{index} : 2 ≤ (L24Gluing.term {index}).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted{index} : originalWeighted {index} = 0 :=
  originalWeighted_eq_zero_of_genus_guard {index} genusGuard{index}

''')
            local = [f"coefficient{index}_nonzero", f"genusGuard{index}", f"weighted{index}"]
        audits.extend(namespace + "." + name for name in local)
        obligations.append({"original_index": index, "reason": kind,
                            "actual_coefficient": [coefficient.numerator, coefficient.denominator],
                            "weighted_theorem": namespace + ".weighted" + str(index)})
    chunks.append("end " + namespace + "\n")
    return "".join(chunks), audits, obligations


def generate(repository: Path, packet_path: Path, helper_path: Path, output: Path):
    raw, helper = checked_inputs(repository, packet_path, helper_path)
    if output.exists():
        raise ValueError("Output must be a new directory")
    records, groups = analyze(raw[SOURCE].decode(), raw[CLAIMS].decode(),
                              json.loads(raw["packet"]), helper)
    pending = []
    for kind, prefix in [("coefficient_zero", "CoefficientBatch"),
                         ("nonzero_coefficient_genus_guard", "GuardBatch")]:
        rows = groups[kind]
        for start in range(0, len(rows), 25):
            name = prefix + str(start // 25).zfill(2)
            text, audits, obligations = module_text(name, kind, rows[start:start+25], records)
            relative = "AxiomaticGW/Surfaces/Fixtures/BlowupF1RootZeroRows/" + name + ".lean"
            pending.append((relative, text, audits, obligations))
    # All validation precedes the first output write.
    output.mkdir(parents=True)
    modules = []
    for relative, text, audits, obligations in pending:
        path = output / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        modules.append({"destination": relative, "source": str(path),
                        "sha256": digest(path.read_bytes()), "rows": obligations,
                        "audit_names": audits})
    partition = {"status": "pure_source_partition_not_Lean_acceptance",
                 "original_frame": list(range(815)), "groups": groups,
                 "counts": {key: len(indices) for key, indices in groups.items()},
                 "disjoint_and_exhaustive": True,
                 "method": "Exact source coefficients and frozen structural classes. Genus metadata only selects obligations; Lean must check every actual guard.",
                 "scope": "The 3 accepted representatives are designated by prior evidence; this generator does not independently revalidate that evidence or the 277 remaining representatives or 414 staged transfers."}
    (output / "coverage.json").write_text(json.dumps(partition, indent=2) + "\n")
    all_audits = [name for module in modules for name in module["audit_names"]]
    imports = ["import " + m["destination"][:-5].replace("/", ".") for m in modules]
    audit_text = "\n".join(imports + ["", "set_option Elab.async false", ""] +
                           ["#print axioms " + name for name in all_audits]) + "\n"
    (output / "F1RootZeroAudit.lean").write_text(audit_text)
    manifest = {"status": "source_bound_staging_not_Lean_accepted", "pins": PINS,
                "modules": modules, "row_count": 121, "audit_count": len(all_audits),
                "batch_member_bound": 25, "coverage": "coverage.json",
                "coverage_sha256": digest((output / "coverage.json").read_bytes()),
                "audit_source": "F1RootZeroAudit.lean",
                "audit_sha256": digest((output / "F1RootZeroAudit.lean").read_bytes()),
                "acceptance_plan": {
                    "resource_limit_mib": 2048, "sequential_modules": True,
                    "required": ["Compile all six generated public modules after authorization.",
                                 "Compile the 269-name public audit and match every exact name.",
                                 "Allow only propext, Classical.choice, Quot.sound; reject missing or extra names.",
                                 "Preserve and review all errors, warnings, source hashes and command logs."],
                    "lean_jobs_run": False},
                "new_hypotheses_or_global_simp_or_instances": False,
                "native_values_read_or_assumed": False,
                "boundary": "Zero of the existing guarded originalWeighted rows only. No unguarded geometric vanishing or final 815-row numerical acceptance."}
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=ROOT)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--relabel-exporter", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    repository = args.repository.resolve()
    helper = (args.relabel_exporter or repository / HELPER).resolve()
    result = generate(repository, args.packet.resolve(), helper, args.output_dir.resolve())
    print(json.dumps({"rows": result["row_count"], "modules": len(result["modules"]),
                      "audit_count": result["audit_count"], "status": result["status"]}))


if __name__ == "__main__":
    main()
