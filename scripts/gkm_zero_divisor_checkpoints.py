#!/usr/bin/env python3
"""Resume native divisor-pair localization by full curve class and assemble validated receipts."""
import argparse
import fcntl
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import check_gkm_inputs as codec
from gkm_regular_fraction_table import indexed_array, ordered_surface_frame
from gkm_report_cli import explore_report
from gkm_three_point_descendants import read_report
from gkm_zero_divisor_pairs import FRAMES, emit, kind, requests


def class_frame(full, target, beta):
    return {t: [q for q in rows if t == target and q[0] == beta] for t, rows in full.items()}


def encoded(report):
    return (json.dumps(report, sort_keys=True, indent=2) + "\n").encode()


def checked(raw, frame, target):
    return read_report(raw, requests=frame, genus=2, kind=kind(target))[0]


def key(row):
    return tuple(row["class"]), tuple(row["powers"]), tuple(row["labels"])


def path_for(directory, target, beta):
    return directory / target / ("-".join(map(str, beta)) + ".json")


def field(row):
    frac = row["equivariant"]
    return codec.RationalFunction(codec.polynomial(frac["numerator"]),
                                  codec.polynomial(frac["denominator"]))


def agree(first, second):
    """Compare complete requests and both values, allowing equivalent regular representatives."""
    incoming = {key(c): c for c in second["cases"]}
    return all(c["ordinary"] == incoming[key(c)]["ordinary"] and field(c) == field(incoming[key(c)])
               for c in first["cases"])


def store(path, raw, frame, target):
    report = checked(raw, frame, target)
    if path.exists():
        if not agree(checked(path.read_bytes(), frame, target), report):
            raise ValueError(f"Conflicting native computations for {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as temp:
        temp.write(raw)
    Path(temp.name).replace(path)


def localize(target, full, beta, directory, producer):
    """Use a fresh native process per class so the producer's memory and caches remain bounded."""
    path = path_for(directory, target, beta)
    path.parent.mkdir(parents=True, exist_ok=True)
    frame = class_frame(full, target, beta)
    with path.with_suffix(".lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print(f"Another worker is localizing {target} {beta}", flush=True)
            return
        if path.is_file():
            checked(path.read_bytes(), frame, target)
        else:
            raw = explore_report(producer, frame, 2, kind(target))
            store(path, raw, frame, target)
    print(f"Verified {target} {beta}: {len(frame[target])} rows", flush=True)


def merge(target, full, classes, directory):
    incoming = {}
    metadata = None
    for beta in classes:
        path = path_for(directory, target, beta)
        if not path.is_file():
            raise ValueError(f"Native checkpoint still required for {target} {beta}")
        report = checked(path.read_bytes(), class_frame(full, target, beta), target)
        header = {k: v for k, v in report.items() if k != "cases"}
        if metadata is not None and header != metadata:
            raise ValueError("Checkpoint provenance differs")
        metadata = header
        incoming.update((key(c), c) for c in report["cases"])
    merged = encoded(dict(metadata, cases=[incoming[q] for q in full[target]]))
    checked(merged, full, target)
    return merged


def assemble(target, full, classes, directory, output):
    merged = merge(target, full, classes, directory)
    emit(merged, target)
    store(output, merged, full, target)


def partial_kind(target):
    return kind(target) + ".partial"


def read_partial(raw, target):
    """Validate the exact full-class subsets, native provenance and ordered full row keys."""
    report = json.loads(raw, object_pairs_hook=codec.unique_object)
    full = requests(target)
    coverage = report["coverage"]
    codec.require(set(coverage) == {"benchmark_rows", "complete_classes"} and
                  codec.integer(coverage["benchmark_rows"]) == len(full[target]), "Wrong benchmark size")
    classes = [tuple(map(codec.integer, beta)) for beta in coverage["complete_classes"]]
    known = {q[0] for q in full[target]}
    codec.require(classes and len(set(classes)) == len(classes) and set(classes) < known,
                  "Partial coverage must list distinct, proper benchmark classes")
    selected = dict(full, **{target: [q for q in full[target] if q[0] in classes]})
    checked_report, grouped = read_report(raw, requests=selected, genus=2, kind=partial_kind(target))
    by_key = {key(row): row for row in grouped[target]}
    return checked_report, [by_key[q] for q in selected[target]]


def class_coverage_source(rows, classes, lean_target):
    """Verify both directions of native request coverage at every completely localized curve."""
    size = len(rows)
    count = len(classes)
    curves = ["![" + ", ".join(map(str, beta)) + "]" for beta in classes]
    indices = [str([j for j, row in enumerate(rows) if row["class"] == beta]) for beta in classes]
    surface = "SurfaceTarget" + lean_target
    lines = ["/-- Full curve coordinates of the completed benchmark fibers. -/",
             f"def heldClass (i : Fin {count}) : {surface}.Curve :=",
             indexed_array(curves, f"{surface}.Curve", 4), "",
             f"private def classIndices (i : Fin {count}) : List (Fin {size}) :=",
             indexed_array(indices, f"List (Fin {size})", 1), "",
             f"private theorem indices_beta (k : Fin {count}) :",
             "    ∀ i ∈ classIndices k, (requests i).beta = heldClass k :=",
             "  (by decide +kernel : ∀ j, ∀ i ∈ classIndices j, (requests i).beta = heldClass j) k", "",
             f"private def actualShapes (k : Fin {count}) :=",
             "  ((classIndices k).map (fun i ↦ (requests i).insertions)).toFinset", "",
             f"private def originalShapes (k : Fin {count}) :=",
             f"  (dimensionShapes {lean_target} ({surface}.effective.energy (heldClass k))).filter",
             f"    (fun m ↦ zeroDivisorPair? (⟨2, heldClass k, m⟩ : SurfaceQuery {lean_target}) = some 0)", ""]
    # A separate kernel decision per curve keeps each finite certificate independently small.
    for k in range(count):
        lines.append(f"private theorem shapes_{k} : actualShapes {k} = originalShapes {k} := by decide +kernel")
    lines += ["", f"private theorem sameShapes (k : Fin {count}) : actualShapes k = originalShapes k := by",
              "  fin_cases k", *(f"  · exact shapes_{k}" for k in range(count)), ""]
    return "\n".join(lines) + f"""
/-- In each completed curve class the native request frame is exactly the original benchmark. -/
theorem complete_at_class (k : Fin {count}) (q : SurfaceQuery {lean_target}) (hb : q.beta = heldClass k) :
    q ∈ ZeroDivisorBenchmark.rows {lean_target} ({surface}.effective.energy q.beta) ↔
      ∃ i, requests i = q := by
  constructor
  · intro h
    obtain ⟨hf, _, hz⟩ := (ZeroDivisorBenchmark.mem_rows _ _).mp h
    have hg : (⟨2, heldClass k, q.insertions⟩ : SurfaceQuery {lean_target}) = q :=
      (SurfaceQuery.eq_iff _ _).mpr ⟨hf.1.symm, hb.symm, rfl⟩
    have hp : 0 < {surface}.effective.energy q.beta :=
      Nat.pos_of_ne_zero fun he ↦
        hf.2.1 (({surface}.effective.energy_eq_zero_iff _).mp he)
    rw [hb] at hp
    have hm := (mem_dimensionShapes_iff (heldClass k) hp q.insertions).mpr
      ⟨hf.2.2.2.1, hg.symm ▸ hf.2.2.2.2⟩
    have has : q.insertions ∈ originalShapes k := Finset.mem_filter.mpr ⟨hm, hg.symm ▸ hz⟩
    rw [← sameShapes] at has
    obtain ⟨i, hi, hm⟩ := List.mem_map.mp (List.mem_toFinset.mp has)
    exact ⟨i, (SurfaceQuery.eq_iff _ _).mpr
      ⟨(frame i).1.1.trans hf.1.symm, (indices_beta k i hi).trans hb.symm, hm⟩⟩
  · rintro ⟨i, rfl⟩
    exact mem_rows i
"""


def partial_source(raw, target):
    """Bind the original divisor and regular full-field proofs only to actually present rows."""
    report, rows = read_partial(raw, target)
    lean_target, namespace, surface = FRAMES[target]
    name = namespace + "Partial"
    surface_type = "SurfaceTarget" + lean_target
    source = ordered_surface_frame(raw, rows, lean_target=lean_target, namespace=name,
                                   title="Completed native divisor comparisons on " + surface,
                                   generator="gkm_zero_divisor_checkpoints.py")
    source = source.replace("module\n", "module\npublic import AxiomaticGW.GKM.Fixtures.ZeroDivisorPairsReplay\n", 1)
    source += f"""
namespace AxiomaticGW.GKM.{name}
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- Each actual ordered row satisfies the hypotheses for the seed-free divisor equation. -/
theorem frame (j : Fin {len(rows)}) :
    FewMarkingQuery (requests j) ∧ zeroDivisorPair? (requests j) = some 0 :=
  (by unfold FewMarkingQuery; decide +kernel :
    ∀ i, FewMarkingQuery (requests i) ∧ zeroDivisorPair? (requests i) = some 0) j

/-- The receipt contains distinct full curve classes and ordered insertion lists. -/
theorem requests_injective : Function.Injective requests := by
  have mono : StrictMono (fun i ↦ ZeroDivisorPairsReplay.pairOrder (requests i)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    decide +kernel
  exact fun _ _ h ↦ mono.injective (congrArg ZeroDivisorPairsReplay.pairOrder h)

/-- The original bounded benchmark contains each row at its actual energy. -/
theorem mem_rows (j : Fin {len(rows)}) :
    requests j ∈ ZeroDivisorBenchmark.rows {lean_target}
      ({surface_type}.effective.energy (requests j).beta) :=
  (ZeroDivisorBenchmark.mem_rows _ _).mpr ⟨(frame j).1, rfl, (frame j).2⟩

theorem values_zero (j : Fin {len(rows)}) : values j = 0 := (by decide +kernel : ∀ i, values i = 0) j

theorem equivariant_zero (j : Fin {len(rows)}) : equivariant j = 0 := by
  rw [equivariant_eq_ordinary, values_zero, Rat.cast_zero]

/-- The original marked divisor evaluator reproduces the incoming ordinary value. -/
theorem original (pivot : Fin {surface_type}.blowups) (j : Fin {len(rows)}) :
    divisorPairValue? pivot (requests j) = some (values j) := by
  rw [values_zero]
  exact zeroDivisorPair?_original pivot _ (frame j).2

/-- Each exported row has a reconstruction witness at the public pivot. -/
theorem accepted (j : Fin {len(rows)}) : CheckedDescendant 0 (requests j) (values j) := by
  rw [values_zero]
  exact zeroDivisorPair?_checked 0 _ (frame j).2

/-- The full torus function, regular specialization and original ordered evaluator agree. -/
theorem all_accepted (pivot : Fin {surface_type}.blowups) (j : Fin {len(rows)}) :
    equivariant j = 0 ∧ EquivariantCoefficients.Specializes (equivariant j) 0 ∧
      divisorPairValue? pivot (requests j) = some 0 :=
  ⟨equivariant_zero j, (values_zero j) ▸ specializes j, (values_zero j) ▸ original pivot j⟩

{class_coverage_source(rows, report["coverage"]["complete_classes"], lean_target)}
end AxiomaticGW.GKM.{name}
"""
    return source.replace("] : Array (SurfaceQuery", "] :\n    Array (SurfaceQuery")


def snapshot(target, full, classes, directory):
    available = sorted(beta for beta in classes if path_for(directory, target, beta).is_file())
    if not available:
        raise ValueError("No native checkpoints are available")
    selected = dict(full, **{target: [q for q in full[target] if q[0] in available]})
    report = json.loads(merge(target, selected, available, directory))
    rows = report.pop("cases")
    report.update(kind=partial_kind(target),
                  coverage={"benchmark_rows": len(full[target]), "complete_classes": available})
    header = json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2)[:-2]
    # One exact receipt per line keeps even large growing frames easy to compare.
    compact_rows = [json.dumps(row, sort_keys=True, separators=(",", ":")) for row in rows]
    raw = (header + ',\n  "cases": [\n    ' + ",\n    ".join(compact_rows) + "\n  ]\n}\n").encode()
    read_partial(raw, target)
    return raw


def archive(target, full, classes, directory, output):
    raw = snapshot(target, full, classes, directory)
    report, _ = read_partial(raw, target)
    if output.is_file():
        previous, _ = read_partial(output.read_bytes(), target)
        keys = {key(row) for row in report["cases"]}
        if not all(key(row) in keys for row in previous["cases"]) or not agree(previous, report):
            raise ValueError("Updated archive would discard or change previous native receipts")
    with tempfile.NamedTemporaryFile(dir=output.parent, delete=False) as temp:
        temp.write(raw)
    Path(temp.name).replace(output)


def replay_completed(target, full, classes, directory, output):
    raw = snapshot(target, full, classes, directory)
    output.write_text(partial_source(raw, target))
    print(f"Generated {len(json.loads(raw)['cases'])} completed native comparisons out of {len(full[target])}")


def ingest(raw, target, full, directory):
    header = json.loads(raw, object_pairs_hook=codec.unique_object)
    if header["kind"] == partial_kind(target):
        report, _ = read_partial(raw, target)
        report = dict(report, kind=kind(target))
        classes = [tuple(beta) for beta in report.pop("coverage")["complete_classes"]]
    else:
        report = checked(raw, full, target)
        classes = sorted({q[0] for q in full[target]})
    for beta in classes:
        subset = dict(report, cases=[r for r in report["cases"] if tuple(r["class"]) == beta])
        path = path_for(directory, target, beta)
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.with_suffix(".lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            store(path, encoded(subset), class_frame(full, target, beta), target)


def curve(text):
    try:
        return tuple(int(x) for x in text.split(","))
    except ValueError as exc:
        raise argparse.ArgumentTypeError("Expected comma-separated full curve coordinates") from exc


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=FRAMES)
    parser.add_argument("command", choices=["resume", "class", "ingest", "assemble", "archive", "replay-partial", "replay-completed", "status"])
    parser.add_argument("--checkpoint-dir", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--producer", type=Path)
    parser.add_argument("--only-class", action="append", type=curve, default=[])
    parser.add_argument("--skip-class", action="append", type=curve, default=[])
    parser.add_argument("--report", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    target, directory = args.target, args.checkpoint_dir
    full = requests(target)
    classes = sorted({q[0] for q in full[target]}, key=lambda b: (b[-1] != 0, sum(b), b))
    selected = set(args.only_class or classes) - set(args.skip_class)
    if not set(args.only_class + args.skip_class) <= set(classes):
        parser.error("Class absent from the held divisor benchmark")
    if args.command not in ("resume", "class") and (args.only_class or args.skip_class):
        parser.error("Class selection is available for native workers")
    if args.command != "replay-partial" and directory is None:
        parser.error("--checkpoint-dir is required for local class receipts")
    if args.check and args.command != "replay-partial":
        parser.error("--check is available for replay-partial")
    if args.report and args.command not in ("resume", "ingest", "replay-partial"):
        parser.error("--report is available for resume, ingest, or replay-partial")
    if args.command == "resume":
        if not args.producer:
            parser.error("Resume requires --producer")
        if args.report:
            ingest(args.report.read_bytes(), target, full, directory)
        for beta in classes:
            if beta in selected:
                subprocess.run([sys.executable, "-B", __file__, target, "class", "--checkpoint-dir",
                                str(directory), "--producer", str(args.producer), "--only-class",
                                ",".join(map(str, beta))], check=True)
    elif args.command == "class":
        if len(selected) != 1 or not args.producer:
            parser.error("Class localization requires --producer and one --only-class")
        localize(target, full, selected.pop(), directory, args.producer)
    elif args.command == "ingest":
        if not args.report:
            parser.error("Ingest requires --report")
        ingest(args.report.read_bytes(), target, full, directory)
    elif args.command == "replay-partial":
        if not args.report or not args.output:
            parser.error("Partial replay requires --report and --output")
        source = partial_source(args.report.read_bytes(), target)
        if args.check:
            codec.require(args.output.read_text() == source, "Saved partial replay differs")
        else:
            args.output.write_text(source)
    elif args.command in ("assemble", "archive", "replay-completed"):
        if not args.output:
            parser.error("Report or source generation requires --output")
        action = {"assemble": assemble, "archive": archive, "replay-completed": replay_completed}[args.command]
        action(target, full, classes, directory, args.output)
    else:
        total = 0
        pending = []
        for beta in classes:
            path = path_for(directory, target, beta)
            if path.is_file():
                rows = checked(path.read_bytes(), class_frame(full, target, beta), target)["cases"]
                total += len(rows)
                print(f"{beta}: {len(rows)}")
            else:
                pending.append(beta)
        if pending:
            print("Awaiting receipts for " + ", ".join(map(str, pending)))
        print(f"{total} of {len(full[target])} native rows checkpointed")


if __name__ == "__main__":
    main()
