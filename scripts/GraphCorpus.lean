/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GraphEnumeration

/-!
# Bounded formal-stratum corpus benchmark

`lake exe graphCorpus` executes R2's full initial range: stable `(g,n)` with
genus at most two, at most six labelled markings, and bounds zero through
three. Smaller bounds run first so the largest cases do not delay evidence
for lower bounds. `lake exe graphCorpus --single g n d` measures one case.

Each stdout line is a JSON record of the bounded formal-stratum count and
elapsed milliseconds. Progress goes to stderr. These are counts in the raw
graph-isomorphism quotient, not dimensions of geometric relation quotients.
The benchmark uses the proved enumerator; its native runtime output is
supplementary computational evidence rather than a kernel proof of a numeral.
-/

@[expose] public section

open AxiomaticGW

namespace AxiomaticGW.GraphCorpus

/-- Measure one complete bounded corpus and emit its count as JSON. -/
def runCase (g n d : Nat) : IO Unit := do
  IO.eprintln s!"Starting g={g}, n={n}, d={d}"
  let out ← IO.getStdout
  let start ← IO.monoMsNow
  let count := (TautologicalStratum.boundedStrata (Fin n) g d).card
  -- Writing the count forces its evaluation before measuring the stop time.
  out.putStr ("{\"genus\":" ++ toString g ++ ",\"markings\":" ++ toString n ++
    ",\"bound\":" ++ toString d ++ ",\"count\":" ++ toString count)
  out.flush
  let stop ← IO.monoMsNow
  out.putStrLn (",\"elapsed_ms\":" ++ toString (stop - start) ++ "}")
  out.flush

end AxiomaticGW.GraphCorpus

open AxiomaticGW.GraphCorpus

/-- Execute the fixed corpus, or a single explicitly requested case. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    for d in List.range 4 do
      for n in List.range 7 do
        for g in List.range 3 do
          if 3 ≤ 2 * g + n then
            runCase g n d
    return 0
  | ["--single", g, n, d] =>
    match g.toNat?, n.toNat?, d.toNat? with
    | some g, some n, some d => runCase g n d; return 0
    | _, _, _ =>
      IO.eprintln "Expected nonnegative integers: --single g n d"
      return 1
  | _ =>
    IO.eprintln "Usage: lake exe graphCorpus [--single g n d]"
    return 1
