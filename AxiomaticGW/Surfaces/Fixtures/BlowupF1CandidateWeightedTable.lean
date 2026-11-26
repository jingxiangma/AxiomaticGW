/- Candidate arithmetic only. Frozen original815 values; no contraction equality is asserted. -/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section
set_option Elab.async false

namespace AxiomaticGW.BlowupF1CandidateWeightedTable
open scoped BigOperators

/-- Original indices 0 through 31, in order. -/
def block00 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block00_sum : (∑ i, block00 i) = 0 := by
  decide +kernel

/-- Original indices 32 through 63, in order. -/
def block01 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block01_sum : (∑ i, block01 i) = 0 := by
  decide +kernel

/-- Original indices 64 through 95, in order. -/
def block02 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block02_sum : (∑ i, block02 i) = 0 := by
  decide +kernel

/-- Original indices 96 through 127, in order. -/
def block03 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, (1 / 2160 : ℚ), (4259 / 505440 : ℚ),
  (161 / 38880 : ℚ), (-745 / 50544 : ℚ), 0,
  0, 0]

theorem block03_sum : (∑ i, block03 i) = (-1 / 585 : ℚ) := by
  decide +kernel

/-- Original indices 128 through 159, in order. -/
def block04 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  (3527 / 758160 : ℚ), (3527 / 758160 : ℚ), (-745 / 75816 : ℚ),
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  (3527 / 758160 : ℚ), (3527 / 758160 : ℚ), (-745 / 75816 : ℚ),
  0, 0]

theorem block04_sum : (∑ i, block04 i) = (-11 / 10530 : ℚ) := by
  decide +kernel

/-- Original indices 160 through 191, in order. -/
def block05 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, (-1481 / 151632 : ℚ), (-161 / 19440 : ℚ),
  (1525 / 75816 : ℚ), 0, 0,
  0, 0, 0,
  0, (4259 / 1010880 : ℚ), (1 / 4320 : ℚ),
  (161 / 77760 : ℚ), (-745 / 101088 : ℚ), 0,
  0, 0, 0,
  0, 0]

theorem block05_sum : (∑ i, block05 i) = (17 / 14040 : ℚ) := by
  decide +kernel

/-- Original indices 192 through 223, in order. -/
def block06 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  (4259 / 1010880 : ℚ), (1 / 4320 : ℚ), (161 / 77760 : ℚ),
  (-745 / 101088 : ℚ), 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, (-1285 / 134784 : ℚ)]

theorem block06_sum : (∑ i, block06 i) = (-7001 / 673920 : ℚ) := by
  decide +kernel

/-- Original indices 224 through 255, in order. -/
def block07 : Fin 32 → ℚ := ![
  (-161 / 17280 : ℚ), (745 / 33696 : ℚ), 0,
  0, 0, 0,
  0, 0, 0,
  (3527 / 1516320 : ℚ), (3527 / 1516320 : ℚ), (-745 / 151632 : ℚ),
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  (-1481 / 303264 : ℚ), (-161 / 38880 : ℚ), (1525 / 151632 : ℚ),
  0, 0]

theorem block07_sum : (∑ i, block07 i) = (3047 / 224640 : ℚ) := by
  decide +kernel

/-- Original indices 256 through 287, in order. -/
def block08 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, (-1481 / 303264 : ℚ), (-161 / 38880 : ℚ),
  (1525 / 151632 : ℚ), 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, (-1 / 360 : ℚ),
  (-1 / 360 : ℚ), 0, 0,
  (1 / 864 : ℚ), (1 / 480 : ℚ), (-1 / 2160 : ℚ),
  (-1 / 2160 : ℚ), (-1 / 2160 : ℚ), 0,
  (1 / 2160 : ℚ), (1 / 2160 : ℚ)]

theorem block08_sum : (∑ i, block08 i) = (-49 / 28080 : ℚ) := by
  decide +kernel

/-- Original indices 288 through 319, in order. -/
def block09 : Fin 32 → ℚ := ![
  0, (1 / 2160 : ℚ), (1 / 2160 : ℚ),
  0, 0, 0,
  (1 / 1440 : ℚ), (-1 / 180 : ℚ), 0,
  0, (1 / 240 : ℚ), (1 / 432 : ℚ),
  0, 0, (1 / 240 : ℚ),
  (1 / 432 : ℚ), 0, 0,
  0, (1 / 240 : ℚ), 0,
  (1 / 1080 : ℚ), (1 / 1080 : ℚ), 0,
  0, 0, (1 / 720 : ℚ),
  0, 0, 0,
  (1 / 720 : ℚ), (1 / 17280 : ℚ)]

theorem block09_sum : (∑ i, block09 i) = (103 / 5760 : ℚ) := by
  decide +kernel

/-- Original indices 320 through 351, in order. -/
def block10 : Fin 32 → ℚ := ![
  (1 / 480 : ℚ), (1 / 4320 : ℚ), (1 / 4320 : ℚ),
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block10_sum : (∑ i, block10 i) = (11 / 4320 : ℚ) := by
  decide +kernel

/-- Original indices 352 through 383, in order. -/
def block11 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block11_sum : (∑ i, block11 i) = 0 := by
  decide +kernel

/-- Original indices 384 through 415, in order. -/
def block12 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block12_sum : (∑ i, block12 i) = 0 := by
  decide +kernel

/-- Original indices 416 through 447, in order. -/
def block13 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, (-73 / 56160 : ℚ), 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, (-73 / 84240 : ℚ),
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  (-73 / 84240 : ℚ), 0, 0,
  0, 0]

theorem block13_sum : (∑ i, block13 i) = (-511 / 168480 : ℚ) := by
  decide +kernel

/-- Original indices 448 through 479, in order. -/
def block14 : Fin 32 → ℚ := ![
  0, (7 / 3744 : ℚ), 0,
  0, 0, 0,
  0, 0, (-73 / 224640 : ℚ),
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  (-73 / 224640 : ℚ), 0, 0,
  0, 0, 0,
  (73 / 74880 : ℚ), 0, 0,
  0, 0, 0,
  0, (-73 / 336960 : ℚ)]

theorem block14_sum : (∑ i, block14 i) = (1333 / 673920 : ℚ) := by
  decide +kernel

/-- Original indices 480 through 511, in order. -/
def block15 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, (7 / 14976 : ℚ),
  0, 0, (7 / 14976 : ℚ),
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block15_sum : (∑ i, block15 i) = (7 / 7488 : ℚ) := by
  decide +kernel

/-- Original indices 512 through 543, in order. -/
def block16 : Fin 32 → ℚ := ![
  0, 0, 0,
  (-539 / 67392 : ℚ), (101 / 18720 : ℚ), (1 / 4320 : ℚ),
  (67 / 25920 : ℚ), (-539 / 67392 : ℚ), (101 / 18720 : ℚ),
  (1 / 4320 : ℚ), (67 / 25920 : ℚ), (539 / 22464 : ℚ),
  0, 0, 0,
  (-553 / 44928 : ℚ), (-67 / 5760 : ℚ), (-539 / 101088 : ℚ),
  (2923 / 1010880 : ℚ), (2923 / 1010880 : ℚ), (1085 / 101088 : ℚ),
  0, 0, 0,
  (-19 / 3159 : ℚ), (-67 / 12960 : ℚ), (1085 / 101088 : ℚ),
  0, 0, 0,
  (-19 / 3159 : ℚ), (-67 / 12960 : ℚ)]

theorem block16_sum : (∑ i, block16 i) = (1 / 33696 : ℚ) := by
  decide +kernel

/-- Original indices 544 through 575, in order. -/
def block17 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, (1 / 360 : ℚ), (1 / 360 : ℚ),
  0, 0, (-1 / 432 : ℚ),
  (1 / 720 : ℚ), (1 / 2160 : ℚ), (1 / 2160 : ℚ),
  (1 / 2160 : ℚ), 0, 0,
  (-1 / 2160 : ℚ), (-1 / 2160 : ℚ), 0,
  0, (-1 / 2160 : ℚ), (-1 / 2160 : ℚ),
  0, 0, 0,
  (-1 / 240 : ℚ), (1 / 360 : ℚ), 0,
  0, (1 / 720 : ℚ), (-1 / 432 : ℚ),
  0, 0]

theorem block17_sum : (∑ i, block17 i) = (1 / 540 : ℚ) := by
  decide +kernel

/-- Original indices 576 through 607, in order. -/
def block18 : Fin 32 → ℚ := ![
  (1 / 720 : ℚ), (-1 / 432 : ℚ), 0,
  0, 0, (-1 / 80 : ℚ),
  0, 0, (-1 / 2160 : ℚ),
  (-1 / 2160 : ℚ), 0, 0,
  0, (-1 / 240 : ℚ), 0,
  0, 0, (-1 / 240 : ℚ),
  0, 0, 0,
  0, (-1 / 8640 : ℚ), (-1 / 960 : ℚ),
  (-1 / 8640 : ℚ), (-1 / 8640 : ℚ), 0,
  (1 / 8640 : ℚ), (-1 / 576 : ℚ), (1 / 8640 : ℚ),
  0, (1 / 8640 : ℚ)]

theorem block18_sum : (∑ i, block18 i) = (-11 / 432 : ℚ) := by
  decide +kernel

/-- Original indices 608 through 639, in order. -/
def block19 : Fin 32 → ℚ := ![
  (-1 / 576 : ℚ), (1 / 8640 : ℚ), 0,
  0, (1 / 960 : ℚ), (1 / 960 : ℚ),
  0, (-1 / 2880 : ℚ), (-1 / 2880 : ℚ),
  (-1 / 2880 : ℚ), 0, 0,
  (1 / 2880 : ℚ), (1 / 2880 : ℚ), 0,
  0, (1 / 2880 : ℚ), (1 / 2880 : ℚ),
  0, 0, 0,
  (7 / 8640 : ℚ), 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block19_sum : (∑ i, block19 i) = (7 / 4320 : ℚ) := by
  decide +kernel

/-- Original indices 640 through 671, in order. -/
def block20 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  (1 / 17280 : ℚ), 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block20_sum : (∑ i, block20 i) = (1 / 17280 : ℚ) := by
  decide +kernel

/-- Original indices 672 through 703, in order. -/
def block21 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block21_sum : (∑ i, block21 i) = 0 := by
  decide +kernel

/-- Original indices 704 through 735, in order. -/
def block22 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0]

theorem block22_sum : (∑ i, block22 i) = 0 := by
  decide +kernel

/-- Original indices 736 through 767, in order. -/
def block23 : Fin 32 → ℚ := ![
  0, 0, 0,
  0, 0, 0,
  0, 0, (-227 / 224640 : ℚ),
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, (-227 / 224640 : ℚ),
  0, 0, 0,
  0, 0]

theorem block23_sum : (∑ i, block23 i) = (-227 / 112320 : ℚ) := by
  decide +kernel

/-- Original indices 768 through 799, in order. -/
def block24 : Fin 32 → ℚ := ![
  0, 0, (227 / 74880 : ℚ),
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, 0,
  0, 0, (-227 / 336960 : ℚ),
  0, 0, 0,
  0, 0, 0,
  0, (187 / 134784 : ℚ), 0,
  0, 0]

theorem block24_sum : (∑ i, block24 i) = (631 / 168480 : ℚ) := by
  decide +kernel

/-- Original indices 800 through 814, in order. -/
def block25 : Fin 15 → ℚ := ![
  0, 0, 0,
  0, (187 / 134784 : ℚ), 0,
  0, 0, 0,
  (-77 / 112320 : ℚ), (-77 / 112320 : ℚ), (77 / 37440 : ℚ),
  (-77 / 168480 : ℚ), (31 / 33696 : ℚ), (31 / 33696 : ℚ)]

theorem block25_sum : (∑ i, block25 i) = (2329 / 673920 : ℚ) := by
  decide +kernel

private theorem sum_append {m n : ℕ} (a : Fin m → ℚ) (b : Fin n → ℚ) :
    (∑ i, Fin.append a b i) = (∑ i, a i) + ∑ i, b i := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The complete original Fin815 table; no default or missing-row branch. -/
def claimed : Fin 815 → ℚ :=
  Fin.append block00 (
    Fin.append block01 (
      Fin.append block02 (
        Fin.append block03 (
          Fin.append block04 (
            Fin.append block05 (
              Fin.append block06 (
                Fin.append block07 (
                  Fin.append block08 (
                    Fin.append block09 (
                      Fin.append block10 (
                        Fin.append block11 (
                          Fin.append block12 (
                            Fin.append block13 (
                              Fin.append block14 (
                                Fin.append block15 (
                                  Fin.append block16 (
                                    Fin.append block17 (
                                      Fin.append block18 (
                                        Fin.append block19 (
                                          Fin.append block20 (
                                            Fin.append block21 (
                                              Fin.append block22 (
                                                Fin.append block23 (
                                                  Fin.append block24 (
                                                    block25)))))))))))))))))))))))))

/-- Arithmetic of the frozen candidate table, independent of every GW evaluator. -/
theorem claimed_sum : (∑ j : Fin 815, claimed j) = (1 / 288 : ℚ) := by
  calc
    (∑ j : Fin 815, claimed j) =
        0 + (
          0 + (
            0 + (
              (-1 / 585 : ℚ) + (
                (-11 / 10530 : ℚ) + (
                  (17 / 14040 : ℚ) + (
                    (-7001 / 673920 : ℚ) + (
                      (3047 / 224640 : ℚ) + (
                        (-49 / 28080 : ℚ) + (
                          (103 / 5760 : ℚ) + (
                            (11 / 4320 : ℚ) + (
                              0 + (
                                0 + (
                                  (-511 / 168480 : ℚ) + (
                                    (1333 / 673920 : ℚ) + (
                                      (7 / 7488 : ℚ) + (
                                        (1 / 33696 : ℚ) + (
                                          (1 / 540 : ℚ) + (
                                            (-11 / 432 : ℚ) + (
                                              (7 / 4320 : ℚ) + (
                                                (1 / 17280 : ℚ) + (
                                                  0 + (
                                                    0 + (
                                                      (-227 / 112320 : ℚ) + (
                                                        (631 / 168480 : ℚ) + (
                                                          (2329 / 673920 : ℚ)
        ))))))))))))))))))))))))) := by
      simp only [claimed, sum_append (m := 32) (n := 783),
        sum_append (m := 32) (n := 751),
        sum_append (m := 32) (n := 719),
        sum_append (m := 32) (n := 687),
        sum_append (m := 32) (n := 655),
        sum_append (m := 32) (n := 623),
        sum_append (m := 32) (n := 591),
        sum_append (m := 32) (n := 559),
        sum_append (m := 32) (n := 527),
        sum_append (m := 32) (n := 495),
        sum_append (m := 32) (n := 463),
        sum_append (m := 32) (n := 431),
        sum_append (m := 32) (n := 399),
        sum_append (m := 32) (n := 367),
        sum_append (m := 32) (n := 335),
        sum_append (m := 32) (n := 303),
        sum_append (m := 32) (n := 271),
        sum_append (m := 32) (n := 239),
        sum_append (m := 32) (n := 207),
        sum_append (m := 32) (n := 175),
        sum_append (m := 32) (n := 143),
        sum_append (m := 32) (n := 111),
        sum_append (m := 32) (n := 79),
        sum_append (m := 32) (n := 47),
        sum_append (m := 32) (n := 15),
        block00_sum, block01_sum, block02_sum, block03_sum,
        block04_sum, block05_sum, block06_sum, block07_sum,
        block08_sum, block09_sum, block10_sum, block11_sum,
        block12_sum, block13_sum, block14_sum, block15_sum,
        block16_sum, block17_sum, block18_sum, block19_sum,
        block20_sum, block21_sum, block22_sum, block23_sum,
        block24_sum, block25_sum]
    _ = (1 / 288 : ℚ) := by decide +kernel

end AxiomaticGW.BlowupF1CandidateWeightedTable
