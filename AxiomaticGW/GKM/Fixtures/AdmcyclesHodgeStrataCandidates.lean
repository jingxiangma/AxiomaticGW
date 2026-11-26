/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GraphEnumeration
public import AxiomaticGW.Tautological.RelationCertificate

/-!
# Candidate raw admcycles Hodge-packet representatives

Input SHA256: 1ec7e5df068bd9edbe896dc5bf6f20f59b0e42e81896d2e4364f11efc0c6ec32
The digest records provenance only. Source marking1 labels Lean Fin1 index0.
Source numeric internal flag names are replaced by their ordered Fin edge × Fin2 labels.
No automorphism factor or graph-isomorphism canonicalization is added.
Graph validity and formal homogeneity are the only acceptance claims in this file.
GRR/Chern-class identification, geometric product, constant-map GW and CohFT laws
remain unproved. No relation quotient or geometric realization is asserted.
-/

@[expose] public section

-- Long finite vectors require a larger local elaboration recursion bound.
-- Serial theorem elaboration bounds memory; these options change no data or claims.
set_option maxRecDepth 4000
set_option Elab.async false

namespace AxiomaticGW.AdmcyclesHodgeStrataCandidates

/-- Raw incidence and vertex genera for explicit incidence encoding 0. -/
def rawIncidence0Candidate : StableGraphCode.Candidate (Fin 1) 1 0 where
  legVertex := ![0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence0Valid : rawIncidence0Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 1. -/
def rawIncidence1Candidate : StableGraphCode.Candidate (Fin 1) 1 1 where
  legVertex := ![0]
  endpoint := ![![0, 0]]
  genus := ![1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence1Valid : rawIncidence1Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 2. -/
def rawIncidence2Candidate : StableGraphCode.Candidate (Fin 1) 2 1 where
  legVertex := ![0]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence2Valid : rawIncidence2Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 3. -/
def rawIncidence3Candidate : StableGraphCode.Candidate (Fin 1) 2 1 where
  legVertex := ![1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence3Valid : rawIncidence3Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 4. -/
def rawIncidence4Candidate : StableGraphCode.Candidate (Fin 1) 1 2 where
  legVertex := ![0]
  endpoint := ![![0, 0], ![0, 0]]
  genus := ![0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence4Valid : rawIncidence4Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 5. -/
def rawIncidence5Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![1]
  endpoint := ![![1, 0], ![0, 1]]
  genus := ![1, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence5Valid : rawIncidence5Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 6. -/
def rawIncidence6Candidate : StableGraphCode.Candidate (Fin 1) 3 2 where
  legVertex := ![2]
  endpoint := ![![2, 1], ![0, 2]]
  genus := ![1, 1, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence6Valid : rawIncidence6Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 7. -/
def rawIncidence7Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence7Valid : rawIncidence7Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 8. -/
def rawIncidence8Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![1]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence8Valid : rawIncidence8Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 9. -/
def rawIncidence9Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![0, 1]]
  genus := ![0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence9Valid : rawIncidence9Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 10. -/
def rawIncidence10Candidate : StableGraphCode.Candidate (Fin 1) 3 2 where
  legVertex := ![1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence10Valid : rawIncidence10Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 11. -/
def rawIncidence11Candidate : StableGraphCode.Candidate (Fin 1) 3 2 where
  legVertex := ![0]
  endpoint := ![![0, 2], ![0, 1]]
  genus := ![0, 1, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence11Valid : rawIncidence11Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 12. -/
def rawIncidence12Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![1, 0], ![0, 1]]
  genus := ![0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence12Valid : rawIncidence12Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 13. -/
def rawIncidence13Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![1, 1], ![0, 1]]
  genus := ![1, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence13Valid : rawIncidence13Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 14. -/
def rawIncidence14Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![0, 0]]
  genus := ![0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence14Valid : rawIncidence14Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 15. -/
def rawIncidence15Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![1]
  endpoint := ![![0, 1], ![0, 0]]
  genus := ![0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence15Valid : rawIncidence15Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 16. -/
def rawIncidence16Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![1, 1]]
  genus := ![1, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence16Valid : rawIncidence16Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 17. -/
def rawIncidence17Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![1]
  endpoint := ![![0, 1], ![1, 1]]
  genus := ![1, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence17Valid : rawIncidence17Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 18. -/
def rawIncidence18Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![0, 0], ![1, 1], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence18Valid : rawIncidence18Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 19. -/
def rawIncidence19Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![1, 1], ![0, 0], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence19Valid : rawIncidence19Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 20. -/
def rawIncidence20Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![0, 1], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence20Valid : rawIncidence20Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 21. -/
def rawIncidence21Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![1, 0], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence21Valid : rawIncidence21Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 22. -/
def rawIncidence22Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![1, 1], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence22Valid : rawIncidence22Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 23. -/
def rawIncidence23Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![1, 0], ![0, 1], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence23Valid : rawIncidence23Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 24. -/
def rawIncidence24Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![1, 0], ![1, 0], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence24Valid : rawIncidence24Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 25. -/
def rawIncidence25Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![1, 0], ![1, 1], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence25Valid : rawIncidence25Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 26. -/
def rawIncidence26Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![1, 1], ![0, 1], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence26Valid : rawIncidence26Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 27. -/
def rawIncidence27Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![1, 1], ![1, 0], ![0, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence27Valid : rawIncidence27Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 28. -/
def rawIncidence28Candidate : StableGraphCode.Candidate (Fin 1) 3 3 where
  legVertex := ![2]
  endpoint := ![![2, 0], ![0, 2], ![0, 1]]
  genus := ![0, 1, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence28Valid : rawIncidence28Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 29. -/
def rawIncidence29Candidate : StableGraphCode.Candidate (Fin 1) 3 3 where
  legVertex := ![1]
  endpoint := ![![0, 0], ![0, 1], ![1, 2]]
  genus := ![0, 0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence29Valid : rawIncidence29Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 30. -/
def rawIncidence30Candidate : StableGraphCode.Candidate (Fin 1) 3 3 where
  legVertex := ![1]
  endpoint := ![![0, 0], ![1, 2], ![1, 0]]
  genus := ![0, 0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence30Valid : rawIncidence30Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 31. -/
def rawIncidence31Candidate : StableGraphCode.Candidate (Fin 1) 3 3 where
  legVertex := ![1]
  endpoint := ![![0, 1], ![0, 2], ![1, 0]]
  genus := ![0, 0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence31Valid : rawIncidence31Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 32. -/
def rawIncidence32Candidate : StableGraphCode.Candidate (Fin 1) 3 3 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![1, 2], ![0, 1]]
  genus := ![0, 0, 1]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence32Valid : rawIncidence32Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 33. -/
def rawIncidence33Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![1]
  endpoint := ![![1, 0], ![0, 1], ![0, 0]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence33Valid : rawIncidence33Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 34. -/
def rawIncidence34Candidate : StableGraphCode.Candidate (Fin 1) 3 3 where
  legVertex := ![2]
  endpoint := ![![2, 1], ![0, 2], ![0, 0]]
  genus := ![0, 1, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence34Valid : rawIncidence34Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 35. -/
def rawIncidence35Candidate : StableGraphCode.Candidate (Fin 1) 3 3 where
  legVertex := ![2]
  endpoint := ![![2, 1], ![0, 2], ![1, 1]]
  genus := ![1, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence35Valid : rawIncidence35Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 36. -/
def rawIncidence36Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![0]
  endpoint := ![![0, 0], ![0, 1], ![1, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence36Valid : rawIncidence36Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 37. -/
def rawIncidence37Candidate : StableGraphCode.Candidate (Fin 1) 2 3 where
  legVertex := ![1]
  endpoint := ![![0, 0], ![0, 1], ![1, 1]]
  genus := ![0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence37Valid : rawIncidence37Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 38. -/
def rawIncidence38Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![2]
  endpoint := ![![2, 1], ![0, 2], ![0, 0], ![1, 1]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence38Valid : rawIncidence38Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 39. -/
def rawIncidence39Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![1, 2], ![2, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence39Valid : rawIncidence39Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 40. -/
def rawIncidence40Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![2, 1], ![2, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence40Valid : rawIncidence40Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 41. -/
def rawIncidence41Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![2, 2], ![0, 1], ![1, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence41Valid : rawIncidence41Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 42. -/
def rawIncidence42Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![1, 0], ![1, 2], ![2, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence42Valid : rawIncidence42Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 43. -/
def rawIncidence43Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![1, 0], ![2, 1], ![2, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence43Valid : rawIncidence43Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 44. -/
def rawIncidence44Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![1, 0], ![2, 2], ![0, 1], ![1, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence44Valid : rawIncidence44Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 45. -/
def rawIncidence45Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![1, 2], ![0, 1], ![2, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence45Valid : rawIncidence45Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 46. -/
def rawIncidence46Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![1, 2], ![1, 2], ![0, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence46Valid : rawIncidence46Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 47. -/
def rawIncidence47Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![2, 1], ![0, 1], ![2, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence47Valid : rawIncidence47Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 48. -/
def rawIncidence48Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![2, 1], ![1, 0], ![2, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence48Valid : rawIncidence48Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 49. -/
def rawIncidence49Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![2, 1], ![1, 2], ![0, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence49Valid : rawIncidence49Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 50. -/
def rawIncidence50Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![2, 1], ![2, 0], ![0, 1], ![2, 1]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence50Valid : rawIncidence50Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 51. -/
def rawIncidence51Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![2, 2], ![0, 1], ![0, 1], ![1, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence51Valid : rawIncidence51Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 52. -/
def rawIncidence52Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![2, 2], ![1, 0], ![0, 1], ![1, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence52Valid : rawIncidence52Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 53. -/
def rawIncidence53Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![2, 2], ![1, 1], ![0, 1], ![0, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence53Valid : rawIncidence53Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 54. -/
def rawIncidence54Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![2]
  endpoint := ![![2, 0], ![0, 2], ![0, 1], ![1, 1]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence54Valid : rawIncidence54Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 55. -/
def rawIncidence55Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![2]
  endpoint := ![![2, 0], ![1, 2], ![1, 0], ![1, 0]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence55Valid : rawIncidence55Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 56. -/
def rawIncidence56Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![1]
  endpoint := ![![0, 0], ![0, 1], ![1, 2], ![2, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence56Valid : rawIncidence56Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 57. -/
def rawIncidence57Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![2]
  endpoint := ![![0, 0], ![0, 1], ![2, 1], ![2, 1]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence57Valid : rawIncidence57Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 58. -/
def rawIncidence58Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![1]
  endpoint := ![![0, 0], ![1, 2], ![1, 0], ![2, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence58Valid : rawIncidence58Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 59. -/
def rawIncidence59Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![1]
  endpoint := ![![0, 1], ![0, 2], ![1, 0], ![2, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence59Valid : rawIncidence59Candidate.Valid 2 := by decide +kernel

/-- Raw incidence and vertex genera for explicit incidence encoding 60. -/
def rawIncidence60Candidate : StableGraphCode.Candidate (Fin 1) 3 4 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![1, 2], ![0, 1], ![2, 2]]
  genus := ![0, 0, 0]

/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/
theorem rawIncidence60Valid : rawIncidence60Candidate.Valid 2 := by decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph0Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph0 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph0Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph0Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph0Codimension : rawGraph0.codimension = 0 := by
  rw [rawGraph0, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph1Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph1 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph1Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph1Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph1Codimension : rawGraph1.codimension = 1 := by
  rw [rawGraph1, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph2Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph2 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph2Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph2Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph2Codimension : rawGraph2.codimension = 1 := by
  rw [rawGraph2, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph3Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph3 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph3Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph3Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph3Codimension : rawGraph3.codimension = 1 := by
  rw [rawGraph3, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph4Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph4 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph4Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph4Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph4Codimension : rawGraph4.codimension = 1 := by
  rw [rawGraph4, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph5Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph5 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph5Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph5Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph5Codimension : rawGraph5.codimension = 1 := by
  rw [rawGraph5, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph6Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph6 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph6Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph6Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph6Codimension : rawGraph6.codimension = 2 := by
  rw [rawGraph6, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph7Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph7 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph7Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph7Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph7Codimension : rawGraph7.codimension = 2 := by
  rw [rawGraph7, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph8Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph8 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph8Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph8Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph8Codimension : rawGraph8.codimension = 2 := by
  rw [rawGraph8, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph9Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph9 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph9Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph9Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph9Codimension : rawGraph9.codimension = 2 := by
  rw [rawGraph9, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph10Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph10 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph10Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph10Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph10Codimension : rawGraph10.codimension = 2 := by
  rw [rawGraph10, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph11Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph11 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph11Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph11Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph11Codimension : rawGraph11.codimension = 2 := by
  rw [rawGraph11, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph12Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph12 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph12Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph12Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph12Codimension : rawGraph12.codimension = 2 := by
  rw [rawGraph12, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph13Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph13 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph13Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph13Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph13Codimension : rawGraph13.codimension = 2 := by
  rw [rawGraph13, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph14Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph14 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph14Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph14Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph14Codimension : rawGraph14.codimension = 2 := by
  rw [rawGraph14, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph15Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph15 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph15Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph15Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph15Codimension : rawGraph15.codimension = 2 := by
  rw [rawGraph15, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph16Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph16 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence6Candidate rawIncidence6Valid rawGraph16Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph16Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph16Codimension : rawGraph16.codimension = 2 := by
  rw [rawGraph16, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph17Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph17 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph17Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph17Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph17Codimension : rawGraph17.codimension = 2 := by
  rw [rawGraph17, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph18Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph18 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph18Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph18Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph18Codimension : rawGraph18.codimension = 2 := by
  rw [rawGraph18, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph19Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph19 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph19Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph19Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph19Codimension : rawGraph19.codimension = 2 := by
  rw [rawGraph19, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph20Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph20 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph20Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph20Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph20Codimension : rawGraph20.codimension = 2 := by
  rw [rawGraph20, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph21Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph21 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph21Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph21Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph21Codimension : rawGraph21.codimension = 2 := by
  rw [rawGraph21, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph22Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph22 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph22Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph22Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph22Codimension : rawGraph22.codimension = 2 := by
  rw [rawGraph22, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph23Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph23 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph23Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph23Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph23Codimension : rawGraph23.codimension = 2 := by
  rw [rawGraph23, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph24Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph24 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph24Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph24Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph24Codimension : rawGraph24.codimension = 2 := by
  rw [rawGraph24, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph25Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph25 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph25Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph25Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph25Codimension : rawGraph25.codimension = 2 := by
  rw [rawGraph25, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph26Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph26 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph26Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph26Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph26Codimension : rawGraph26.codimension = 2 := by
  rw [rawGraph26, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph27Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph27 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph27Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph27Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph27Codimension : rawGraph27.codimension = 2 := by
  rw [rawGraph27, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph28Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph28 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence9Candidate rawIncidence9Valid rawGraph28Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph28Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph28Codimension : rawGraph28.codimension = 2 := by
  rw [rawGraph28, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph29Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph29 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence10Candidate rawIncidence10Valid rawGraph29Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph29Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph29Codimension : rawGraph29.codimension = 2 := by
  rw [rawGraph29, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph30Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph30 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence11Candidate rawIncidence11Valid rawGraph30Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence11Candidate rawIncidence11Valid rawGraph30Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph30Codimension : rawGraph30.codimension = 2 := by
  rw [rawGraph30, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph31Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph31 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence12Candidate rawIncidence12Valid rawGraph31Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph31Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph31Codimension : rawGraph31.codimension = 2 := by
  rw [rawGraph31, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph32Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph32 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence13Candidate rawIncidence13Valid rawGraph32Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph32Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph32Codimension : rawGraph32.codimension = 2 := by
  rw [rawGraph32, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph33Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph33 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence14Candidate rawIncidence14Valid rawGraph33Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph33Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph33Codimension : rawGraph33.codimension = 2 := by
  rw [rawGraph33, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph34Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph34 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence15Candidate rawIncidence15Valid rawGraph34Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence15Candidate rawIncidence15Valid rawGraph34Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph34Codimension : rawGraph34.codimension = 2 := by
  rw [rawGraph34, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph35Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph35 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence16Candidate rawIncidence16Valid rawGraph35Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph35Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph35Codimension : rawGraph35.codimension = 2 := by
  rw [rawGraph35, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph36Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph36 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph36Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph36Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph36Codimension : rawGraph36.codimension = 2 := by
  rw [rawGraph36, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph37Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph37 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph37Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph37Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph37Codimension : rawGraph37.codimension = 3 := by
  rw [rawGraph37, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph38Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph38 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph38Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph38Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph38Codimension : rawGraph38.codimension = 3 := by
  rw [rawGraph38, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph39Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph39 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph39Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph39Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph39Codimension : rawGraph39.codimension = 3 := by
  rw [rawGraph39, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph40Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph40 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph40Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph40Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph40Codimension : rawGraph40.codimension = 3 := by
  rw [rawGraph40, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph41Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph41 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph41Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph41Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph41Codimension : rawGraph41.codimension = 3 := by
  rw [rawGraph41, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph42Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph42 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph42Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph42Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph42Codimension : rawGraph42.codimension = 3 := by
  rw [rawGraph42, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph43Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph43 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph43Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph43Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph43Codimension : rawGraph43.codimension = 3 := by
  rw [rawGraph43, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph44Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph44 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph44Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph44Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph44Codimension : rawGraph44.codimension = 3 := by
  rw [rawGraph44, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph45Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph45 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph45Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph45Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph45Codimension : rawGraph45.codimension = 3 := by
  rw [rawGraph45, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph46Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph46 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph46Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph46Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph46Codimension : rawGraph46.codimension = 3 := by
  rw [rawGraph46, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph47Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph47 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph47Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph47Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph47Codimension : rawGraph47.codimension = 3 := by
  rw [rawGraph47, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph48Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph48 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph48Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph48Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph48Codimension : rawGraph48.codimension = 3 := by
  rw [rawGraph48, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph49Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph49 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph49Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph49Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph49Codimension : rawGraph49.codimension = 3 := by
  rw [rawGraph49, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph50Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph50 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph50Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph50Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph50Codimension : rawGraph50.codimension = 3 := by
  rw [rawGraph50, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph51Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph51 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph51Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph51Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph51Codimension : rawGraph51.codimension = 3 := by
  rw [rawGraph51, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph52Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph52 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph52Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph52Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph52Codimension : rawGraph52.codimension = 3 := by
  rw [rawGraph52, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph53Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph53 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence13Candidate rawIncidence13Valid rawGraph53Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph53Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph53Codimension : rawGraph53.codimension = 3 := by
  rw [rawGraph53, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph54Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph54 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence6Candidate rawIncidence6Valid rawGraph54Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph54Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph54Codimension : rawGraph54.codimension = 3 := by
  rw [rawGraph54, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph55Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph55 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence6Candidate rawIncidence6Valid rawGraph55Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph55Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph55Codimension : rawGraph55.codimension = 3 := by
  rw [rawGraph55, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph56Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph56 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph56Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph56Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph56Codimension : rawGraph56.codimension = 3 := by
  rw [rawGraph56, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph57Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph57 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph57Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph57Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph57Codimension : rawGraph57.codimension = 3 := by
  rw [rawGraph57, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph58Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph58 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph58Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph58Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph58Codimension : rawGraph58.codimension = 3 := by
  rw [rawGraph58, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph59Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph59 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph59Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph59Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph59Codimension : rawGraph59.codimension = 3 := by
  rw [rawGraph59, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph60Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph60 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph60Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph60Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph60Codimension : rawGraph60.codimension = 3 := by
  rw [rawGraph60, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph61Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph61 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph61Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph61Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph61Codimension : rawGraph61.codimension = 3 := by
  rw [rawGraph61, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph62Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph62 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph62Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph62Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph62Codimension : rawGraph62.codimension = 3 := by
  rw [rawGraph62, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph63Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph63 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph63Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph63Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph63Codimension : rawGraph63.codimension = 3 := by
  rw [rawGraph63, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph64Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph64 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph64Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph64Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph64Codimension : rawGraph64.codimension = 3 := by
  rw [rawGraph64, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph65Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph65 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph65Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph65Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph65Codimension : rawGraph65.codimension = 3 := by
  rw [rawGraph65, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph66Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph66 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph66Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph66Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph66Codimension : rawGraph66.codimension = 3 := by
  rw [rawGraph66, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph67Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![3]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph67 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph67Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph67Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph67Codimension : rawGraph67.codimension = 3 := by
  rw [rawGraph67, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph68Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph68 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence14Candidate rawIncidence14Valid rawGraph68Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph68Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph68Codimension : rawGraph68.codimension = 3 := by
  rw [rawGraph68, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph69Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph69 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence15Candidate rawIncidence15Valid rawGraph69Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence15Candidate rawIncidence15Valid rawGraph69Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph69Codimension : rawGraph69.codimension = 3 := by
  rw [rawGraph69, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph70Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph70 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence14Candidate rawIncidence14Valid rawGraph70Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph70Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph70Codimension : rawGraph70.codimension = 3 := by
  rw [rawGraph70, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph71Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph71 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence9Candidate rawIncidence9Valid rawGraph71Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph71Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph71Codimension : rawGraph71.codimension = 3 := by
  rw [rawGraph71, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph72Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph72 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence16Candidate rawIncidence16Valid rawGraph72Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph72Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph72Codimension : rawGraph72.codimension = 3 := by
  rw [rawGraph72, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph73Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph73 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph73Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph73Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph73Codimension : rawGraph73.codimension = 3 := by
  rw [rawGraph73, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph74Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph74 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph74Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph74Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph74Codimension : rawGraph74.codimension = 3 := by
  rw [rawGraph74, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph75Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph75 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence10Candidate rawIncidence10Valid rawGraph75Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph75Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph75Codimension : rawGraph75.codimension = 3 := by
  rw [rawGraph75, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph76Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph76 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence11Candidate rawIncidence11Valid rawGraph76Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence11Candidate rawIncidence11Valid rawGraph76Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph76Codimension : rawGraph76.codimension = 3 := by
  rw [rawGraph76, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph77Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph77 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence12Candidate rawIncidence12Valid rawGraph77Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph77Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph77Codimension : rawGraph77.codimension = 3 := by
  rw [rawGraph77, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph78Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph78 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence13Candidate rawIncidence13Valid rawGraph78Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph78Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph78Codimension : rawGraph78.codimension = 3 := by
  rw [rawGraph78, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph79Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph79 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph79Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph79Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph79Codimension : rawGraph79.codimension = 3 := by
  rw [rawGraph79, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph80Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph80 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph80Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph80Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph80Codimension : rawGraph80.codimension = 3 := by
  rw [rawGraph80, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph81Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph81 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph81Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph81Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph81Codimension : rawGraph81.codimension = 3 := by
  rw [rawGraph81, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph82Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph82 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph82Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph82Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph82Codimension : rawGraph82.codimension = 3 := by
  rw [rawGraph82, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph83Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph83 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence18Candidate rawIncidence18Valid rawGraph83Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph83Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph83Codimension : rawGraph83.codimension = 3 := by
  rw [rawGraph83, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph84Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph84 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence19Candidate rawIncidence19Valid rawGraph84Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence19Candidate rawIncidence19Valid rawGraph84Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph84Codimension : rawGraph84.codimension = 3 := by
  rw [rawGraph84, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph85Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph85 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph85Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph85Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph85Codimension : rawGraph85.codimension = 3 := by
  rw [rawGraph85, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph86Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph86 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph86Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph86Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph86Codimension : rawGraph86.codimension = 3 := by
  rw [rawGraph86, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph87Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph87 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph87Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph87Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph87Codimension : rawGraph87.codimension = 3 := by
  rw [rawGraph87, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph88Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph88 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph88Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph88Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph88Codimension : rawGraph88.codimension = 3 := by
  rw [rawGraph88, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph89Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph89 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph89Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph89Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph89Codimension : rawGraph89.codimension = 3 := by
  rw [rawGraph89, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph90Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph90 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph90Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph90Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph90Codimension : rawGraph90.codimension = 3 := by
  rw [rawGraph90, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph91Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph91 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence20Candidate rawIncidence20Valid rawGraph91Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph91Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph91Codimension : rawGraph91.codimension = 3 := by
  rw [rawGraph91, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph92Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph92 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence21Candidate rawIncidence21Valid rawGraph92Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence21Candidate rawIncidence21Valid rawGraph92Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph92Codimension : rawGraph92.codimension = 3 := by
  rw [rawGraph92, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph93Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph93 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence22Candidate rawIncidence22Valid rawGraph93Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph93Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph93Codimension : rawGraph93.codimension = 3 := by
  rw [rawGraph93, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph94Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph94 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence23Candidate rawIncidence23Valid rawGraph94Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence23Candidate rawIncidence23Valid rawGraph94Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph94Codimension : rawGraph94.codimension = 3 := by
  rw [rawGraph94, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph95Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph95 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence24Candidate rawIncidence24Valid rawGraph95Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence24Candidate rawIncidence24Valid rawGraph95Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph95Codimension : rawGraph95.codimension = 3 := by
  rw [rawGraph95, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph96Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph96 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence25Candidate rawIncidence25Valid rawGraph96Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence25Candidate rawIncidence25Valid rawGraph96Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph96Codimension : rawGraph96.codimension = 3 := by
  rw [rawGraph96, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph97Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph97 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence26Candidate rawIncidence26Valid rawGraph97Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence26Candidate rawIncidence26Valid rawGraph97Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph97Codimension : rawGraph97.codimension = 3 := by
  rw [rawGraph97, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph98Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph98 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence27Candidate rawIncidence27Valid rawGraph98Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence27Candidate rawIncidence27Valid rawGraph98Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph98Codimension : rawGraph98.codimension = 3 := by
  rw [rawGraph98, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph99Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph99 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence28Candidate rawIncidence28Valid rawGraph99Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence28Candidate rawIncidence28Valid rawGraph99Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph99Codimension : rawGraph99.codimension = 3 := by
  rw [rawGraph99, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph100Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph100 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph100Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph100Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph100Codimension : rawGraph100.codimension = 3 := by
  rw [rawGraph100, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph101Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph101 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph101Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph101Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph101Codimension : rawGraph101.codimension = 3 := by
  rw [rawGraph101, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph102Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph102 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence9Candidate rawIncidence9Valid rawGraph102Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph102Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph102Codimension : rawGraph102.codimension = 3 := by
  rw [rawGraph102, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph103Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph103 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence10Candidate rawIncidence10Valid rawGraph103Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph103Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph103Codimension : rawGraph103.codimension = 3 := by
  rw [rawGraph103, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph104Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph104 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence10Candidate rawIncidence10Valid rawGraph104Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph104Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph104Codimension : rawGraph104.codimension = 3 := by
  rw [rawGraph104, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph105Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph105 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence11Candidate rawIncidence11Valid rawGraph105Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence11Candidate rawIncidence11Valid rawGraph105Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph105Codimension : rawGraph105.codimension = 3 := by
  rw [rawGraph105, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph106Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph106 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence11Candidate rawIncidence11Valid rawGraph106Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence11Candidate rawIncidence11Valid rawGraph106Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph106Codimension : rawGraph106.codimension = 3 := by
  rw [rawGraph106, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph107Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph107 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence12Candidate rawIncidence12Valid rawGraph107Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph107Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph107Codimension : rawGraph107.codimension = 3 := by
  rw [rawGraph107, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph108Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph108 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph108Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph108Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph108Codimension : rawGraph108.codimension = 3 := by
  rw [rawGraph108, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph109Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph109 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence13Candidate rawIncidence13Valid rawGraph109Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph109Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph109Codimension : rawGraph109.codimension = 3 := by
  rw [rawGraph109, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph110Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph110 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence6Candidate rawIncidence6Valid rawGraph110Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph110Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph110Codimension : rawGraph110.codimension = 3 := by
  rw [rawGraph110, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph111Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph111 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence6Candidate rawIncidence6Valid rawGraph111Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph111Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph111Codimension : rawGraph111.codimension = 3 := by
  rw [rawGraph111, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph112Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph112 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph112Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph112Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph112Codimension : rawGraph112.codimension = 3 := by
  rw [rawGraph112, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph113Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph113 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph113Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph113Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph113Codimension : rawGraph113.codimension = 3 := by
  rw [rawGraph113, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph114Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph114 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph114Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph114Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph114Codimension : rawGraph114.codimension = 3 := by
  rw [rawGraph114, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph115Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph115 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph115Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph115Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph115Codimension : rawGraph115.codimension = 3 := by
  rw [rawGraph115, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph116Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph116 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph116Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph116Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph116Codimension : rawGraph116.codimension = 3 := by
  rw [rawGraph116, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph117Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph117 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph117Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph117Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph117Codimension : rawGraph117.codimension = 3 := by
  rw [rawGraph117, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph118Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph118 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence29Candidate rawIncidence29Valid rawGraph118Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence29Candidate rawIncidence29Valid rawGraph118Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph118Codimension : rawGraph118.codimension = 3 := by
  rw [rawGraph118, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph119Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph119 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence30Candidate rawIncidence30Valid rawGraph119Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence30Candidate rawIncidence30Valid rawGraph119Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph119Codimension : rawGraph119.codimension = 3 := by
  rw [rawGraph119, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph120Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph120 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence31Candidate rawIncidence31Valid rawGraph120Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence31Candidate rawIncidence31Valid rawGraph120Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph120Codimension : rawGraph120.codimension = 3 := by
  rw [rawGraph120, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph121Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph121 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence32Candidate rawIncidence32Valid rawGraph121Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence32Candidate rawIncidence32Valid rawGraph121Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph121Codimension : rawGraph121.codimension = 3 := by
  rw [rawGraph121, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph122Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph122 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph122Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph122Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph122Codimension : rawGraph122.codimension = 3 := by
  rw [rawGraph122, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph123Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![3, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph123 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph123Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph123Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph123Codimension : rawGraph123.codimension = 3 := by
  rw [rawGraph123, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph124Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph124 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence33Candidate rawIncidence33Valid rawGraph124Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence33Candidate rawIncidence33Valid rawGraph124Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph124Codimension : rawGraph124.codimension = 3 := by
  rw [rawGraph124, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph125Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph125 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence34Candidate rawIncidence34Valid rawGraph125Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence34Candidate rawIncidence34Valid rawGraph125Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph125Codimension : rawGraph125.codimension = 3 := by
  rw [rawGraph125, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph126Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph126 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence35Candidate rawIncidence35Valid rawGraph126Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence35Candidate rawIncidence35Valid rawGraph126Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph126Codimension : rawGraph126.codimension = 3 := by
  rw [rawGraph126, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph127Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph127 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence14Candidate rawIncidence14Valid rawGraph127Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph127Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph127Codimension : rawGraph127.codimension = 3 := by
  rw [rawGraph127, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph128Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph128 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence15Candidate rawIncidence15Valid rawGraph128Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence15Candidate rawIncidence15Valid rawGraph128Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph128Codimension : rawGraph128.codimension = 3 := by
  rw [rawGraph128, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph129Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph129 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence14Candidate rawIncidence14Valid rawGraph129Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph129Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph129Codimension : rawGraph129.codimension = 3 := by
  rw [rawGraph129, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph130Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph130 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph130Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph130Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph130Codimension : rawGraph130.codimension = 3 := by
  rw [rawGraph130, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph131Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph131 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence16Candidate rawIncidence16Valid rawGraph131Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph131Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph131Codimension : rawGraph131.codimension = 3 := by
  rw [rawGraph131, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph132Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph132 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph132Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph132Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph132Codimension : rawGraph132.codimension = 3 := by
  rw [rawGraph132, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph133Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 2]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph133 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph133Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph133Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph133Codimension : rawGraph133.codimension = 3 := by
  rw [rawGraph133, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph134Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![2, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph134 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph134Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph134Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph134Codimension : rawGraph134.codimension = 3 := by
  rw [rawGraph134, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph135Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph135 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph135Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph135Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph135Codimension : rawGraph135.codimension = 3 := by
  rw [rawGraph135, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph136Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![2, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph136 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph136Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph136Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph136Codimension : rawGraph136.codimension = 3 := by
  rw [rawGraph136, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph137Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 2]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph137 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph137Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph137Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph137Codimension : rawGraph137.codimension = 3 := by
  rw [rawGraph137, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph138Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![2, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph138 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph138Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph138Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph138Codimension : rawGraph138.codimension = 3 := by
  rw [rawGraph138, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph139Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph139 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence36Candidate rawIncidence36Valid rawGraph139Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence36Candidate rawIncidence36Valid rawGraph139Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph139Codimension : rawGraph139.codimension = 3 := by
  rw [rawGraph139, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph140Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph140 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence37Candidate rawIncidence37Valid rawGraph140Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence37Candidate rawIncidence37Valid rawGraph140Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph140Codimension : rawGraph140.codimension = 3 := by
  rw [rawGraph140, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph141Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph141 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph141Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph141Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph141Codimension : rawGraph141.codimension = 3 := by
  rw [rawGraph141, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph142Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph142 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph142Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph142Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph142Codimension : rawGraph142.codimension = 3 := by
  rw [rawGraph142, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph143Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph143 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence10Candidate rawIncidence10Valid rawGraph143Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph143Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph143Codimension : rawGraph143.codimension = 3 := by
  rw [rawGraph143, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph144Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph144 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence12Candidate rawIncidence12Valid rawGraph144Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph144Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph144Codimension : rawGraph144.codimension = 3 := by
  rw [rawGraph144, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph145Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph145 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence14Candidate rawIncidence14Valid rawGraph145Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph145Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph145Codimension : rawGraph145.codimension = 3 := by
  rw [rawGraph145, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph146Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph146 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence16Candidate rawIncidence16Valid rawGraph146Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph146Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph146Codimension : rawGraph146.codimension = 3 := by
  rw [rawGraph146, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph147Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph147 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph147Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph147Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph147Codimension : rawGraph147.codimension = 3 := by
  rw [rawGraph147, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph148Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph148 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph148Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph148Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph148Codimension : rawGraph148.codimension = 4 := by
  rw [rawGraph148, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph149Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph149 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph149Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph149Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph149Codimension : rawGraph149.codimension = 4 := by
  rw [rawGraph149, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph150Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph150 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph150Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph150Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph150Codimension : rawGraph150.codimension = 4 := by
  rw [rawGraph150, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph151Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph151 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph151Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph151Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph151Codimension : rawGraph151.codimension = 4 := by
  rw [rawGraph151, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph152Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph152 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence18Candidate rawIncidence18Valid rawGraph152Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph152Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph152Codimension : rawGraph152.codimension = 4 := by
  rw [rawGraph152, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph153Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph153 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence18Candidate rawIncidence18Valid rawGraph153Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph153Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph153Codimension : rawGraph153.codimension = 4 := by
  rw [rawGraph153, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph154Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph154 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence18Candidate rawIncidence18Valid rawGraph154Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph154Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph154Codimension : rawGraph154.codimension = 4 := by
  rw [rawGraph154, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph155Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph155 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence20Candidate rawIncidence20Valid rawGraph155Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph155Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph155Codimension : rawGraph155.codimension = 4 := by
  rw [rawGraph155, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph156Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph156 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence20Candidate rawIncidence20Valid rawGraph156Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph156Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph156Codimension : rawGraph156.codimension = 4 := by
  rw [rawGraph156, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph157Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph157 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence20Candidate rawIncidence20Valid rawGraph157Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph157Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph157Codimension : rawGraph157.codimension = 4 := by
  rw [rawGraph157, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph158Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph158 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence20Candidate rawIncidence20Valid rawGraph158Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph158Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph158Codimension : rawGraph158.codimension = 4 := by
  rw [rawGraph158, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph159Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph159 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence21Candidate rawIncidence21Valid rawGraph159Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence21Candidate rawIncidence21Valid rawGraph159Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph159Codimension : rawGraph159.codimension = 4 := by
  rw [rawGraph159, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph160Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph160 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence21Candidate rawIncidence21Valid rawGraph160Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence21Candidate rawIncidence21Valid rawGraph160Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph160Codimension : rawGraph160.codimension = 4 := by
  rw [rawGraph160, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph161Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph161 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence21Candidate rawIncidence21Valid rawGraph161Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence21Candidate rawIncidence21Valid rawGraph161Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph161Codimension : rawGraph161.codimension = 4 := by
  rw [rawGraph161, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph162Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph162 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence21Candidate rawIncidence21Valid rawGraph162Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence21Candidate rawIncidence21Valid rawGraph162Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph162Codimension : rawGraph162.codimension = 4 := by
  rw [rawGraph162, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph163Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph163 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence22Candidate rawIncidence22Valid rawGraph163Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph163Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph163Codimension : rawGraph163.codimension = 4 := by
  rw [rawGraph163, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph164Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph164 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence22Candidate rawIncidence22Valid rawGraph164Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph164Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph164Codimension : rawGraph164.codimension = 4 := by
  rw [rawGraph164, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph165Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph165 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence22Candidate rawIncidence22Valid rawGraph165Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph165Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph165Codimension : rawGraph165.codimension = 4 := by
  rw [rawGraph165, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph166Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph166 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence22Candidate rawIncidence22Valid rawGraph166Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph166Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph166Codimension : rawGraph166.codimension = 4 := by
  rw [rawGraph166, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph167Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph167 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence23Candidate rawIncidence23Valid rawGraph167Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence23Candidate rawIncidence23Valid rawGraph167Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph167Codimension : rawGraph167.codimension = 4 := by
  rw [rawGraph167, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph168Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph168 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence23Candidate rawIncidence23Valid rawGraph168Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence23Candidate rawIncidence23Valid rawGraph168Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph168Codimension : rawGraph168.codimension = 4 := by
  rw [rawGraph168, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph169Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph169 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence23Candidate rawIncidence23Valid rawGraph169Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence23Candidate rawIncidence23Valid rawGraph169Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph169Codimension : rawGraph169.codimension = 4 := by
  rw [rawGraph169, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph170Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph170 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence23Candidate rawIncidence23Valid rawGraph170Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence23Candidate rawIncidence23Valid rawGraph170Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph170Codimension : rawGraph170.codimension = 4 := by
  rw [rawGraph170, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph171Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph171 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence24Candidate rawIncidence24Valid rawGraph171Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence24Candidate rawIncidence24Valid rawGraph171Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph171Codimension : rawGraph171.codimension = 4 := by
  rw [rawGraph171, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph172Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph172 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence24Candidate rawIncidence24Valid rawGraph172Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence24Candidate rawIncidence24Valid rawGraph172Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph172Codimension : rawGraph172.codimension = 4 := by
  rw [rawGraph172, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph173Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph173 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence24Candidate rawIncidence24Valid rawGraph173Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence24Candidate rawIncidence24Valid rawGraph173Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph173Codimension : rawGraph173.codimension = 4 := by
  rw [rawGraph173, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph174Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph174 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence24Candidate rawIncidence24Valid rawGraph174Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence24Candidate rawIncidence24Valid rawGraph174Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph174Codimension : rawGraph174.codimension = 4 := by
  rw [rawGraph174, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph175Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph175 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence25Candidate rawIncidence25Valid rawGraph175Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence25Candidate rawIncidence25Valid rawGraph175Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph175Codimension : rawGraph175.codimension = 4 := by
  rw [rawGraph175, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph176Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph176 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence25Candidate rawIncidence25Valid rawGraph176Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence25Candidate rawIncidence25Valid rawGraph176Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph176Codimension : rawGraph176.codimension = 4 := by
  rw [rawGraph176, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph177Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph177 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence25Candidate rawIncidence25Valid rawGraph177Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence25Candidate rawIncidence25Valid rawGraph177Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph177Codimension : rawGraph177.codimension = 4 := by
  rw [rawGraph177, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph178Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph178 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence25Candidate rawIncidence25Valid rawGraph178Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence25Candidate rawIncidence25Valid rawGraph178Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph178Codimension : rawGraph178.codimension = 4 := by
  rw [rawGraph178, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph179Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph179 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence19Candidate rawIncidence19Valid rawGraph179Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence19Candidate rawIncidence19Valid rawGraph179Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph179Codimension : rawGraph179.codimension = 4 := by
  rw [rawGraph179, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph180Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph180 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence19Candidate rawIncidence19Valid rawGraph180Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence19Candidate rawIncidence19Valid rawGraph180Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph180Codimension : rawGraph180.codimension = 4 := by
  rw [rawGraph180, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph181Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph181 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence19Candidate rawIncidence19Valid rawGraph181Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence19Candidate rawIncidence19Valid rawGraph181Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph181Codimension : rawGraph181.codimension = 4 := by
  rw [rawGraph181, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph182Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph182 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence26Candidate rawIncidence26Valid rawGraph182Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence26Candidate rawIncidence26Valid rawGraph182Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph182Codimension : rawGraph182.codimension = 4 := by
  rw [rawGraph182, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph183Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph183 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence26Candidate rawIncidence26Valid rawGraph183Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence26Candidate rawIncidence26Valid rawGraph183Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph183Codimension : rawGraph183.codimension = 4 := by
  rw [rawGraph183, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph184Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph184 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence26Candidate rawIncidence26Valid rawGraph184Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence26Candidate rawIncidence26Valid rawGraph184Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph184Codimension : rawGraph184.codimension = 4 := by
  rw [rawGraph184, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph185Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph185 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence26Candidate rawIncidence26Valid rawGraph185Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence26Candidate rawIncidence26Valid rawGraph185Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph185Codimension : rawGraph185.codimension = 4 := by
  rw [rawGraph185, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph186Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph186 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence27Candidate rawIncidence27Valid rawGraph186Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence27Candidate rawIncidence27Valid rawGraph186Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph186Codimension : rawGraph186.codimension = 4 := by
  rw [rawGraph186, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph187Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph187 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence27Candidate rawIncidence27Valid rawGraph187Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence27Candidate rawIncidence27Valid rawGraph187Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph187Codimension : rawGraph187.codimension = 4 := by
  rw [rawGraph187, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph188Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph188 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence27Candidate rawIncidence27Valid rawGraph188Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence27Candidate rawIncidence27Valid rawGraph188Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph188Codimension : rawGraph188.codimension = 4 := by
  rw [rawGraph188, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph189Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph189 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence27Candidate rawIncidence27Valid rawGraph189Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence27Candidate rawIncidence27Valid rawGraph189Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph189Codimension : rawGraph189.codimension = 4 := by
  rw [rawGraph189, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph190Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph190 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph190Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph190Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph190Codimension : rawGraph190.codimension = 4 := by
  rw [rawGraph190, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph191Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph191 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence16Candidate rawIncidence16Valid rawGraph191Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph191Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph191Codimension : rawGraph191.codimension = 4 := by
  rw [rawGraph191, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph192Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph192 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph192Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph192Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph192Codimension : rawGraph192.codimension = 4 := by
  rw [rawGraph192, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph193Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph193 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph193Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph193Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph193Codimension : rawGraph193.codimension = 4 := by
  rw [rawGraph193, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph194Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph194 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence13Candidate rawIncidence13Valid rawGraph194Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph194Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph194Codimension : rawGraph194.codimension = 4 := by
  rw [rawGraph194, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph195Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph195 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence6Candidate rawIncidence6Valid rawGraph195Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph195Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph195Codimension : rawGraph195.codimension = 4 := by
  rw [rawGraph195, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph196Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph196 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence6Candidate rawIncidence6Valid rawGraph196Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph196Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph196Codimension : rawGraph196.codimension = 4 := by
  rw [rawGraph196, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph197Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph197 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph197Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph197Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph197Codimension : rawGraph197.codimension = 4 := by
  rw [rawGraph197, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph198Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph198 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph198Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph198Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph198Codimension : rawGraph198.codimension = 4 := by
  rw [rawGraph198, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph199Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph199 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph199Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph199Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph199Codimension : rawGraph199.codimension = 4 := by
  rw [rawGraph199, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph200Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph200 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph200Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph200Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph200Codimension : rawGraph200.codimension = 4 := by
  rw [rawGraph200, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph201Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph201 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph201Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph201Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph201Codimension : rawGraph201.codimension = 4 := by
  rw [rawGraph201, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph202Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph202 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph202Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph202Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph202Codimension : rawGraph202.codimension = 4 := by
  rw [rawGraph202, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph203Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph203 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph203Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph203Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph203Codimension : rawGraph203.codimension = 4 := by
  rw [rawGraph203, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph204Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph204 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph204Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph204Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph204Codimension : rawGraph204.codimension = 4 := by
  rw [rawGraph204, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph205Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph205 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph205Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph205Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph205Codimension : rawGraph205.codimension = 4 := by
  rw [rawGraph205, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph206Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph206 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph206Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph206Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph206Codimension : rawGraph206.codimension = 4 := by
  rw [rawGraph206, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph207Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph207 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph207Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph207Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph207Codimension : rawGraph207.codimension = 4 := by
  rw [rawGraph207, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph208Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph208 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph208Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph208Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph208Codimension : rawGraph208.codimension = 4 := by
  rw [rawGraph208, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph209Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![3]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph209 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph209Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph209Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph209Codimension : rawGraph209.codimension = 4 := by
  rw [rawGraph209, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph210Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![3, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph210 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph210Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph210Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph210Codimension : rawGraph210.codimension = 4 := by
  rw [rawGraph210, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph211Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![2, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph211 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph211Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph211Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph211Codimension : rawGraph211.codimension = 4 := by
  rw [rawGraph211, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph212Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph212 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence33Candidate rawIncidence33Valid rawGraph212Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence33Candidate rawIncidence33Valid rawGraph212Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph212Codimension : rawGraph212.codimension = 4 := by
  rw [rawGraph212, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph213Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph213 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence28Candidate rawIncidence28Valid rawGraph213Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence28Candidate rawIncidence28Valid rawGraph213Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph213Codimension : rawGraph213.codimension = 4 := by
  rw [rawGraph213, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph214Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph214 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph214Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph214Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph214Codimension : rawGraph214.codimension = 4 := by
  rw [rawGraph214, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph215Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph215 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence14Candidate rawIncidence14Valid rawGraph215Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph215Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph215Codimension : rawGraph215.codimension = 4 := by
  rw [rawGraph215, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph216Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph216 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph216Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph216Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph216Codimension : rawGraph216.codimension = 4 := by
  rw [rawGraph216, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph217Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph217 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph217Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph217Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph217Codimension : rawGraph217.codimension = 4 := by
  rw [rawGraph217, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph218Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph218 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence10Candidate rawIncidence10Valid rawGraph218Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph218Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph218Codimension : rawGraph218.codimension = 4 := by
  rw [rawGraph218, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph219Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph219 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence10Candidate rawIncidence10Valid rawGraph219Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph219Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph219Codimension : rawGraph219.codimension = 4 := by
  rw [rawGraph219, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph220Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph220 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence12Candidate rawIncidence12Valid rawGraph220Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph220Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph220Codimension : rawGraph220.codimension = 4 := by
  rw [rawGraph220, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph221Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![3]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph221 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph221Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph221Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph221Codimension : rawGraph221.codimension = 4 := by
  rw [rawGraph221, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph222Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph222 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph222Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph222Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph222Codimension : rawGraph222.codimension = 4 := by
  rw [rawGraph222, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph223Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph223 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph223Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph223Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph223Codimension : rawGraph223.codimension = 4 := by
  rw [rawGraph223, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph224Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![2, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph224 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph224Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph224Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph224Codimension : rawGraph224.codimension = 4 := by
  rw [rawGraph224, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph225Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph225 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph225Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph225Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph225Codimension : rawGraph225.codimension = 4 := by
  rw [rawGraph225, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph226Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![2, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph226 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph226Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph226Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph226Codimension : rawGraph226.codimension = 4 := by
  rw [rawGraph226, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph227Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph227 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph227Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph227Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph227Codimension : rawGraph227.codimension = 4 := by
  rw [rawGraph227, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph228Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![2, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph228 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph228Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph228Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph228Codimension : rawGraph228.codimension = 4 := by
  rw [rawGraph228, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph229Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph229 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence36Candidate rawIncidence36Valid rawGraph229Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence36Candidate rawIncidence36Valid rawGraph229Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph229Codimension : rawGraph229.codimension = 4 := by
  rw [rawGraph229, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph230Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph230 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence37Candidate rawIncidence37Valid rawGraph230Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence37Candidate rawIncidence37Valid rawGraph230Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph230Codimension : rawGraph230.codimension = 4 := by
  rw [rawGraph230, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph231Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph231 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence37Candidate rawIncidence37Valid rawGraph231Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence37Candidate rawIncidence37Valid rawGraph231Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph231Codimension : rawGraph231.codimension = 4 := by
  rw [rawGraph231, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph232Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph232 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence29Candidate rawIncidence29Valid rawGraph232Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence29Candidate rawIncidence29Valid rawGraph232Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph232Codimension : rawGraph232.codimension = 4 := by
  rw [rawGraph232, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph233Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph233 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence30Candidate rawIncidence30Valid rawGraph233Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence30Candidate rawIncidence30Valid rawGraph233Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph233Codimension : rawGraph233.codimension = 4 := by
  rw [rawGraph233, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph234Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph234 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence31Candidate rawIncidence31Valid rawGraph234Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence31Candidate rawIncidence31Valid rawGraph234Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph234Codimension : rawGraph234.codimension = 4 := by
  rw [rawGraph234, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph235Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph235 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence32Candidate rawIncidence32Valid rawGraph235Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence32Candidate rawIncidence32Valid rawGraph235Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph235Codimension : rawGraph235.codimension = 4 := by
  rw [rawGraph235, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph236Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph236 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph236Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph236Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph236Codimension : rawGraph236.codimension = 4 := by
  rw [rawGraph236, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph237Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph237 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence33Candidate rawIncidence33Valid rawGraph237Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence33Candidate rawIncidence33Valid rawGraph237Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph237Codimension : rawGraph237.codimension = 4 := by
  rw [rawGraph237, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph238Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph238 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence33Candidate rawIncidence33Valid rawGraph238Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence33Candidate rawIncidence33Valid rawGraph238Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph238Codimension : rawGraph238.codimension = 4 := by
  rw [rawGraph238, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph239Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph239 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence34Candidate rawIncidence34Valid rawGraph239Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence34Candidate rawIncidence34Valid rawGraph239Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph239Codimension : rawGraph239.codimension = 4 := by
  rw [rawGraph239, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph240Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph240 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence35Candidate rawIncidence35Valid rawGraph240Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence35Candidate rawIncidence35Valid rawGraph240Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph240Codimension : rawGraph240.codimension = 4 := by
  rw [rawGraph240, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph241Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph241 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph241Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph241Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph241Codimension : rawGraph241.codimension = 4 := by
  rw [rawGraph241, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph242Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph242 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph242Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph242Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph242Codimension : rawGraph242.codimension = 4 := by
  rw [rawGraph242, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph243Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph243 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence14Candidate rawIncidence14Valid rawGraph243Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph243Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph243Codimension : rawGraph243.codimension = 4 := by
  rw [rawGraph243, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph244Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph244 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence9Candidate rawIncidence9Valid rawGraph244Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph244Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph244Codimension : rawGraph244.codimension = 4 := by
  rw [rawGraph244, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph245Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph245 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph245Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph245Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph245Codimension : rawGraph245.codimension = 4 := by
  rw [rawGraph245, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph246Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph246 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence16Candidate rawIncidence16Valid rawGraph246Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph246Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph246Codimension : rawGraph246.codimension = 4 := by
  rw [rawGraph246, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph247Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph247 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence12Candidate rawIncidence12Valid rawGraph247Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph247Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph247Codimension : rawGraph247.codimension = 4 := by
  rw [rawGraph247, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph248Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph248 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence13Candidate rawIncidence13Valid rawGraph248Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph248Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph248Codimension : rawGraph248.codimension = 4 := by
  rw [rawGraph248, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph249Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 2]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph249 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph249Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph249Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph249Codimension : rawGraph249.codimension = 4 := by
  rw [rawGraph249, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph250Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 2]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph250 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph250Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph250Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph250Codimension : rawGraph250.codimension = 4 := by
  rw [rawGraph250, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph251Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![3, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph251 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph251Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph251Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph251Codimension : rawGraph251.codimension = 4 := by
  rw [rawGraph251, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph252Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 2]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph252 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph252Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph252Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph252Codimension : rawGraph252.codimension = 4 := by
  rw [rawGraph252, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph253Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph253 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence37Candidate rawIncidence37Valid rawGraph253Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence37Candidate rawIncidence37Valid rawGraph253Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph253Codimension : rawGraph253.codimension = 4 := by
  rw [rawGraph253, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph254Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph254 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence36Candidate rawIncidence36Valid rawGraph254Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence36Candidate rawIncidence36Valid rawGraph254Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph254Codimension : rawGraph254.codimension = 4 := by
  rw [rawGraph254, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph255Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph255 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence36Candidate rawIncidence36Valid rawGraph255Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence36Candidate rawIncidence36Valid rawGraph255Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph255Codimension : rawGraph255.codimension = 4 := by
  rw [rawGraph255, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph256Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph256 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence36Candidate rawIncidence36Valid rawGraph256Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence36Candidate rawIncidence36Valid rawGraph256Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph256Codimension : rawGraph256.codimension = 4 := by
  rw [rawGraph256, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph257Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph257 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence18Candidate rawIncidence18Valid rawGraph257Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph257Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph257Codimension : rawGraph257.codimension = 4 := by
  rw [rawGraph257, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph258Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph258 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence19Candidate rawIncidence19Valid rawGraph258Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence19Candidate rawIncidence19Valid rawGraph258Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph258Codimension : rawGraph258.codimension = 4 := by
  rw [rawGraph258, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph259Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph259 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph259Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph259Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph259Codimension : rawGraph259.codimension = 4 := by
  rw [rawGraph259, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph260Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph260 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph260Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph260Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph260Codimension : rawGraph260.codimension = 4 := by
  rw [rawGraph260, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph261Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph261 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph261Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph261Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph261Codimension : rawGraph261.codimension = 4 := by
  rw [rawGraph261, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph262Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph262 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph262Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph262Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph262Codimension : rawGraph262.codimension = 4 := by
  rw [rawGraph262, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph263Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph263 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph263Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph263Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph263Codimension : rawGraph263.codimension = 4 := by
  rw [rawGraph263, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph264Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph264 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph264Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph264Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph264Codimension : rawGraph264.codimension = 4 := by
  rw [rawGraph264, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph265Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph265 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph265Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph265Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph265Codimension : rawGraph265.codimension = 4 := by
  rw [rawGraph265, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph266Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph266 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph266Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph266Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph266Codimension : rawGraph266.codimension = 4 := by
  rw [rawGraph266, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph267Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph267 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph267Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph267Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph267Codimension : rawGraph267.codimension = 4 := by
  rw [rawGraph267, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph268Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph268 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph268Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph268Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph268Codimension : rawGraph268.codimension = 4 := by
  rw [rawGraph268, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph269Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph269 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence38Candidate rawIncidence38Valid rawGraph269Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence38Candidate rawIncidence38Valid rawGraph269Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph269Codimension : rawGraph269.codimension = 4 := by
  rw [rawGraph269, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph270Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph270 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence39Candidate rawIncidence39Valid rawGraph270Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence39Candidate rawIncidence39Valid rawGraph270Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph270Codimension : rawGraph270.codimension = 4 := by
  rw [rawGraph270, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph271Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph271 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence40Candidate rawIncidence40Valid rawGraph271Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence40Candidate rawIncidence40Valid rawGraph271Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph271Codimension : rawGraph271.codimension = 4 := by
  rw [rawGraph271, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph272Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph272 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence41Candidate rawIncidence41Valid rawGraph272Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence41Candidate rawIncidence41Valid rawGraph272Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph272Codimension : rawGraph272.codimension = 4 := by
  rw [rawGraph272, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph273Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph273 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence42Candidate rawIncidence42Valid rawGraph273Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence42Candidate rawIncidence42Valid rawGraph273Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph273Codimension : rawGraph273.codimension = 4 := by
  rw [rawGraph273, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph274Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph274 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence43Candidate rawIncidence43Valid rawGraph274Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence43Candidate rawIncidence43Valid rawGraph274Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph274Codimension : rawGraph274.codimension = 4 := by
  rw [rawGraph274, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph275Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph275 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence44Candidate rawIncidence44Valid rawGraph275Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence44Candidate rawIncidence44Valid rawGraph275Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph275Codimension : rawGraph275.codimension = 4 := by
  rw [rawGraph275, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph276Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph276 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence45Candidate rawIncidence45Valid rawGraph276Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence45Candidate rawIncidence45Valid rawGraph276Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph276Codimension : rawGraph276.codimension = 4 := by
  rw [rawGraph276, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph277Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph277 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence46Candidate rawIncidence46Valid rawGraph277Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence46Candidate rawIncidence46Valid rawGraph277Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph277Codimension : rawGraph277.codimension = 4 := by
  rw [rawGraph277, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph278Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph278 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence47Candidate rawIncidence47Valid rawGraph278Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence47Candidate rawIncidence47Valid rawGraph278Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph278Codimension : rawGraph278.codimension = 4 := by
  rw [rawGraph278, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph279Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph279 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence48Candidate rawIncidence48Valid rawGraph279Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence48Candidate rawIncidence48Valid rawGraph279Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph279Codimension : rawGraph279.codimension = 4 := by
  rw [rawGraph279, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph280Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph280 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence49Candidate rawIncidence49Valid rawGraph280Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence49Candidate rawIncidence49Valid rawGraph280Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph280Codimension : rawGraph280.codimension = 4 := by
  rw [rawGraph280, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph281Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph281 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence50Candidate rawIncidence50Valid rawGraph281Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence50Candidate rawIncidence50Valid rawGraph281Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph281Codimension : rawGraph281.codimension = 4 := by
  rw [rawGraph281, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph282Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph282 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence51Candidate rawIncidence51Valid rawGraph282Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence51Candidate rawIncidence51Valid rawGraph282Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph282Codimension : rawGraph282.codimension = 4 := by
  rw [rawGraph282, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph283Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph283 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence52Candidate rawIncidence52Valid rawGraph283Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence52Candidate rawIncidence52Valid rawGraph283Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph283Codimension : rawGraph283.codimension = 4 := by
  rw [rawGraph283, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph284Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph284 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence53Candidate rawIncidence53Valid rawGraph284Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence53Candidate rawIncidence53Valid rawGraph284Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph284Codimension : rawGraph284.codimension = 4 := by
  rw [rawGraph284, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph285Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph285 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence20Candidate rawIncidence20Valid rawGraph285Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph285Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph285Codimension : rawGraph285.codimension = 4 := by
  rw [rawGraph285, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph286Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph286 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence21Candidate rawIncidence21Valid rawGraph286Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence21Candidate rawIncidence21Valid rawGraph286Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph286Codimension : rawGraph286.codimension = 4 := by
  rw [rawGraph286, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph287Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph287 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence22Candidate rawIncidence22Valid rawGraph287Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph287Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph287Codimension : rawGraph287.codimension = 4 := by
  rw [rawGraph287, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph288Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph288 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence23Candidate rawIncidence23Valid rawGraph288Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence23Candidate rawIncidence23Valid rawGraph288Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph288Codimension : rawGraph288.codimension = 4 := by
  rw [rawGraph288, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph289Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph289 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence24Candidate rawIncidence24Valid rawGraph289Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence24Candidate rawIncidence24Valid rawGraph289Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph289Codimension : rawGraph289.codimension = 4 := by
  rw [rawGraph289, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph290Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph290 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence25Candidate rawIncidence25Valid rawGraph290Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence25Candidate rawIncidence25Valid rawGraph290Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph290Codimension : rawGraph290.codimension = 4 := by
  rw [rawGraph290, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph291Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph291 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence26Candidate rawIncidence26Valid rawGraph291Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence26Candidate rawIncidence26Valid rawGraph291Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph291Codimension : rawGraph291.codimension = 4 := by
  rw [rawGraph291, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph292Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph292 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence27Candidate rawIncidence27Valid rawGraph292Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence27Candidate rawIncidence27Valid rawGraph292Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph292Codimension : rawGraph292.codimension = 4 := by
  rw [rawGraph292, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph293Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph293 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph293Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph293Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph293Codimension : rawGraph293.codimension = 4 := by
  rw [rawGraph293, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph294Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph294 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph294Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph294Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph294Codimension : rawGraph294.codimension = 4 := by
  rw [rawGraph294, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph295Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 2]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph295 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph295Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph295Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph295Codimension : rawGraph295.codimension = 4 := by
  rw [rawGraph295, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph296Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![2, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph296 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph296Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph296Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph296Codimension : rawGraph296.codimension = 4 := by
  rw [rawGraph296, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph297Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph297 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph297Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph297Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph297Codimension : rawGraph297.codimension = 4 := by
  rw [rawGraph297, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph298Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph298 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph298Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph298Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph298Codimension : rawGraph298.codimension = 4 := by
  rw [rawGraph298, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph299Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 2], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph299 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph299Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph299Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph299Codimension : rawGraph299.codimension = 4 := by
  rw [rawGraph299, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph300Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph300 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph300Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph300Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph300Codimension : rawGraph300.codimension = 4 := by
  rw [rawGraph300, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph301Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph301 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph301Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph301Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph301Codimension : rawGraph301.codimension = 4 := by
  rw [rawGraph301, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph302Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![2, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph302 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph302Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph302Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph302Codimension : rawGraph302.codimension = 4 := by
  rw [rawGraph302, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph303Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph303 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence28Candidate rawIncidence28Valid rawGraph303Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence28Candidate rawIncidence28Valid rawGraph303Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph303Codimension : rawGraph303.codimension = 4 := by
  rw [rawGraph303, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph304Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph304 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph304Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph304Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph304Codimension : rawGraph304.codimension = 4 := by
  rw [rawGraph304, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph305Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph305 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence10Candidate rawIncidence10Valid rawGraph305Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph305Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph305Codimension : rawGraph305.codimension = 4 := by
  rw [rawGraph305, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph306Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph306 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence11Candidate rawIncidence11Valid rawGraph306Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence11Candidate rawIncidence11Valid rawGraph306Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph306Codimension : rawGraph306.codimension = 4 := by
  rw [rawGraph306, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph307Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph307 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence6Candidate rawIncidence6Valid rawGraph307Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph307Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph307Codimension : rawGraph307.codimension = 4 := by
  rw [rawGraph307, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph308Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph308 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph308Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph308Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph308Codimension : rawGraph308.codimension = 4 := by
  rw [rawGraph308, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph309Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph309 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph309Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph309Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph309Codimension : rawGraph309.codimension = 4 := by
  rw [rawGraph309, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph310Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph310 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph310Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph310Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph310Codimension : rawGraph310.codimension = 4 := by
  rw [rawGraph310, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph311Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![2, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph311 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph311Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph311Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph311Codimension : rawGraph311.codimension = 4 := by
  rw [rawGraph311, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph312Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph312 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph312Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph312Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph312Codimension : rawGraph312.codimension = 4 := by
  rw [rawGraph312, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph313Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph313 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph313Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph313Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph313Codimension : rawGraph313.codimension = 4 := by
  rw [rawGraph313, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph314Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph314 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence29Candidate rawIncidence29Valid rawGraph314Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence29Candidate rawIncidence29Valid rawGraph314Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph314Codimension : rawGraph314.codimension = 4 := by
  rw [rawGraph314, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph315Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph315 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence30Candidate rawIncidence30Valid rawGraph315Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence30Candidate rawIncidence30Valid rawGraph315Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph315Codimension : rawGraph315.codimension = 4 := by
  rw [rawGraph315, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph316Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph316 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence31Candidate rawIncidence31Valid rawGraph316Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence31Candidate rawIncidence31Valid rawGraph316Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph316Codimension : rawGraph316.codimension = 4 := by
  rw [rawGraph316, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph317Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph317 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence32Candidate rawIncidence32Valid rawGraph317Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence32Candidate rawIncidence32Valid rawGraph317Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph317Codimension : rawGraph317.codimension = 4 := by
  rw [rawGraph317, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph318Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph318 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph318Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph318Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph318Codimension : rawGraph318.codimension = 4 := by
  rw [rawGraph318, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph319Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph319 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph319Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph319Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph319Codimension : rawGraph319.codimension = 4 := by
  rw [rawGraph319, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph320Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph320 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph320Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph320Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph320Codimension : rawGraph320.codimension = 4 := by
  rw [rawGraph320, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph321Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![2, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph321 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph321Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph321Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph321Codimension : rawGraph321.codimension = 4 := by
  rw [rawGraph321, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph322Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph322 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence33Candidate rawIncidence33Valid rawGraph322Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence33Candidate rawIncidence33Valid rawGraph322Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph322Codimension : rawGraph322.codimension = 4 := by
  rw [rawGraph322, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph323Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph323 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence34Candidate rawIncidence34Valid rawGraph323Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence34Candidate rawIncidence34Valid rawGraph323Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph323Codimension : rawGraph323.codimension = 4 := by
  rw [rawGraph323, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph324Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph324 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence35Candidate rawIncidence35Valid rawGraph324Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence35Candidate rawIncidence35Valid rawGraph324Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph324Codimension : rawGraph324.codimension = 4 := by
  rw [rawGraph324, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph325Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph325 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence14Candidate rawIncidence14Valid rawGraph325Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph325Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph325Codimension : rawGraph325.codimension = 4 := by
  rw [rawGraph325, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph326Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![2, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph326 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence9Candidate rawIncidence9Valid rawGraph326Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph326Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph326Codimension : rawGraph326.codimension = 4 := by
  rw [rawGraph326, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph327Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph327 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence16Candidate rawIncidence16Valid rawGraph327Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph327Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph327Codimension : rawGraph327.codimension = 4 := by
  rw [rawGraph327, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph328Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph328 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph328Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph328Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph328Codimension : rawGraph328.codimension = 4 := by
  rw [rawGraph328, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph329Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph329 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence16Candidate rawIncidence16Valid rawGraph329Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph329Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph329Codimension : rawGraph329.codimension = 4 := by
  rw [rawGraph329, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph330Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![2, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph330 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence12Candidate rawIncidence12Valid rawGraph330Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph330Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph330Codimension : rawGraph330.codimension = 4 := by
  rw [rawGraph330, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph331Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph331 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph331Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph331Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph331Codimension : rawGraph331.codimension = 4 := by
  rw [rawGraph331, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph332Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![2, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph332 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph332Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph332Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph332Codimension : rawGraph332.codimension = 4 := by
  rw [rawGraph332, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph333Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph333 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph333Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph333Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph333Codimension : rawGraph333.codimension = 4 := by
  rw [rawGraph333, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph334Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 2], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph334 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence5Candidate rawIncidence5Valid rawGraph334Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph334Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph334Codimension : rawGraph334.codimension = 4 := by
  rw [rawGraph334, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph335Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph335 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence13Candidate rawIncidence13Valid rawGraph335Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph335Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph335Codimension : rawGraph335.codimension = 4 := by
  rw [rawGraph335, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph336Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![2, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph336 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence13Candidate rawIncidence13Valid rawGraph336Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph336Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph336Codimension : rawGraph336.codimension = 4 := by
  rw [rawGraph336, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph337Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph337 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence6Candidate rawIncidence6Valid rawGraph337Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph337Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph337Codimension : rawGraph337.codimension = 4 := by
  rw [rawGraph337, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph338Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![3, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph338 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph338Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph338Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph338Codimension : rawGraph338.codimension = 4 := by
  rw [rawGraph338, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph339Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 2]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph339 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph339Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph339Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph339Codimension : rawGraph339.codimension = 4 := by
  rw [rawGraph339, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph340Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph340 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence3Candidate rawIncidence3Valid rawGraph340Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph340Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph340Codimension : rawGraph340.codimension = 4 := by
  rw [rawGraph340, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph341Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![2, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph341 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence2Candidate rawIncidence2Valid rawGraph341Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph341Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph341Codimension : rawGraph341.codimension = 4 := by
  rw [rawGraph341, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph342Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![1, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph342 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence37Candidate rawIncidence37Valid rawGraph342Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence37Candidate rawIncidence37Valid rawGraph342Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph342Codimension : rawGraph342.codimension = 4 := by
  rw [rawGraph342, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph343Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph343 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence36Candidate rawIncidence36Valid rawGraph343Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence36Candidate rawIncidence36Valid rawGraph343Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph343Codimension : rawGraph343.codimension = 4 := by
  rw [rawGraph343, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph344Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph344 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph344Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph344Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph344Codimension : rawGraph344.codimension = 4 := by
  rw [rawGraph344, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph345Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![2, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph345 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph345Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph345Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph345Codimension : rawGraph345.codimension = 4 := by
  rw [rawGraph345, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph346Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 2]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph346 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence8Candidate rawIncidence8Valid rawGraph346Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph346Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph346Codimension : rawGraph346.codimension = 4 := by
  rw [rawGraph346, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph347Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph347 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph347Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph347Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph347Codimension : rawGraph347.codimension = 4 := by
  rw [rawGraph347, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph348Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph348 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence7Candidate rawIncidence7Valid rawGraph348Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph348Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph348Codimension : rawGraph348.codimension = 4 := by
  rw [rawGraph348, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph349Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph349 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence54Candidate rawIncidence54Valid rawGraph349Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence54Candidate rawIncidence54Valid rawGraph349Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph349Codimension : rawGraph349.codimension = 4 := by
  rw [rawGraph349, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph350Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph350 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence55Candidate rawIncidence55Valid rawGraph350Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence55Candidate rawIncidence55Valid rawGraph350Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph350Codimension : rawGraph350.codimension = 4 := by
  rw [rawGraph350, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph351Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph351 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph351Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph351Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph351Codimension : rawGraph351.codimension = 4 := by
  rw [rawGraph351, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph352Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph352 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph352Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph352Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph352Codimension : rawGraph352.codimension = 4 := by
  rw [rawGraph352, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph353Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph353 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence16Candidate rawIncidence16Valid rawGraph353Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph353Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph353Codimension : rawGraph353.codimension = 4 := by
  rw [rawGraph353, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph354Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph354 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph354Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph354Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph354Codimension : rawGraph354.codimension = 4 := by
  rw [rawGraph354, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph355Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph355 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence17Candidate rawIncidence17Valid rawGraph355Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph355Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph355Codimension : rawGraph355.codimension = 4 := by
  rw [rawGraph355, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph356Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph356 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence10Candidate rawIncidence10Valid rawGraph356Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph356Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph356Codimension : rawGraph356.codimension = 4 := by
  rw [rawGraph356, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph357Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 0], ![0, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph357 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence12Candidate rawIncidence12Valid rawGraph357Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph357Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph357Codimension : rawGraph357.codimension = 4 := by
  rw [rawGraph357, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph358Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph358 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence13Candidate rawIncidence13Valid rawGraph358Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph358Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph358Codimension : rawGraph358.codimension = 4 := by
  rw [rawGraph358, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph359Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 2]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph359 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence1Candidate rawIncidence1Valid rawGraph359Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph359Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph359Codimension : rawGraph359.codimension = 4 := by
  rw [rawGraph359, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph360Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph360 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence56Candidate rawIncidence56Valid rawGraph360Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence56Candidate rawIncidence56Valid rawGraph360Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph360Codimension : rawGraph360.codimension = 4 := by
  rw [rawGraph360, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph361Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph361 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence57Candidate rawIncidence57Valid rawGraph361Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence57Candidate rawIncidence57Valid rawGraph361Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph361Codimension : rawGraph361.codimension = 4 := by
  rw [rawGraph361, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph362Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph362 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence58Candidate rawIncidence58Valid rawGraph362Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence58Candidate rawIncidence58Valid rawGraph362Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph362Codimension : rawGraph362.codimension = 4 := by
  rw [rawGraph362, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph363Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph363 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence59Candidate rawIncidence59Valid rawGraph363Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence59Candidate rawIncidence59Valid rawGraph363Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph363Codimension : rawGraph363.codimension = 4 := by
  rw [rawGraph363, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph364Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 3 4 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Fin 3 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph364 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence60Candidate rawIncidence60Valid rawGraph364Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence60Candidate rawIncidence60Valid rawGraph364Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph364Codimension : rawGraph364.codimension = 4 := by
  rw [rawGraph364, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph365Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph365 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence18Candidate rawIncidence18Valid rawGraph365Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph365Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph365Codimension : rawGraph365.codimension = 4 := by
  rw [rawGraph365, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph366Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 2 3 4 → ℕ
  | .inl (vertex, index) =>
      (![![1, 0, 0, 0], ![0, 0, 0, 0]] : Fin 2 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![0, 0], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph366 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence19Candidate rawIncidence19Valid rawGraph366Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence19Candidate rawIncidence19Valid rawGraph366Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph366Codimension : rawGraph366.codimension = 4 := by
  rw [rawGraph366, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph367Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph367 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph367Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph367Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph367Codimension : rawGraph367.codimension = 4 := by
  rw [rawGraph367, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph368Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 0], ![1, 1]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph368 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph368Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph368Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph368Codimension : rawGraph368.codimension = 4 := by
  rw [rawGraph368, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph369Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) =>
      (![![0, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph369 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph369Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph369Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph369Codimension : rawGraph369.codimension = 4 := by
  rw [rawGraph369, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph370Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) =>
      (![![1, 1], ![0, 0]]) edge branch

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph370 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence4Candidate rawIncidence4Valid rawGraph370Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph370Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph370Codimension : rawGraph370.codimension = 4 := by
  rw [rawGraph370, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph371Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![0, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![4]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph371 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph371Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph371Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph371Codimension : rawGraph371.codimension = 4 := by
  rw [rawGraph371, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/
def rawGraph372Exponents :
    DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 4 → ℕ
  | .inl (vertex, index) =>
      (![![4, 0, 0, 0]] : Fin 1 → Fin 4 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- This representative uses the existing decorated-graph isomorphism quotient. -/
def rawGraph372 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      rawIncidence0Candidate rawIncidence0Valid rawGraph372Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph372Exponents)

/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/
theorem rawGraph372Codimension : rawGraph372.codimension = 4 := by
  rw [rawGraph372, TautologicalStratum.codimension_mk,
    DecoratedStableGraph.toDecoration_codimension]
  decide +kernel

/-- Raw source columns for ordered pair (0,0), degree 0; repetitions remain. -/
def raw_0_0_degree0Columns : Fin 1 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph0]

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_0_degree0Coordinates : RelationCertificate.Coordinates 1 :=
  ![1]

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_0_degree0ColumnsCodimension :
    ∀ i, (raw_0_0_degree0Columns i).codimension = 0 := by
  intro i
  fin_cases i
  · exact rawGraph0Codimension

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_0_degree0 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_0_degree0Columns raw_0_0_degree0Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_0_degree0_mem_degree : raw_0_0_degree0 ∈ StrataModule.degree 0 :=
  RelationCertificate.interpret_mem_degree
    raw_0_0_degree0Columns raw_0_0_degree0ColumnsCodimension raw_0_0_degree0Coordinates

/-- Raw source columns for ordered pair (0,0), degree 1; repetitions remain. -/
def raw_0_0_degree1Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_0_degree1Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_0_degree1ColumnsCodimension :
    ∀ i, (raw_0_0_degree1Columns i).codimension = 1 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_0_degree1 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_0_degree1Columns raw_0_0_degree1Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_0_degree1_mem_degree : raw_0_0_degree1 ∈ StrataModule.degree 1 :=
  RelationCertificate.interpret_mem_degree
    raw_0_0_degree1Columns raw_0_0_degree1ColumnsCodimension raw_0_0_degree1Coordinates

/-- Raw source columns for ordered pair (0,0), degree 2; repetitions remain. -/
def raw_0_0_degree2Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_0_degree2Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_0_degree2ColumnsCodimension :
    ∀ i, (raw_0_0_degree2Columns i).codimension = 2 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_0_degree2 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_0_degree2Columns raw_0_0_degree2Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_0_degree2_mem_degree : raw_0_0_degree2 ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree
    raw_0_0_degree2Columns raw_0_0_degree2ColumnsCodimension raw_0_0_degree2Coordinates

/-- Raw source columns for ordered pair (0,0), degree 3; repetitions remain. -/
def raw_0_0_degree3Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_0_degree3Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_0_degree3ColumnsCodimension :
    ∀ i, (raw_0_0_degree3Columns i).codimension = 3 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_0_degree3 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_0_degree3Columns raw_0_0_degree3Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_0_degree3_mem_degree : raw_0_0_degree3 ∈ StrataModule.degree 3 :=
  RelationCertificate.interpret_mem_degree
    raw_0_0_degree3Columns raw_0_0_degree3ColumnsCodimension raw_0_0_degree3Coordinates

/-- Raw source columns for ordered pair (0,0), degree 4; repetitions remain. -/
def raw_0_0_degree4Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_0_degree4Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_0_degree4ColumnsCodimension :
    ∀ i, (raw_0_0_degree4Columns i).codimension = 4 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_0_degree4 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_0_degree4Columns raw_0_0_degree4Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_0_degree4_mem_degree : raw_0_0_degree4 ∈ StrataModule.degree 4 :=
  RelationCertificate.interpret_mem_degree
    raw_0_0_degree4Columns raw_0_0_degree4ColumnsCodimension raw_0_0_degree4Coordinates

/-- Raw source columns for ordered pair (0,1), degree 0; repetitions remain. -/
def raw_0_1_degree0Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_1_degree0Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_1_degree0ColumnsCodimension :
    ∀ i, (raw_0_1_degree0Columns i).codimension = 0 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_1_degree0 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_1_degree0Columns raw_0_1_degree0Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_1_degree0_mem_degree : raw_0_1_degree0 ∈ StrataModule.degree 0 :=
  RelationCertificate.interpret_mem_degree
    raw_0_1_degree0Columns raw_0_1_degree0ColumnsCodimension raw_0_1_degree0Coordinates

/-- Raw source columns for ordered pair (0,1), degree 1; repetitions remain. -/
def raw_0_1_degree1Columns : Fin 5 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph1,
    rawGraph2,
    rawGraph3,
    rawGraph4,
    rawGraph5]

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_1_degree1Coordinates : RelationCertificate.Coordinates 5 :=
  ![(-1 / 12),
    (1 / 12),
    (1 / 24),
    (1 / 24),
    (1 / 24)]

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_1_degree1ColumnsCodimension :
    ∀ i, (raw_0_1_degree1Columns i).codimension = 1 := by
  intro i
  fin_cases i
  · exact rawGraph1Codimension
  · exact rawGraph2Codimension
  · exact rawGraph3Codimension
  · exact rawGraph4Codimension
  · exact rawGraph5Codimension

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_1_degree1 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_1_degree1Columns raw_0_1_degree1Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_1_degree1_mem_degree : raw_0_1_degree1 ∈ StrataModule.degree 1 :=
  RelationCertificate.interpret_mem_degree
    raw_0_1_degree1Columns raw_0_1_degree1ColumnsCodimension raw_0_1_degree1Coordinates

/-- Raw source columns for ordered pair (0,1), degree 2; repetitions remain. -/
def raw_0_1_degree2Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_1_degree2Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_1_degree2ColumnsCodimension :
    ∀ i, (raw_0_1_degree2Columns i).codimension = 2 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_1_degree2 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_1_degree2Columns raw_0_1_degree2Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_1_degree2_mem_degree : raw_0_1_degree2 ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree
    raw_0_1_degree2Columns raw_0_1_degree2ColumnsCodimension raw_0_1_degree2Coordinates

/-- Raw source columns for ordered pair (0,1), degree 3; repetitions remain. -/
def raw_0_1_degree3Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_1_degree3Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_1_degree3ColumnsCodimension :
    ∀ i, (raw_0_1_degree3Columns i).codimension = 3 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_1_degree3 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_1_degree3Columns raw_0_1_degree3Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_1_degree3_mem_degree : raw_0_1_degree3 ∈ StrataModule.degree 3 :=
  RelationCertificate.interpret_mem_degree
    raw_0_1_degree3Columns raw_0_1_degree3ColumnsCodimension raw_0_1_degree3Coordinates

/-- Raw source columns for ordered pair (0,1), degree 4; repetitions remain. -/
def raw_0_1_degree4Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_1_degree4Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_1_degree4ColumnsCodimension :
    ∀ i, (raw_0_1_degree4Columns i).codimension = 4 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_1_degree4 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_1_degree4Columns raw_0_1_degree4Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_1_degree4_mem_degree : raw_0_1_degree4 ∈ StrataModule.degree 4 :=
  RelationCertificate.interpret_mem_degree
    raw_0_1_degree4Columns raw_0_1_degree4ColumnsCodimension raw_0_1_degree4Coordinates

/-- Raw source columns for ordered pair (0,2), degree 0; repetitions remain. -/
def raw_0_2_degree0Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_2_degree0Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_2_degree0ColumnsCodimension :
    ∀ i, (raw_0_2_degree0Columns i).codimension = 0 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_2_degree0 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_2_degree0Columns raw_0_2_degree0Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_2_degree0_mem_degree : raw_0_2_degree0 ∈ StrataModule.degree 0 :=
  RelationCertificate.interpret_mem_degree
    raw_0_2_degree0Columns raw_0_2_degree0ColumnsCodimension raw_0_2_degree0Coordinates

/-- Raw source columns for ordered pair (0,2), degree 1; repetitions remain. -/
def raw_0_2_degree1Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_2_degree1Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_2_degree1ColumnsCodimension :
    ∀ i, (raw_0_2_degree1Columns i).codimension = 1 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_2_degree1 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_2_degree1Columns raw_0_2_degree1Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_2_degree1_mem_degree : raw_0_2_degree1 ∈ StrataModule.degree 1 :=
  RelationCertificate.interpret_mem_degree
    raw_0_2_degree1Columns raw_0_2_degree1ColumnsCodimension raw_0_2_degree1Coordinates

/-- Raw source columns for ordered pair (0,2), degree 2; repetitions remain. -/
def raw_0_2_degree2Columns : Fin 16 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph6,
    rawGraph7,
    rawGraph8,
    rawGraph9,
    rawGraph10,
    rawGraph11,
    rawGraph12,
    rawGraph13,
    rawGraph14,
    rawGraph15,
    rawGraph16,
    rawGraph17,
    rawGraph18,
    rawGraph19,
    rawGraph20,
    rawGraph21]

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_2_degree2Coordinates : RelationCertificate.Coordinates 16 :=
  ![(-1 / 144),
    (-1 / 144),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (1 / 1152),
    (1 / 144),
    (1 / 144),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288)]

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_2_degree2ColumnsCodimension :
    ∀ i, (raw_0_2_degree2Columns i).codimension = 2 := by
  intro i
  fin_cases i
  · exact rawGraph6Codimension
  · exact rawGraph7Codimension
  · exact rawGraph8Codimension
  · exact rawGraph9Codimension
  · exact rawGraph10Codimension
  · exact rawGraph11Codimension
  · exact rawGraph12Codimension
  · exact rawGraph13Codimension
  · exact rawGraph14Codimension
  · exact rawGraph15Codimension
  · exact rawGraph16Codimension
  · exact rawGraph17Codimension
  · exact rawGraph18Codimension
  · exact rawGraph19Codimension
  · exact rawGraph20Codimension
  · exact rawGraph21Codimension

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_2_degree2 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_2_degree2Columns raw_0_2_degree2Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_2_degree2_mem_degree : raw_0_2_degree2 ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree
    raw_0_2_degree2Columns raw_0_2_degree2ColumnsCodimension raw_0_2_degree2Coordinates

/-- Raw source columns for ordered pair (0,2), degree 3; repetitions remain. -/
def raw_0_2_degree3Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_2_degree3Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_2_degree3ColumnsCodimension :
    ∀ i, (raw_0_2_degree3Columns i).codimension = 3 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_2_degree3 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_2_degree3Columns raw_0_2_degree3Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_2_degree3_mem_degree : raw_0_2_degree3 ∈ StrataModule.degree 3 :=
  RelationCertificate.interpret_mem_degree
    raw_0_2_degree3Columns raw_0_2_degree3ColumnsCodimension raw_0_2_degree3Coordinates

/-- Raw source columns for ordered pair (0,2), degree 4; repetitions remain. -/
def raw_0_2_degree4Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_0_2_degree4Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_0_2_degree4ColumnsCodimension :
    ∀ i, (raw_0_2_degree4Columns i).codimension = 4 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_0_2_degree4 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_0_2_degree4Columns raw_0_2_degree4Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_0_2_degree4_mem_degree : raw_0_2_degree4 ∈ StrataModule.degree 4 :=
  RelationCertificate.interpret_mem_degree
    raw_0_2_degree4Columns raw_0_2_degree4ColumnsCodimension raw_0_2_degree4Coordinates

/-- Raw source columns for ordered pair (1,0), degree 0; repetitions remain. -/
def raw_1_0_degree0Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_0_degree0Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_0_degree0ColumnsCodimension :
    ∀ i, (raw_1_0_degree0Columns i).codimension = 0 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_0_degree0 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_0_degree0Columns raw_1_0_degree0Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_0_degree0_mem_degree : raw_1_0_degree0 ∈ StrataModule.degree 0 :=
  RelationCertificate.interpret_mem_degree
    raw_1_0_degree0Columns raw_1_0_degree0ColumnsCodimension raw_1_0_degree0Coordinates

/-- Raw source columns for ordered pair (1,0), degree 1; repetitions remain. -/
def raw_1_0_degree1Columns : Fin 5 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph1,
    rawGraph2,
    rawGraph3,
    rawGraph4,
    rawGraph5]

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_0_degree1Coordinates : RelationCertificate.Coordinates 5 :=
  ![(-1 / 12),
    (1 / 12),
    (1 / 24),
    (1 / 24),
    (1 / 24)]

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_0_degree1ColumnsCodimension :
    ∀ i, (raw_1_0_degree1Columns i).codimension = 1 := by
  intro i
  fin_cases i
  · exact rawGraph1Codimension
  · exact rawGraph2Codimension
  · exact rawGraph3Codimension
  · exact rawGraph4Codimension
  · exact rawGraph5Codimension

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_0_degree1 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_0_degree1Columns raw_1_0_degree1Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_0_degree1_mem_degree : raw_1_0_degree1 ∈ StrataModule.degree 1 :=
  RelationCertificate.interpret_mem_degree
    raw_1_0_degree1Columns raw_1_0_degree1ColumnsCodimension raw_1_0_degree1Coordinates

/-- Raw source columns for ordered pair (1,0), degree 2; repetitions remain. -/
def raw_1_0_degree2Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_0_degree2Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_0_degree2ColumnsCodimension :
    ∀ i, (raw_1_0_degree2Columns i).codimension = 2 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_0_degree2 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_0_degree2Columns raw_1_0_degree2Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_0_degree2_mem_degree : raw_1_0_degree2 ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree
    raw_1_0_degree2Columns raw_1_0_degree2ColumnsCodimension raw_1_0_degree2Coordinates

/-- Raw source columns for ordered pair (1,0), degree 3; repetitions remain. -/
def raw_1_0_degree3Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_0_degree3Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_0_degree3ColumnsCodimension :
    ∀ i, (raw_1_0_degree3Columns i).codimension = 3 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_0_degree3 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_0_degree3Columns raw_1_0_degree3Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_0_degree3_mem_degree : raw_1_0_degree3 ∈ StrataModule.degree 3 :=
  RelationCertificate.interpret_mem_degree
    raw_1_0_degree3Columns raw_1_0_degree3ColumnsCodimension raw_1_0_degree3Coordinates

/-- Raw source columns for ordered pair (1,0), degree 4; repetitions remain. -/
def raw_1_0_degree4Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_0_degree4Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_0_degree4ColumnsCodimension :
    ∀ i, (raw_1_0_degree4Columns i).codimension = 4 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_0_degree4 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_0_degree4Columns raw_1_0_degree4Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_0_degree4_mem_degree : raw_1_0_degree4 ∈ StrataModule.degree 4 :=
  RelationCertificate.interpret_mem_degree
    raw_1_0_degree4Columns raw_1_0_degree4ColumnsCodimension raw_1_0_degree4Coordinates

/-- Raw source columns for ordered pair (1,1), degree 0; repetitions remain. -/
def raw_1_1_degree0Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_1_degree0Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_1_degree0ColumnsCodimension :
    ∀ i, (raw_1_1_degree0Columns i).codimension = 0 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_1_degree0 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_1_degree0Columns raw_1_1_degree0Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_1_degree0_mem_degree : raw_1_1_degree0 ∈ StrataModule.degree 0 :=
  RelationCertificate.interpret_mem_degree
    raw_1_1_degree0Columns raw_1_1_degree0ColumnsCodimension raw_1_1_degree0Coordinates

/-- Raw source columns for ordered pair (1,1), degree 1; repetitions remain. -/
def raw_1_1_degree1Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_1_degree1Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_1_degree1ColumnsCodimension :
    ∀ i, (raw_1_1_degree1Columns i).codimension = 1 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_1_degree1 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_1_degree1Columns raw_1_1_degree1Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_1_degree1_mem_degree : raw_1_1_degree1 ∈ StrataModule.degree 1 :=
  RelationCertificate.interpret_mem_degree
    raw_1_1_degree1Columns raw_1_1_degree1ColumnsCodimension raw_1_1_degree1Coordinates

/-- Raw source columns for ordered pair (1,1), degree 2; repetitions remain. -/
def raw_1_1_degree2Columns : Fin 28 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph8,
    rawGraph6,
    rawGraph22,
    rawGraph23,
    rawGraph9,
    rawGraph24,
    rawGraph25,
    rawGraph10,
    rawGraph11,
    rawGraph7,
    rawGraph17,
    rawGraph26,
    rawGraph27,
    rawGraph13,
    rawGraph14,
    rawGraph20,
    rawGraph21,
    rawGraph18,
    rawGraph28,
    rawGraph29,
    rawGraph30,
    rawGraph31,
    rawGraph32,
    rawGraph12,
    rawGraph33,
    rawGraph34,
    rawGraph35,
    rawGraph36]

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_1_degree2Coordinates : RelationCertificate.Coordinates 28 :=
  ![(-1 / 144),
    (-1 / 144),
    (-1 / 144),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (-1 / 72),
    (1 / 144),
    (1 / 144),
    (1 / 144),
    (1 / 144),
    (1 / 144),
    (1 / 144),
    (1 / 144),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 576),
    (1 / 576),
    (1 / 576),
    (1 / 576),
    (1 / 576)]

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_1_degree2ColumnsCodimension :
    ∀ i, (raw_1_1_degree2Columns i).codimension = 2 := by
  intro i
  fin_cases i
  · exact rawGraph8Codimension
  · exact rawGraph6Codimension
  · exact rawGraph22Codimension
  · exact rawGraph23Codimension
  · exact rawGraph9Codimension
  · exact rawGraph24Codimension
  · exact rawGraph25Codimension
  · exact rawGraph10Codimension
  · exact rawGraph11Codimension
  · exact rawGraph7Codimension
  · exact rawGraph17Codimension
  · exact rawGraph26Codimension
  · exact rawGraph27Codimension
  · exact rawGraph13Codimension
  · exact rawGraph14Codimension
  · exact rawGraph20Codimension
  · exact rawGraph21Codimension
  · exact rawGraph18Codimension
  · exact rawGraph28Codimension
  · exact rawGraph29Codimension
  · exact rawGraph30Codimension
  · exact rawGraph31Codimension
  · exact rawGraph32Codimension
  · exact rawGraph12Codimension
  · exact rawGraph33Codimension
  · exact rawGraph34Codimension
  · exact rawGraph35Codimension
  · exact rawGraph36Codimension

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_1_degree2 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_1_degree2Columns raw_1_1_degree2Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_1_degree2_mem_degree : raw_1_1_degree2 ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree
    raw_1_1_degree2Columns raw_1_1_degree2ColumnsCodimension raw_1_1_degree2Coordinates

/-- Raw source columns for ordered pair (1,1), degree 3; repetitions remain. -/
def raw_1_1_degree3Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_1_degree3Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_1_degree3ColumnsCodimension :
    ∀ i, (raw_1_1_degree3Columns i).codimension = 3 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_1_degree3 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_1_degree3Columns raw_1_1_degree3Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_1_degree3_mem_degree : raw_1_1_degree3 ∈ StrataModule.degree 3 :=
  RelationCertificate.interpret_mem_degree
    raw_1_1_degree3Columns raw_1_1_degree3ColumnsCodimension raw_1_1_degree3Coordinates

/-- Raw source columns for ordered pair (1,1), degree 4; repetitions remain. -/
def raw_1_1_degree4Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_1_degree4Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_1_degree4ColumnsCodimension :
    ∀ i, (raw_1_1_degree4Columns i).codimension = 4 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_1_degree4 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_1_degree4Columns raw_1_1_degree4Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_1_degree4_mem_degree : raw_1_1_degree4 ∈ StrataModule.degree 4 :=
  RelationCertificate.interpret_mem_degree
    raw_1_1_degree4Columns raw_1_1_degree4ColumnsCodimension raw_1_1_degree4Coordinates

/-- Raw source columns for ordered pair (1,2), degree 0; repetitions remain. -/
def raw_1_2_degree0Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_2_degree0Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_2_degree0ColumnsCodimension :
    ∀ i, (raw_1_2_degree0Columns i).codimension = 0 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_2_degree0 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_2_degree0Columns raw_1_2_degree0Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_2_degree0_mem_degree : raw_1_2_degree0 ∈ StrataModule.degree 0 :=
  RelationCertificate.interpret_mem_degree
    raw_1_2_degree0Columns raw_1_2_degree0ColumnsCodimension raw_1_2_degree0Coordinates

/-- Raw source columns for ordered pair (1,2), degree 1; repetitions remain. -/
def raw_1_2_degree1Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_2_degree1Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_2_degree1ColumnsCodimension :
    ∀ i, (raw_1_2_degree1Columns i).codimension = 1 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_2_degree1 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_2_degree1Columns raw_1_2_degree1Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_2_degree1_mem_degree : raw_1_2_degree1 ∈ StrataModule.degree 1 :=
  RelationCertificate.interpret_mem_degree
    raw_1_2_degree1Columns raw_1_2_degree1ColumnsCodimension raw_1_2_degree1Coordinates

/-- Raw source columns for ordered pair (1,2), degree 2; repetitions remain. -/
def raw_1_2_degree2Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_2_degree2Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_2_degree2ColumnsCodimension :
    ∀ i, (raw_1_2_degree2Columns i).codimension = 2 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_2_degree2 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_2_degree2Columns raw_1_2_degree2Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_2_degree2_mem_degree : raw_1_2_degree2 ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree
    raw_1_2_degree2Columns raw_1_2_degree2ColumnsCodimension raw_1_2_degree2Coordinates

/-- Raw source columns for ordered pair (1,2), degree 3; repetitions remain. -/
def raw_1_2_degree3Columns : Fin 122 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph37,
    rawGraph38,
    rawGraph39,
    rawGraph40,
    rawGraph41,
    rawGraph42,
    rawGraph43,
    rawGraph44,
    rawGraph45,
    rawGraph46,
    rawGraph47,
    rawGraph48,
    rawGraph49,
    rawGraph50,
    rawGraph51,
    rawGraph52,
    rawGraph53,
    rawGraph54,
    rawGraph55,
    rawGraph56,
    rawGraph57,
    rawGraph58,
    rawGraph59,
    rawGraph60,
    rawGraph50,
    rawGraph61,
    rawGraph62,
    rawGraph63,
    rawGraph64,
    rawGraph65,
    rawGraph66,
    rawGraph67,
    rawGraph41,
    rawGraph42,
    rawGraph62,
    rawGraph64,
    rawGraph68,
    rawGraph69,
    rawGraph70,
    rawGraph71,
    rawGraph72,
    rawGraph73,
    rawGraph74,
    rawGraph75,
    rawGraph76,
    rawGraph77,
    rawGraph78,
    rawGraph79,
    rawGraph80,
    rawGraph81,
    rawGraph82,
    rawGraph83,
    rawGraph84,
    rawGraph85,
    rawGraph86,
    rawGraph87,
    rawGraph88,
    rawGraph89,
    rawGraph90,
    rawGraph91,
    rawGraph91,
    rawGraph92,
    rawGraph92,
    rawGraph93,
    rawGraph93,
    rawGraph94,
    rawGraph94,
    rawGraph95,
    rawGraph95,
    rawGraph96,
    rawGraph96,
    rawGraph97,
    rawGraph97,
    rawGraph98,
    rawGraph98,
    rawGraph99,
    rawGraph100,
    rawGraph101,
    rawGraph102,
    rawGraph103,
    rawGraph104,
    rawGraph105,
    rawGraph106,
    rawGraph107,
    rawGraph108,
    rawGraph109,
    rawGraph110,
    rawGraph111,
    rawGraph112,
    rawGraph113,
    rawGraph114,
    rawGraph115,
    rawGraph116,
    rawGraph117,
    rawGraph118,
    rawGraph119,
    rawGraph120,
    rawGraph121,
    rawGraph100,
    rawGraph122,
    rawGraph101,
    rawGraph123,
    rawGraph124,
    rawGraph125,
    rawGraph126,
    rawGraph85,
    rawGraph127,
    rawGraph128,
    rawGraph129,
    rawGraph130,
    rawGraph131,
    rawGraph132,
    rawGraph133,
    rawGraph134,
    rawGraph135,
    rawGraph136,
    rawGraph137,
    rawGraph138,
    rawGraph139,
    rawGraph140,
    rawGraph141,
    rawGraph142]

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_2_degree3Coordinates : RelationCertificate.Coordinates 122 :=
  ![(-1 / 1152),
    (-1 / 1152),
    (-1 / 1152),
    (-1 / 1152),
    (-1 / 13824),
    (-1 / 13824),
    (-1 / 13824),
    (-1 / 13824),
    (-1 / 13824),
    (-1 / 1728),
    (-1 / 1728),
    (-1 / 1728),
    (-1 / 1728),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-5 / 3456),
    (1 / 1152),
    (1 / 1152),
    (1 / 1152),
    (1 / 13824),
    (1 / 13824),
    (1 / 13824),
    (1 / 1728),
    (1 / 1728),
    (1 / 1728),
    (1 / 2304),
    (1 / 2304),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (5 / 6912),
    (5 / 6912)]

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_2_degree3ColumnsCodimension :
    ∀ i, (raw_1_2_degree3Columns i).codimension = 3 := by
  intro i
  fin_cases i
  · exact rawGraph37Codimension
  · exact rawGraph38Codimension
  · exact rawGraph39Codimension
  · exact rawGraph40Codimension
  · exact rawGraph41Codimension
  · exact rawGraph42Codimension
  · exact rawGraph43Codimension
  · exact rawGraph44Codimension
  · exact rawGraph45Codimension
  · exact rawGraph46Codimension
  · exact rawGraph47Codimension
  · exact rawGraph48Codimension
  · exact rawGraph49Codimension
  · exact rawGraph50Codimension
  · exact rawGraph51Codimension
  · exact rawGraph52Codimension
  · exact rawGraph53Codimension
  · exact rawGraph54Codimension
  · exact rawGraph55Codimension
  · exact rawGraph56Codimension
  · exact rawGraph57Codimension
  · exact rawGraph58Codimension
  · exact rawGraph59Codimension
  · exact rawGraph60Codimension
  · exact rawGraph50Codimension
  · exact rawGraph61Codimension
  · exact rawGraph62Codimension
  · exact rawGraph63Codimension
  · exact rawGraph64Codimension
  · exact rawGraph65Codimension
  · exact rawGraph66Codimension
  · exact rawGraph67Codimension
  · exact rawGraph41Codimension
  · exact rawGraph42Codimension
  · exact rawGraph62Codimension
  · exact rawGraph64Codimension
  · exact rawGraph68Codimension
  · exact rawGraph69Codimension
  · exact rawGraph70Codimension
  · exact rawGraph71Codimension
  · exact rawGraph72Codimension
  · exact rawGraph73Codimension
  · exact rawGraph74Codimension
  · exact rawGraph75Codimension
  · exact rawGraph76Codimension
  · exact rawGraph77Codimension
  · exact rawGraph78Codimension
  · exact rawGraph79Codimension
  · exact rawGraph80Codimension
  · exact rawGraph81Codimension
  · exact rawGraph82Codimension
  · exact rawGraph83Codimension
  · exact rawGraph84Codimension
  · exact rawGraph85Codimension
  · exact rawGraph86Codimension
  · exact rawGraph87Codimension
  · exact rawGraph88Codimension
  · exact rawGraph89Codimension
  · exact rawGraph90Codimension
  · exact rawGraph91Codimension
  · exact rawGraph91Codimension
  · exact rawGraph92Codimension
  · exact rawGraph92Codimension
  · exact rawGraph93Codimension
  · exact rawGraph93Codimension
  · exact rawGraph94Codimension
  · exact rawGraph94Codimension
  · exact rawGraph95Codimension
  · exact rawGraph95Codimension
  · exact rawGraph96Codimension
  · exact rawGraph96Codimension
  · exact rawGraph97Codimension
  · exact rawGraph97Codimension
  · exact rawGraph98Codimension
  · exact rawGraph98Codimension
  · exact rawGraph99Codimension
  · exact rawGraph100Codimension
  · exact rawGraph101Codimension
  · exact rawGraph102Codimension
  · exact rawGraph103Codimension
  · exact rawGraph104Codimension
  · exact rawGraph105Codimension
  · exact rawGraph106Codimension
  · exact rawGraph107Codimension
  · exact rawGraph108Codimension
  · exact rawGraph109Codimension
  · exact rawGraph110Codimension
  · exact rawGraph111Codimension
  · exact rawGraph112Codimension
  · exact rawGraph113Codimension
  · exact rawGraph114Codimension
  · exact rawGraph115Codimension
  · exact rawGraph116Codimension
  · exact rawGraph117Codimension
  · exact rawGraph118Codimension
  · exact rawGraph119Codimension
  · exact rawGraph120Codimension
  · exact rawGraph121Codimension
  · exact rawGraph100Codimension
  · exact rawGraph122Codimension
  · exact rawGraph101Codimension
  · exact rawGraph123Codimension
  · exact rawGraph124Codimension
  · exact rawGraph125Codimension
  · exact rawGraph126Codimension
  · exact rawGraph85Codimension
  · exact rawGraph127Codimension
  · exact rawGraph128Codimension
  · exact rawGraph129Codimension
  · exact rawGraph130Codimension
  · exact rawGraph131Codimension
  · exact rawGraph132Codimension
  · exact rawGraph133Codimension
  · exact rawGraph134Codimension
  · exact rawGraph135Codimension
  · exact rawGraph136Codimension
  · exact rawGraph137Codimension
  · exact rawGraph138Codimension
  · exact rawGraph139Codimension
  · exact rawGraph140Codimension
  · exact rawGraph141Codimension
  · exact rawGraph142Codimension

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_2_degree3 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_2_degree3Columns raw_1_2_degree3Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_2_degree3_mem_degree : raw_1_2_degree3 ∈ StrataModule.degree 3 :=
  RelationCertificate.interpret_mem_degree
    raw_1_2_degree3Columns raw_1_2_degree3ColumnsCodimension raw_1_2_degree3Coordinates

/-- Raw source columns for ordered pair (1,2), degree 4; repetitions remain. -/
def raw_1_2_degree4Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_1_2_degree4Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_1_2_degree4ColumnsCodimension :
    ∀ i, (raw_1_2_degree4Columns i).codimension = 4 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_1_2_degree4 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_1_2_degree4Columns raw_1_2_degree4Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_1_2_degree4_mem_degree : raw_1_2_degree4 ∈ StrataModule.degree 4 :=
  RelationCertificate.interpret_mem_degree
    raw_1_2_degree4Columns raw_1_2_degree4ColumnsCodimension raw_1_2_degree4Coordinates

/-- Raw source columns for ordered pair (2,0), degree 0; repetitions remain. -/
def raw_2_0_degree0Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_0_degree0Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_0_degree0ColumnsCodimension :
    ∀ i, (raw_2_0_degree0Columns i).codimension = 0 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_0_degree0 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_0_degree0Columns raw_2_0_degree0Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_0_degree0_mem_degree : raw_2_0_degree0 ∈ StrataModule.degree 0 :=
  RelationCertificate.interpret_mem_degree
    raw_2_0_degree0Columns raw_2_0_degree0ColumnsCodimension raw_2_0_degree0Coordinates

/-- Raw source columns for ordered pair (2,0), degree 1; repetitions remain. -/
def raw_2_0_degree1Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_0_degree1Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_0_degree1ColumnsCodimension :
    ∀ i, (raw_2_0_degree1Columns i).codimension = 1 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_0_degree1 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_0_degree1Columns raw_2_0_degree1Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_0_degree1_mem_degree : raw_2_0_degree1 ∈ StrataModule.degree 1 :=
  RelationCertificate.interpret_mem_degree
    raw_2_0_degree1Columns raw_2_0_degree1ColumnsCodimension raw_2_0_degree1Coordinates

/-- Raw source columns for ordered pair (2,0), degree 2; repetitions remain. -/
def raw_2_0_degree2Columns : Fin 16 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph6,
    rawGraph7,
    rawGraph8,
    rawGraph9,
    rawGraph10,
    rawGraph11,
    rawGraph12,
    rawGraph13,
    rawGraph14,
    rawGraph15,
    rawGraph16,
    rawGraph17,
    rawGraph18,
    rawGraph19,
    rawGraph20,
    rawGraph21]

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_0_degree2Coordinates : RelationCertificate.Coordinates 16 :=
  ![(-1 / 144),
    (-1 / 144),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (1 / 1152),
    (1 / 144),
    (1 / 144),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288)]

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_0_degree2ColumnsCodimension :
    ∀ i, (raw_2_0_degree2Columns i).codimension = 2 := by
  intro i
  fin_cases i
  · exact rawGraph6Codimension
  · exact rawGraph7Codimension
  · exact rawGraph8Codimension
  · exact rawGraph9Codimension
  · exact rawGraph10Codimension
  · exact rawGraph11Codimension
  · exact rawGraph12Codimension
  · exact rawGraph13Codimension
  · exact rawGraph14Codimension
  · exact rawGraph15Codimension
  · exact rawGraph16Codimension
  · exact rawGraph17Codimension
  · exact rawGraph18Codimension
  · exact rawGraph19Codimension
  · exact rawGraph20Codimension
  · exact rawGraph21Codimension

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_0_degree2 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_0_degree2Columns raw_2_0_degree2Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_0_degree2_mem_degree : raw_2_0_degree2 ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree
    raw_2_0_degree2Columns raw_2_0_degree2ColumnsCodimension raw_2_0_degree2Coordinates

/-- Raw source columns for ordered pair (2,0), degree 3; repetitions remain. -/
def raw_2_0_degree3Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_0_degree3Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_0_degree3ColumnsCodimension :
    ∀ i, (raw_2_0_degree3Columns i).codimension = 3 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_0_degree3 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_0_degree3Columns raw_2_0_degree3Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_0_degree3_mem_degree : raw_2_0_degree3 ∈ StrataModule.degree 3 :=
  RelationCertificate.interpret_mem_degree
    raw_2_0_degree3Columns raw_2_0_degree3ColumnsCodimension raw_2_0_degree3Coordinates

/-- Raw source columns for ordered pair (2,0), degree 4; repetitions remain. -/
def raw_2_0_degree4Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_0_degree4Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_0_degree4ColumnsCodimension :
    ∀ i, (raw_2_0_degree4Columns i).codimension = 4 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_0_degree4 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_0_degree4Columns raw_2_0_degree4Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_0_degree4_mem_degree : raw_2_0_degree4 ∈ StrataModule.degree 4 :=
  RelationCertificate.interpret_mem_degree
    raw_2_0_degree4Columns raw_2_0_degree4ColumnsCodimension raw_2_0_degree4Coordinates

/-- Raw source columns for ordered pair (2,1), degree 0; repetitions remain. -/
def raw_2_1_degree0Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_1_degree0Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_1_degree0ColumnsCodimension :
    ∀ i, (raw_2_1_degree0Columns i).codimension = 0 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_1_degree0 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_1_degree0Columns raw_2_1_degree0Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_1_degree0_mem_degree : raw_2_1_degree0 ∈ StrataModule.degree 0 :=
  RelationCertificate.interpret_mem_degree
    raw_2_1_degree0Columns raw_2_1_degree0ColumnsCodimension raw_2_1_degree0Coordinates

/-- Raw source columns for ordered pair (2,1), degree 1; repetitions remain. -/
def raw_2_1_degree1Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_1_degree1Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_1_degree1ColumnsCodimension :
    ∀ i, (raw_2_1_degree1Columns i).codimension = 1 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_1_degree1 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_1_degree1Columns raw_2_1_degree1Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_1_degree1_mem_degree : raw_2_1_degree1 ∈ StrataModule.degree 1 :=
  RelationCertificate.interpret_mem_degree
    raw_2_1_degree1Columns raw_2_1_degree1ColumnsCodimension raw_2_1_degree1Coordinates

/-- Raw source columns for ordered pair (2,1), degree 2; repetitions remain. -/
def raw_2_1_degree2Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_1_degree2Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_1_degree2ColumnsCodimension :
    ∀ i, (raw_2_1_degree2Columns i).codimension = 2 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_1_degree2 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_1_degree2Columns raw_2_1_degree2Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_1_degree2_mem_degree : raw_2_1_degree2 ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree
    raw_2_1_degree2Columns raw_2_1_degree2ColumnsCodimension raw_2_1_degree2Coordinates

/-- Raw source columns for ordered pair (2,1), degree 3; repetitions remain. -/
def raw_2_1_degree3Columns : Fin 108 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph37,
    rawGraph38,
    rawGraph39,
    rawGraph49,
    rawGraph40,
    rawGraph41,
    rawGraph42,
    rawGraph43,
    rawGraph44,
    rawGraph45,
    rawGraph46,
    rawGraph59,
    rawGraph60,
    rawGraph50,
    rawGraph66,
    rawGraph68,
    rawGraph72,
    rawGraph143,
    rawGraph144,
    rawGraph51,
    rawGraph52,
    rawGraph53,
    rawGraph54,
    rawGraph55,
    rawGraph56,
    rawGraph57,
    rawGraph47,
    rawGraph48,
    rawGraph50,
    rawGraph61,
    rawGraph62,
    rawGraph63,
    rawGraph64,
    rawGraph65,
    rawGraph66,
    rawGraph67,
    rawGraph41,
    rawGraph45,
    rawGraph145,
    rawGraph146,
    rawGraph147,
    rawGraph79,
    rawGraph80,
    rawGraph81,
    rawGraph87,
    rawGraph82,
    rawGraph83,
    rawGraph84,
    rawGraph85,
    rawGraph104,
    rawGraph106,
    rawGraph86,
    rawGraph114,
    rawGraph89,
    rawGraph90,
    rawGraph91,
    rawGraph91,
    rawGraph92,
    rawGraph92,
    rawGraph93,
    rawGraph93,
    rawGraph94,
    rawGraph94,
    rawGraph95,
    rawGraph95,
    rawGraph96,
    rawGraph96,
    rawGraph97,
    rawGraph97,
    rawGraph98,
    rawGraph98,
    rawGraph99,
    rawGraph100,
    rawGraph101,
    rawGraph129,
    rawGraph102,
    rawGraph131,
    rawGraph132,
    rawGraph107,
    rawGraph108,
    rawGraph109,
    rawGraph110,
    rawGraph111,
    rawGraph112,
    rawGraph113,
    rawGraph134,
    rawGraph88,
    rawGraph116,
    rawGraph117,
    rawGraph138,
    rawGraph118,
    rawGraph119,
    rawGraph120,
    rawGraph121,
    rawGraph100,
    rawGraph122,
    rawGraph101,
    rawGraph123,
    rawGraph124,
    rawGraph125,
    rawGraph126,
    rawGraph85,
    rawGraph135,
    rawGraph136,
    rawGraph139,
    rawGraph140,
    rawGraph141,
    rawGraph142]

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_1_degree3Coordinates : RelationCertificate.Coordinates 108 :=
  ![(-1 / 1152),
    (-1 / 1152),
    (-1 / 1152),
    (-1 / 1152),
    (-1 / 1152),
    (-1 / 13824),
    (-1 / 13824),
    (-1 / 13824),
    (-1 / 13824),
    (-1 / 13824),
    (-1 / 1728),
    (-1 / 1728),
    (-1 / 1728),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 3456),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-1 / 6912),
    (-5 / 3456),
    (1 / 1152),
    (1 / 1152),
    (1 / 1152),
    (1 / 1152),
    (1 / 13824),
    (1 / 13824),
    (1 / 13824),
    (1 / 1728),
    (1 / 1728),
    (1 / 1728),
    (1 / 1728),
    (1 / 2304),
    (1 / 2304),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 27648),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 3456),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (1 / 6912),
    (5 / 6912),
    (5 / 6912)]

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_1_degree3ColumnsCodimension :
    ∀ i, (raw_2_1_degree3Columns i).codimension = 3 := by
  intro i
  fin_cases i
  · exact rawGraph37Codimension
  · exact rawGraph38Codimension
  · exact rawGraph39Codimension
  · exact rawGraph49Codimension
  · exact rawGraph40Codimension
  · exact rawGraph41Codimension
  · exact rawGraph42Codimension
  · exact rawGraph43Codimension
  · exact rawGraph44Codimension
  · exact rawGraph45Codimension
  · exact rawGraph46Codimension
  · exact rawGraph59Codimension
  · exact rawGraph60Codimension
  · exact rawGraph50Codimension
  · exact rawGraph66Codimension
  · exact rawGraph68Codimension
  · exact rawGraph72Codimension
  · exact rawGraph143Codimension
  · exact rawGraph144Codimension
  · exact rawGraph51Codimension
  · exact rawGraph52Codimension
  · exact rawGraph53Codimension
  · exact rawGraph54Codimension
  · exact rawGraph55Codimension
  · exact rawGraph56Codimension
  · exact rawGraph57Codimension
  · exact rawGraph47Codimension
  · exact rawGraph48Codimension
  · exact rawGraph50Codimension
  · exact rawGraph61Codimension
  · exact rawGraph62Codimension
  · exact rawGraph63Codimension
  · exact rawGraph64Codimension
  · exact rawGraph65Codimension
  · exact rawGraph66Codimension
  · exact rawGraph67Codimension
  · exact rawGraph41Codimension
  · exact rawGraph45Codimension
  · exact rawGraph145Codimension
  · exact rawGraph146Codimension
  · exact rawGraph147Codimension
  · exact rawGraph79Codimension
  · exact rawGraph80Codimension
  · exact rawGraph81Codimension
  · exact rawGraph87Codimension
  · exact rawGraph82Codimension
  · exact rawGraph83Codimension
  · exact rawGraph84Codimension
  · exact rawGraph85Codimension
  · exact rawGraph104Codimension
  · exact rawGraph106Codimension
  · exact rawGraph86Codimension
  · exact rawGraph114Codimension
  · exact rawGraph89Codimension
  · exact rawGraph90Codimension
  · exact rawGraph91Codimension
  · exact rawGraph91Codimension
  · exact rawGraph92Codimension
  · exact rawGraph92Codimension
  · exact rawGraph93Codimension
  · exact rawGraph93Codimension
  · exact rawGraph94Codimension
  · exact rawGraph94Codimension
  · exact rawGraph95Codimension
  · exact rawGraph95Codimension
  · exact rawGraph96Codimension
  · exact rawGraph96Codimension
  · exact rawGraph97Codimension
  · exact rawGraph97Codimension
  · exact rawGraph98Codimension
  · exact rawGraph98Codimension
  · exact rawGraph99Codimension
  · exact rawGraph100Codimension
  · exact rawGraph101Codimension
  · exact rawGraph129Codimension
  · exact rawGraph102Codimension
  · exact rawGraph131Codimension
  · exact rawGraph132Codimension
  · exact rawGraph107Codimension
  · exact rawGraph108Codimension
  · exact rawGraph109Codimension
  · exact rawGraph110Codimension
  · exact rawGraph111Codimension
  · exact rawGraph112Codimension
  · exact rawGraph113Codimension
  · exact rawGraph134Codimension
  · exact rawGraph88Codimension
  · exact rawGraph116Codimension
  · exact rawGraph117Codimension
  · exact rawGraph138Codimension
  · exact rawGraph118Codimension
  · exact rawGraph119Codimension
  · exact rawGraph120Codimension
  · exact rawGraph121Codimension
  · exact rawGraph100Codimension
  · exact rawGraph122Codimension
  · exact rawGraph101Codimension
  · exact rawGraph123Codimension
  · exact rawGraph124Codimension
  · exact rawGraph125Codimension
  · exact rawGraph126Codimension
  · exact rawGraph85Codimension
  · exact rawGraph135Codimension
  · exact rawGraph136Codimension
  · exact rawGraph139Codimension
  · exact rawGraph140Codimension
  · exact rawGraph141Codimension
  · exact rawGraph142Codimension

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_1_degree3 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_1_degree3Columns raw_2_1_degree3Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_1_degree3_mem_degree : raw_2_1_degree3 ∈ StrataModule.degree 3 :=
  RelationCertificate.interpret_mem_degree
    raw_2_1_degree3Columns raw_2_1_degree3ColumnsCodimension raw_2_1_degree3Coordinates

/-- Raw source columns for ordered pair (2,1), degree 4; repetitions remain. -/
def raw_2_1_degree4Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_1_degree4Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_1_degree4ColumnsCodimension :
    ∀ i, (raw_2_1_degree4Columns i).codimension = 4 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_1_degree4 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_1_degree4Columns raw_2_1_degree4Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_1_degree4_mem_degree : raw_2_1_degree4 ∈ StrataModule.degree 4 :=
  RelationCertificate.interpret_mem_degree
    raw_2_1_degree4Columns raw_2_1_degree4ColumnsCodimension raw_2_1_degree4Coordinates

/-- Raw source columns for ordered pair (2,2), degree 0; repetitions remain. -/
def raw_2_2_degree0Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_2_degree0Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_2_degree0ColumnsCodimension :
    ∀ i, (raw_2_2_degree0Columns i).codimension = 0 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_2_degree0 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_2_degree0Columns raw_2_2_degree0Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_2_degree0_mem_degree : raw_2_2_degree0 ∈ StrataModule.degree 0 :=
  RelationCertificate.interpret_mem_degree
    raw_2_2_degree0Columns raw_2_2_degree0ColumnsCodimension raw_2_2_degree0Coordinates

/-- Raw source columns for ordered pair (2,2), degree 1; repetitions remain. -/
def raw_2_2_degree1Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_2_degree1Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_2_degree1ColumnsCodimension :
    ∀ i, (raw_2_2_degree1Columns i).codimension = 1 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_2_degree1 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_2_degree1Columns raw_2_2_degree1Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_2_degree1_mem_degree : raw_2_2_degree1 ∈ StrataModule.degree 1 :=
  RelationCertificate.interpret_mem_degree
    raw_2_2_degree1Columns raw_2_2_degree1ColumnsCodimension raw_2_2_degree1Coordinates

/-- Raw source columns for ordered pair (2,2), degree 2; repetitions remain. -/
def raw_2_2_degree2Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_2_degree2Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_2_degree2ColumnsCodimension :
    ∀ i, (raw_2_2_degree2Columns i).codimension = 2 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_2_degree2 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_2_degree2Columns raw_2_2_degree2Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_2_degree2_mem_degree : raw_2_2_degree2 ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree
    raw_2_2_degree2Columns raw_2_2_degree2ColumnsCodimension raw_2_2_degree2Coordinates

/-- Raw source columns for ordered pair (2,2), degree 3; repetitions remain. -/
def raw_2_2_degree3Columns : Fin 0 → TautologicalStratum 2 (Fin 1) :=
  Fin.elim0

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_2_degree3Coordinates : RelationCertificate.Coordinates 0 :=
  Fin.elim0

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_2_degree3ColumnsCodimension :
    ∀ i, (raw_2_2_degree3Columns i).codimension = 3 := by
  intro i
  exact Fin.elim0 i

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_2_degree3 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_2_degree3Columns raw_2_2_degree3Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_2_degree3_mem_degree : raw_2_2_degree3 ∈ StrataModule.degree 3 :=
  RelationCertificate.interpret_mem_degree
    raw_2_2_degree3Columns raw_2_2_degree3ColumnsCodimension raw_2_2_degree3Coordinates

/-- Raw source columns for ordered pair (2,2), degree 4; repetitions remain. -/
def raw_2_2_degree4Columns : Fin 252 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph148,
    rawGraph149,
    rawGraph150,
    rawGraph151,
    rawGraph152,
    rawGraph153,
    rawGraph154,
    rawGraph155,
    rawGraph155,
    rawGraph156,
    rawGraph157,
    rawGraph158,
    rawGraph159,
    rawGraph159,
    rawGraph160,
    rawGraph161,
    rawGraph162,
    rawGraph163,
    rawGraph164,
    rawGraph165,
    rawGraph166,
    rawGraph167,
    rawGraph167,
    rawGraph168,
    rawGraph169,
    rawGraph170,
    rawGraph171,
    rawGraph171,
    rawGraph172,
    rawGraph173,
    rawGraph174,
    rawGraph175,
    rawGraph176,
    rawGraph177,
    rawGraph178,
    rawGraph179,
    rawGraph180,
    rawGraph181,
    rawGraph182,
    rawGraph183,
    rawGraph184,
    rawGraph185,
    rawGraph186,
    rawGraph187,
    rawGraph188,
    rawGraph189,
    rawGraph190,
    rawGraph191,
    rawGraph192,
    rawGraph193,
    rawGraph194,
    rawGraph195,
    rawGraph196,
    rawGraph197,
    rawGraph198,
    rawGraph199,
    rawGraph200,
    rawGraph201,
    rawGraph202,
    rawGraph190,
    rawGraph203,
    rawGraph204,
    rawGraph205,
    rawGraph206,
    rawGraph207,
    rawGraph208,
    rawGraph209,
    rawGraph210,
    rawGraph211,
    rawGraph212,
    rawGraph213,
    rawGraph214,
    rawGraph208,
    rawGraph215,
    rawGraph216,
    rawGraph217,
    rawGraph218,
    rawGraph219,
    rawGraph220,
    rawGraph221,
    rawGraph222,
    rawGraph223,
    rawGraph224,
    rawGraph225,
    rawGraph226,
    rawGraph227,
    rawGraph228,
    rawGraph229,
    rawGraph230,
    rawGraph231,
    rawGraph232,
    rawGraph233,
    rawGraph234,
    rawGraph235,
    rawGraph236,
    rawGraph237,
    rawGraph238,
    rawGraph239,
    rawGraph240,
    rawGraph241,
    rawGraph242,
    rawGraph205,
    rawGraph206,
    rawGraph243,
    rawGraph244,
    rawGraph245,
    rawGraph246,
    rawGraph247,
    rawGraph248,
    rawGraph249,
    rawGraph250,
    rawGraph251,
    rawGraph252,
    rawGraph253,
    rawGraph254,
    rawGraph255,
    rawGraph256,
    rawGraph257,
    rawGraph258,
    rawGraph214,
    rawGraph241,
    rawGraph259,
    rawGraph260,
    rawGraph242,
    rawGraph261,
    rawGraph262,
    rawGraph263,
    rawGraph264,
    rawGraph265,
    rawGraph266,
    rawGraph267,
    rawGraph268,
    rawGraph269,
    rawGraph270,
    rawGraph271,
    rawGraph272,
    rawGraph273,
    rawGraph274,
    rawGraph275,
    rawGraph276,
    rawGraph277,
    rawGraph278,
    rawGraph279,
    rawGraph280,
    rawGraph281,
    rawGraph282,
    rawGraph283,
    rawGraph284,
    rawGraph285,
    rawGraph285,
    rawGraph286,
    rawGraph286,
    rawGraph287,
    rawGraph287,
    rawGraph288,
    rawGraph288,
    rawGraph289,
    rawGraph289,
    rawGraph290,
    rawGraph290,
    rawGraph291,
    rawGraph291,
    rawGraph292,
    rawGraph292,
    rawGraph293,
    rawGraph294,
    rawGraph295,
    rawGraph296,
    rawGraph297,
    rawGraph298,
    rawGraph299,
    rawGraph300,
    rawGraph301,
    rawGraph302,
    rawGraph303,
    rawGraph304,
    rawGraph305,
    rawGraph306,
    rawGraph307,
    rawGraph308,
    rawGraph309,
    rawGraph310,
    rawGraph311,
    rawGraph312,
    rawGraph313,
    rawGraph314,
    rawGraph315,
    rawGraph316,
    rawGraph317,
    rawGraph304,
    rawGraph318,
    rawGraph319,
    rawGraph320,
    rawGraph321,
    rawGraph322,
    rawGraph323,
    rawGraph324,
    rawGraph325,
    rawGraph326,
    rawGraph327,
    rawGraph328,
    rawGraph329,
    rawGraph330,
    rawGraph331,
    rawGraph332,
    rawGraph333,
    rawGraph334,
    rawGraph335,
    rawGraph336,
    rawGraph337,
    rawGraph338,
    rawGraph339,
    rawGraph340,
    rawGraph341,
    rawGraph342,
    rawGraph343,
    rawGraph344,
    rawGraph345,
    rawGraph346,
    rawGraph347,
    rawGraph348,
    rawGraph349,
    rawGraph350,
    rawGraph293,
    rawGraph294,
    rawGraph351,
    rawGraph352,
    rawGraph300,
    rawGraph318,
    rawGraph348,
    rawGraph353,
    rawGraph354,
    rawGraph355,
    rawGraph356,
    rawGraph357,
    rawGraph358,
    rawGraph359,
    rawGraph360,
    rawGraph361,
    rawGraph362,
    rawGraph363,
    rawGraph364,
    rawGraph365,
    rawGraph366,
    rawGraph351,
    rawGraph367,
    rawGraph368,
    rawGraph369,
    rawGraph352,
    rawGraph370,
    rawGraph371,
    rawGraph372]

/-- Exact raw-gluing coefficients, without an additional automorphism division. -/
def raw_2_2_degree4Coordinates : RelationCertificate.Coordinates 252 :=
  ![(-1 / 10368),
    (-1 / 10368),
    (-1 / 13824),
    (-1 / 13824),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 165888),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 20736),
    (-1 / 27648),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 41472),
    (-1 / 5184),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (-1 / 82944),
    (1 / 10368),
    (1 / 10368),
    (1 / 10368),
    (1 / 10368),
    (1 / 10368),
    (1 / 13824),
    (1 / 13824),
    (1 / 13824),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 165888),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 20736),
    (1 / 27648),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 41472),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944),
    (1 / 82944)]

/-- Every source column has the recorded edge-plus-decoration degree. -/
theorem raw_2_2_degree4ColumnsCodimension :
    ∀ i, (raw_2_2_degree4Columns i).codimension = 4 := by
  intro i
  fin_cases i
  · exact rawGraph148Codimension
  · exact rawGraph149Codimension
  · exact rawGraph150Codimension
  · exact rawGraph151Codimension
  · exact rawGraph152Codimension
  · exact rawGraph153Codimension
  · exact rawGraph154Codimension
  · exact rawGraph155Codimension
  · exact rawGraph155Codimension
  · exact rawGraph156Codimension
  · exact rawGraph157Codimension
  · exact rawGraph158Codimension
  · exact rawGraph159Codimension
  · exact rawGraph159Codimension
  · exact rawGraph160Codimension
  · exact rawGraph161Codimension
  · exact rawGraph162Codimension
  · exact rawGraph163Codimension
  · exact rawGraph164Codimension
  · exact rawGraph165Codimension
  · exact rawGraph166Codimension
  · exact rawGraph167Codimension
  · exact rawGraph167Codimension
  · exact rawGraph168Codimension
  · exact rawGraph169Codimension
  · exact rawGraph170Codimension
  · exact rawGraph171Codimension
  · exact rawGraph171Codimension
  · exact rawGraph172Codimension
  · exact rawGraph173Codimension
  · exact rawGraph174Codimension
  · exact rawGraph175Codimension
  · exact rawGraph176Codimension
  · exact rawGraph177Codimension
  · exact rawGraph178Codimension
  · exact rawGraph179Codimension
  · exact rawGraph180Codimension
  · exact rawGraph181Codimension
  · exact rawGraph182Codimension
  · exact rawGraph183Codimension
  · exact rawGraph184Codimension
  · exact rawGraph185Codimension
  · exact rawGraph186Codimension
  · exact rawGraph187Codimension
  · exact rawGraph188Codimension
  · exact rawGraph189Codimension
  · exact rawGraph190Codimension
  · exact rawGraph191Codimension
  · exact rawGraph192Codimension
  · exact rawGraph193Codimension
  · exact rawGraph194Codimension
  · exact rawGraph195Codimension
  · exact rawGraph196Codimension
  · exact rawGraph197Codimension
  · exact rawGraph198Codimension
  · exact rawGraph199Codimension
  · exact rawGraph200Codimension
  · exact rawGraph201Codimension
  · exact rawGraph202Codimension
  · exact rawGraph190Codimension
  · exact rawGraph203Codimension
  · exact rawGraph204Codimension
  · exact rawGraph205Codimension
  · exact rawGraph206Codimension
  · exact rawGraph207Codimension
  · exact rawGraph208Codimension
  · exact rawGraph209Codimension
  · exact rawGraph210Codimension
  · exact rawGraph211Codimension
  · exact rawGraph212Codimension
  · exact rawGraph213Codimension
  · exact rawGraph214Codimension
  · exact rawGraph208Codimension
  · exact rawGraph215Codimension
  · exact rawGraph216Codimension
  · exact rawGraph217Codimension
  · exact rawGraph218Codimension
  · exact rawGraph219Codimension
  · exact rawGraph220Codimension
  · exact rawGraph221Codimension
  · exact rawGraph222Codimension
  · exact rawGraph223Codimension
  · exact rawGraph224Codimension
  · exact rawGraph225Codimension
  · exact rawGraph226Codimension
  · exact rawGraph227Codimension
  · exact rawGraph228Codimension
  · exact rawGraph229Codimension
  · exact rawGraph230Codimension
  · exact rawGraph231Codimension
  · exact rawGraph232Codimension
  · exact rawGraph233Codimension
  · exact rawGraph234Codimension
  · exact rawGraph235Codimension
  · exact rawGraph236Codimension
  · exact rawGraph237Codimension
  · exact rawGraph238Codimension
  · exact rawGraph239Codimension
  · exact rawGraph240Codimension
  · exact rawGraph241Codimension
  · exact rawGraph242Codimension
  · exact rawGraph205Codimension
  · exact rawGraph206Codimension
  · exact rawGraph243Codimension
  · exact rawGraph244Codimension
  · exact rawGraph245Codimension
  · exact rawGraph246Codimension
  · exact rawGraph247Codimension
  · exact rawGraph248Codimension
  · exact rawGraph249Codimension
  · exact rawGraph250Codimension
  · exact rawGraph251Codimension
  · exact rawGraph252Codimension
  · exact rawGraph253Codimension
  · exact rawGraph254Codimension
  · exact rawGraph255Codimension
  · exact rawGraph256Codimension
  · exact rawGraph257Codimension
  · exact rawGraph258Codimension
  · exact rawGraph214Codimension
  · exact rawGraph241Codimension
  · exact rawGraph259Codimension
  · exact rawGraph260Codimension
  · exact rawGraph242Codimension
  · exact rawGraph261Codimension
  · exact rawGraph262Codimension
  · exact rawGraph263Codimension
  · exact rawGraph264Codimension
  · exact rawGraph265Codimension
  · exact rawGraph266Codimension
  · exact rawGraph267Codimension
  · exact rawGraph268Codimension
  · exact rawGraph269Codimension
  · exact rawGraph270Codimension
  · exact rawGraph271Codimension
  · exact rawGraph272Codimension
  · exact rawGraph273Codimension
  · exact rawGraph274Codimension
  · exact rawGraph275Codimension
  · exact rawGraph276Codimension
  · exact rawGraph277Codimension
  · exact rawGraph278Codimension
  · exact rawGraph279Codimension
  · exact rawGraph280Codimension
  · exact rawGraph281Codimension
  · exact rawGraph282Codimension
  · exact rawGraph283Codimension
  · exact rawGraph284Codimension
  · exact rawGraph285Codimension
  · exact rawGraph285Codimension
  · exact rawGraph286Codimension
  · exact rawGraph286Codimension
  · exact rawGraph287Codimension
  · exact rawGraph287Codimension
  · exact rawGraph288Codimension
  · exact rawGraph288Codimension
  · exact rawGraph289Codimension
  · exact rawGraph289Codimension
  · exact rawGraph290Codimension
  · exact rawGraph290Codimension
  · exact rawGraph291Codimension
  · exact rawGraph291Codimension
  · exact rawGraph292Codimension
  · exact rawGraph292Codimension
  · exact rawGraph293Codimension
  · exact rawGraph294Codimension
  · exact rawGraph295Codimension
  · exact rawGraph296Codimension
  · exact rawGraph297Codimension
  · exact rawGraph298Codimension
  · exact rawGraph299Codimension
  · exact rawGraph300Codimension
  · exact rawGraph301Codimension
  · exact rawGraph302Codimension
  · exact rawGraph303Codimension
  · exact rawGraph304Codimension
  · exact rawGraph305Codimension
  · exact rawGraph306Codimension
  · exact rawGraph307Codimension
  · exact rawGraph308Codimension
  · exact rawGraph309Codimension
  · exact rawGraph310Codimension
  · exact rawGraph311Codimension
  · exact rawGraph312Codimension
  · exact rawGraph313Codimension
  · exact rawGraph314Codimension
  · exact rawGraph315Codimension
  · exact rawGraph316Codimension
  · exact rawGraph317Codimension
  · exact rawGraph304Codimension
  · exact rawGraph318Codimension
  · exact rawGraph319Codimension
  · exact rawGraph320Codimension
  · exact rawGraph321Codimension
  · exact rawGraph322Codimension
  · exact rawGraph323Codimension
  · exact rawGraph324Codimension
  · exact rawGraph325Codimension
  · exact rawGraph326Codimension
  · exact rawGraph327Codimension
  · exact rawGraph328Codimension
  · exact rawGraph329Codimension
  · exact rawGraph330Codimension
  · exact rawGraph331Codimension
  · exact rawGraph332Codimension
  · exact rawGraph333Codimension
  · exact rawGraph334Codimension
  · exact rawGraph335Codimension
  · exact rawGraph336Codimension
  · exact rawGraph337Codimension
  · exact rawGraph338Codimension
  · exact rawGraph339Codimension
  · exact rawGraph340Codimension
  · exact rawGraph341Codimension
  · exact rawGraph342Codimension
  · exact rawGraph343Codimension
  · exact rawGraph344Codimension
  · exact rawGraph345Codimension
  · exact rawGraph346Codimension
  · exact rawGraph347Codimension
  · exact rawGraph348Codimension
  · exact rawGraph349Codimension
  · exact rawGraph350Codimension
  · exact rawGraph293Codimension
  · exact rawGraph294Codimension
  · exact rawGraph351Codimension
  · exact rawGraph352Codimension
  · exact rawGraph300Codimension
  · exact rawGraph318Codimension
  · exact rawGraph348Codimension
  · exact rawGraph353Codimension
  · exact rawGraph354Codimension
  · exact rawGraph355Codimension
  · exact rawGraph356Codimension
  · exact rawGraph357Codimension
  · exact rawGraph358Codimension
  · exact rawGraph359Codimension
  · exact rawGraph360Codimension
  · exact rawGraph361Codimension
  · exact rawGraph362Codimension
  · exact rawGraph363Codimension
  · exact rawGraph364Codimension
  · exact rawGraph365Codimension
  · exact rawGraph366Codimension
  · exact rawGraph351Codimension
  · exact rawGraph367Codimension
  · exact rawGraph368Codimension
  · exact rawGraph369Codimension
  · exact rawGraph352Codimension
  · exact rawGraph370Codimension
  · exact rawGraph371Codimension
  · exact rawGraph372Codimension

/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/
noncomputable def raw_2_2_degree4 : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret raw_2_2_degree4Columns raw_2_2_degree4Coordinates

/-- Homogeneity in the existing free rational strata module. -/
theorem raw_2_2_degree4_mem_degree : raw_2_2_degree4 ∈ StrataModule.degree 4 :=
  RelationCertificate.interpret_mem_degree
    raw_2_2_degree4Columns raw_2_2_degree4ColumnsCodimension raw_2_2_degree4Coordinates

end AxiomaticGW.AdmcyclesHodgeStrataCandidates
