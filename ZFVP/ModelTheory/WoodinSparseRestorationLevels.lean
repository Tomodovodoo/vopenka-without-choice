import ZFVP.ModelTheory.WoodinSparseFiniteReflection
import ZFVP.SetTheory.CnExtendibleWoodinSupercompact

/-! Finite ground bounds for the complete sparse-code dictionary.
The window complexity `r` and graph formula `code` are explicit syntax inputs.
No forcing formula with endpoint sets as parameters is substituted for `r`.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSparseReflectionLevel (r : ℕ) (code : SetTheorySemisentence 2) : ℕ :=
  2 + listBound (woodinSparseReflectionDictionary r code)

def woodinSparseWitnessBase (r : ℕ) (code : SetTheorySemisentence 2) : ℕ :=
  max (max r woodinSupercompactComplexity.val) (woodinSparseReflectionLevel r code)

def woodinSparseWitnessLevel (r : ℕ) (code : SetTheorySemisentence 2) : ℕ :=
  woodinSparseWitnessBase r code + 2

def woodinSparseCnUnboundedSentence (c : ℕ) : SetTheorySentence :=
  “∀ α, !IsOrdinal.dfn α → ∃ ρ, α ∈ ρ ∧ !(cnFormula c) ρ”

def woodinSparseRestorationBase (r : ℕ) (code : SetTheorySemisentence 2) : ℕ :=
  max (woodinSparseWitnessLevel r code)
    (max (levySyntacticBound (cnExtendibleFormula (woodinSparseWitnessLevel r code)))
      (max (levySyntacticBound (unboundedExtendibilitySentence (woodinSparseWitnessLevel r code)))
        (max (levySyntacticBound (cnFormula (woodinSparseReflectionLevel r code)))
          (levySyntacticBound (woodinSparseCnUnboundedSentence (woodinSparseReflectionLevel r code))))))

def woodinSparseRestorationLevel (r : ℕ) (code : SetTheorySemisentence 2) : ℕ :=
  woodinSparseRestorationBase r code + 4

variable {r : ℕ} {code : SetTheorySemisentence 2}

theorem woodinSparseReflectionLevel_ge_two : 2 ≤ woodinSparseReflectionLevel r code :=
  Nat.le_add_right _ _

theorem woodinSparseDictionary_bound :
    listBound (woodinSparseReflectionDictionary r code) ≤ woodinSparseReflectionLevel r code :=
  Nat.le_add_left _ _

theorem woodinSparseReflectionLevel_le_base :
    woodinSparseReflectionLevel r code ≤ woodinSparseWitnessBase r code := Nat.le_max_right _ _

theorem woodinSparseWindowLevel_le_base : r ≤ woodinSparseWitnessBase r code :=
  (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)

theorem woodinSparseWoodinComplexity_le_base :
    woodinSupercompactComplexity.val ≤ woodinSparseWitnessBase r code :=
  (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)

theorem woodinSparseWitnessLevel_le_restorationBase :
    woodinSparseWitnessLevel r code ≤ woodinSparseRestorationBase r code := Nat.le_max_left _ _

theorem woodinSparseExtendibleFormula_sigma :
    IsSigmaFormula (woodinSparseRestorationBase r code + 1)
      (cnExtendibleFormula (woodinSparseWitnessLevel r code)) :=
  (isLevyFormula_syntacticBound _ .sigma).mono (by unfold woodinSparseRestorationBase; omega)

theorem woodinSparseCnFormula_sigma :
    IsSigmaFormula (woodinSparseRestorationBase r code + 1)
      (cnFormula (woodinSparseReflectionLevel r code)) :=
  (isLevyFormula_syntacticBound _ .sigma).mono (by unfold woodinSparseRestorationBase; omega)

theorem woodinSparseUnboundedExtendibleSentence_sigma :
    IsSigmaFormula (woodinSparseRestorationBase r code + 1)
      (unboundedExtendibilitySentence (woodinSparseWitnessLevel r code)) :=
  (isLevyFormula_syntacticBound _ .sigma).mono (by unfold woodinSparseRestorationBase; omega)

theorem woodinSparseUnboundedCnSentence_sigma :
    IsSigmaFormula (woodinSparseRestorationBase r code + 1)
      (woodinSparseCnUnboundedSentence (woodinSparseReflectionLevel r code)) :=
  (isLevyFormula_syntacticBound _ .sigma).mono (by unfold woodinSparseRestorationBase; omega)

end ZFVP
