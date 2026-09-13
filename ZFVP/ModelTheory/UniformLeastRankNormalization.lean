import ZFVP.ModelTheory.NormalizedIsomorphismNames
import ZFVP.SetTheory.UniformRank
import ZFVP.SetTheory.NameRecursionDictionary
import ZFVP.SetTheory.LevyComplexityBound

/-! Explicit formulas for the actual least-rank normalization. Every formula
is declared before the ambient model and uses only fixed syntax. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingScottRelatedFormula : SetTheorySemisentence 5 :=
  f“P R p τ σ. !forcingNameFormula P σ ∧ p ∈ !atomicEqualityFormula P R τ σ”

def forcingLeastNameFamilyFormula : SetTheorySemisentence 5 :=
  f“X P R p τ. ∀ σ, σ ∈ X ↔
    σ ∈ !hierarchyFormula (!succ.dfn (!rankFormula τ)) ∧
    !forcingScottRelatedFormula P R p τ σ ∧
    ∀ ν, !forcingScottRelatedFormula P R p τ ν → !rankFormula σ ⊆ !rankFormula ν”

def forcingLeastRankNameFormula : SetTheorySemisentence 5 :=
  f“z P R p τ. z = !sUnion.dfn (!forcingLeastNameFamilyFormula P R p τ)”

def normalizedNamePoolFormula : SetTheorySemisentence 6 :=
  f“C P R o δ Q. ∀ τ, τ ∈ C ↔ τ ∈ !hierarchyFormula δ ∧
    !forcingNameFormula P τ ∧ !forcingLeastRankNameFormula τ P R o τ ∧
    o ∈ !atomicMembershipFormula P R τ Q”

def normalizedNameTwoStepFormula : SetTheorySemisentence 6 :=
  “C P R o δ Q. ∃ W, !normalizedNamePoolFormula W P R o δ Q ∧ !prod.dfn C P W”

def normalizedIsomorphismNameFormula : SetTheorySemisentence 6 :=
  f“z Q S o f τ. !forcingLeastRankNameFormula z Q S o (!nameActionFormula f τ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingScottRelatedFormula_defined :
    Defined (fun v : Fin 5 → V ↦ ForcingScottRelated (v 0) (v 1) (v 2) (v 3) (v 4))
      forcingScottRelatedFormula :=
  ⟨fun v ↦ by simp [forcingScottRelatedFormula, ForcingScottRelated]⟩

instance forcingLeastNameFamilyFormula_defined :
    ℒₛₑₜ-function₄[V] forcingLeastNameFamily via forcingLeastNameFamilyFormula :=
  ⟨fun v ↦ by
    change forcingLeastNameFamilyFormula.Evalb v ↔
      v 0 = forcingLeastNameFamily (v 1) (v 2) (v 3) (v 4)
    rw [mem_ext_iff]
    simp [forcingLeastNameFamilyFormula, forcingLeastNameFamily]⟩

instance forcingLeastRankNameFormula_defined :
    ℒₛₑₜ-function₄[V] forcingLeastRankName via forcingLeastRankNameFormula :=
  ⟨fun v ↦ by simp [forcingLeastRankNameFormula, forcingLeastRankName]⟩

instance normalizedNamePoolFormula_defined :
    ℒₛₑₜ-function₅[V] normalizedNamePool via normalizedNamePoolFormula :=
  ⟨fun v ↦ by
    change normalizedNamePoolFormula.Evalb v ↔
      v 0 = normalizedNamePool (v 1) (v 2) (v 3) (v 4) (v 5)
    rw [mem_ext_iff]
    simp [normalizedNamePoolFormula, normalizedNamePool, eq_comm]⟩

instance normalizedNameTwoStepFormula_defined :
    ℒₛₑₜ-function₅[V] normalizedNameTwoStep via normalizedNameTwoStepFormula :=
  ⟨fun v ↦ by simp [normalizedNameTwoStepFormula, normalizedNameTwoStep]⟩

instance normalizedIsomorphismNameFormula_defined :
    ℒₛₑₜ-function₅[V] normalizedIsomorphismName via normalizedIsomorphismNameFormula :=
  ⟨fun v ↦ by simp [normalizedIsomorphismNameFormula, normalizedIsomorphismName]⟩

def leastRankNormalizationDictionary : SetFormulaDictionary :=
  [⟨5, forcingScottRelatedFormula⟩, ⟨5, forcingLeastNameFamilyFormula⟩,
   ⟨5, forcingLeastRankNameFormula⟩, ⟨6, normalizedNamePoolFormula⟩,
   ⟨6, normalizedNameTwoStepFormula⟩, ⟨6, normalizedIsomorphismNameFormula⟩]

def leastRankNormalizationDictionaryBound : ℕ :=
  levyDictionaryBound leastRankNormalizationDictionary

theorem leastRankNormalizationDictionary_complexity {n : ℕ}
    {φ : SetTheorySemisentence n} (hφ : ⟨n, φ⟩ ∈ leastRankNormalizationDictionary)
    (p : LevyPolarity) : IsLevyFormula p leastRankNormalizationDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
