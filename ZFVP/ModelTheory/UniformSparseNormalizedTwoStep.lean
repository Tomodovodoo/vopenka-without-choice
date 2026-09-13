import ZFVP.ModelTheory.UniformLeastRankNormalization
import ZFVP.ModelTheory.UniformSparsePair
import ZFVP.ModelTheory.SparseNormalizedTwoStep
import ZFVP.SetTheory.UniformFunctionOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def normalizedTwoStepIsoValueFormula : SetTheorySemisentence 6 :=
  “y A B o f z. ∃ p, ∃ τ, ∃ q, ∃ σ,
    !kpair.π₁.dfn p z ∧ !kpair.π₂.dfn τ z ∧ !value.dfn q f p ∧
    !normalizedIsomorphismNameFormula σ A B o f τ ∧ !kpair.dfn y q σ”

def normalizedTwoStepIsoMapFormula : SetTheorySemisentence 10 :=
  “M P R o δ U A B t f. ∃ C, !normalizedNameTwoStepFormula C P R o δ U ∧
    ∀ w, w ∈ M ↔ ∃ z ∈ C, ∃ y, !normalizedTwoStepIsoValueFormula y A B t f z ∧
      !kpair.dfn w z y”

def sparseNormalizedTwoStepFormula : SetTheorySemisentence 7 :=
  “C a A B o δ U. ∃ W, !normalizedNamePoolFormula W A B o δ U ∧
    !sparsePairCarrierFormula C a A W”

def sparseNormalizedTwoStepOrderFormula : SetTheorySemisentence 8 :=
  “T a A B o δ U S. ∃ W, ∃ C, ∃ N, ∃ O, ∃ f,
    !normalizedNamePoolFormula W A B o δ U ∧
    !sparsePairCarrierFormula C a A W ∧ !prod.dfn N A W ∧
    !nameTwoStepOrderOnFormula O A B S N ∧ !sparsePairDecodeFormula f a A W ∧
    !sparsePullbackOrderFormula T C O f”

def sparseNormalizedTwoStepMapFormula : SetTheorySemisentence 11 :=
  “M a P R o δ U A B t f. ∃ m, ∃ U', ∃ W, ∃ e,
    !normalizedTwoStepIsoMapFormula m P R o δ U A B t f ∧
    !nameActionFormula U' f U ∧ !normalizedNamePoolFormula W A B t δ U' ∧
    !sparsePairEncodeFormula e a A W ∧ !composeFormula M m e”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance normalizedTwoStepIsoValueFormula_defined :
    ℒₛₑₜ-function₅[V] normalizedTwoStepIsoValue via normalizedTwoStepIsoValueFormula :=
  ⟨fun v ↦ by simp [normalizedTwoStepIsoValueFormula, normalizedTwoStepIsoValue]⟩

instance normalizedTwoStepIsoMapFormula_defined :
    Defined (fun v : Fin 10 → V ↦ v 0 = normalizedTwoStepIsoMap
      (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9))
      normalizedTwoStepIsoMapFormula :=
  ⟨fun v ↦ by
    simp [normalizedTwoStepIsoMapFormula]
    rw [mem_ext_iff]
    simp [normalizedTwoStepIsoMap, mem_definableGraph_iff]⟩

instance sparseNormalizedTwoStepFormula_defined :
    Defined (fun v : Fin 7 → V ↦ v 0 = sparseNormalizedTwoStep
      (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) sparseNormalizedTwoStepFormula :=
  ⟨fun v ↦ by simp [sparseNormalizedTwoStepFormula, sparseNormalizedTwoStep]⟩

instance sparseNormalizedTwoStepOrderFormula_defined :
    Defined (fun v : Fin 8 → V ↦ v 0 = sparseNormalizedTwoStepOrder
      (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) sparseNormalizedTwoStepOrderFormula :=
  ⟨fun v ↦ by simp [sparseNormalizedTwoStepOrderFormula,
    sparseNormalizedTwoStepOrder, sparseNormalizedTwoStep, normalizedNameTwoStep]⟩

instance sparseNormalizedTwoStepMapFormula_defined :
    Defined (fun v : Fin 11 → V ↦ v 0 = sparseNormalizedTwoStepMap
      (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10))
      sparseNormalizedTwoStepMapFormula :=
  ⟨fun v ↦ by simp [sparseNormalizedTwoStepMapFormula, sparseNormalizedTwoStepMap]⟩

def sparseNormalizedTwoStepDictionary : SetFormulaDictionary :=
  [⟨6, normalizedTwoStepIsoValueFormula⟩, ⟨10, normalizedTwoStepIsoMapFormula⟩,
   ⟨7, sparseNormalizedTwoStepFormula⟩, ⟨8, sparseNormalizedTwoStepOrderFormula⟩,
   ⟨11, sparseNormalizedTwoStepMapFormula⟩]

def sparseNormalizedTwoStepDictionaryBound : ℕ :=
  levyDictionaryBound sparseNormalizedTwoStepDictionary

theorem sparseNormalizedTwoStepDictionary_complexity {n : ℕ}
    {φ : SetTheorySemisentence n} (hφ : ⟨n, φ⟩ ∈ sparseNormalizedTwoStepDictionary)
    (p : LevyPolarity) : IsLevyFormula p sparseNormalizedTwoStepDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
