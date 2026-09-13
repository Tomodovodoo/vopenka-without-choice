import ZFVP.ModelTheory.UniformWoodinSparseRecursion
import ZFVP.ModelTheory.UniformWoodinSourceCode
import ZFVP.ModelTheory.WoodinSparseFiniteReflection

/-! A fixed graph formula for the complete actual sparse code captured by
finite reflection. Its checked finite complexity bound is not asserted to be 3. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSparseSourcePrefixCodeFormula : SetTheorySemisentence 2 :=
  f“c θ. !woodinSourceCodeFormula c θ (!woodinSparsePrefixCodeFormula θ)”

def woodinSparseSourceStageCodeFormula : SetTheorySemisentence 2 :=
  f“c θ. !woodinSourceCodeFormula c (!succ.dfn θ) (!woodinSparseStageCodeFormula θ)”

def woodinSparseSourcePrefixCardinalsFormula : SetTheorySemisentence 2 :=
  f“K θ. !woodinSourceCardinalsFormula K θ (!woodinIterationCardinalPrefixFormula θ)”

def woodinSparseSourceStageCardinalsFormula : SetTheorySemisentence 2 :=
  f“K θ. !woodinSourceCardinalsFormula K (!succ.dfn θ) (!kpair.π₂.dfn (!woodinIterationRecFormula θ))”

def woodinSparseCompleteStageCodeFormula : SetTheorySemisentence 2 :=
  f“c θ. c = !kpair.dfn (!woodinSparseSourceStageCodeFormula θ)
    (!woodinSparseSourceStageCardinalsFormula θ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinSparseSourcePrefixCodeFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseSourcePrefixCode via woodinSparseSourcePrefixCodeFormula :=
  ⟨fun v ↦ by simp [woodinSparseSourcePrefixCodeFormula, woodinSparseSourcePrefixCode]⟩

instance woodinSparseSourceStageCodeFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseSourceStageCode via woodinSparseSourceStageCodeFormula :=
  ⟨fun v ↦ by simp [woodinSparseSourceStageCodeFormula, woodinSparseSourceStageCode]⟩

instance woodinSparseSourcePrefixCardinalsFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseSourcePrefixCardinals via woodinSparseSourcePrefixCardinalsFormula :=
  ⟨fun v ↦ by simp [woodinSparseSourcePrefixCardinalsFormula, woodinSparseSourcePrefixCardinals]⟩

instance woodinSparseSourceStageCardinalsFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseSourceStageCardinals via woodinSparseSourceStageCardinalsFormula :=
  ⟨fun v ↦ by simp [woodinSparseSourceStageCardinalsFormula, woodinSparseSourceStageCardinals]⟩

instance woodinSparseCompleteStageCodeFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseCompleteStageCode via woodinSparseCompleteStageCodeFormula :=
  ⟨fun v ↦ by simp [woodinSparseCompleteStageCodeFormula, woodinSparseCompleteStageCode]⟩

theorem eval_woodinSparseCompleteStageCodeFormula (c θ : V) :
    woodinSparseCompleteStageCodeFormula.Evalb ![c, θ] ↔ c = woodinSparseCompleteStageCode θ :=
  Defined.eval_iff (φ := woodinSparseCompleteStageCodeFormula) ![c, θ]

def woodinSparseCompleteCodeDictionary : SetFormulaDictionary :=
  [⟨2, woodinSparsePrefixCodeFormula⟩, ⟨2, woodinSparseStageCodeFormula⟩,
   ⟨2, woodinSparseSourcePrefixCodeFormula⟩, ⟨2, woodinSparseSourceStageCodeFormula⟩,
   ⟨2, woodinSparseSourcePrefixCardinalsFormula⟩, ⟨2, woodinSparseSourceStageCardinalsFormula⟩,
   ⟨2, woodinSparseCompleteStageCodeFormula⟩]

def woodinSparseCompleteCodeDictionaryBound : ℕ := levyDictionaryBound woodinSparseCompleteCodeDictionary

theorem woodinSparseCompleteCodeDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ woodinSparseCompleteCodeDictionary) (p : LevyPolarity) :
    IsLevyFormula p woodinSparseCompleteCodeDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

theorem woodinSparseCompleteStageCodeFormula_complexity (p : LevyPolarity) :
    IsLevyFormula p woodinSparseCompleteCodeDictionaryBound woodinSparseCompleteStageCodeFormula :=
  woodinSparseCompleteCodeDictionary_complexity (by simp [woodinSparseCompleteCodeDictionary]) p

end ZFVP
