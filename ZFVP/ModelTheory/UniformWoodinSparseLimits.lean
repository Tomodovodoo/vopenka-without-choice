import ZFVP.ModelTheory.UniformWoodinSparseSuccessor
import ZFVP.ModelTheory.UniformSparseThread
import ZFVP.ModelTheory.WoodinSparseInverseStage
import ZFVP.ModelTheory.WoodinSparseDirectBase

/-! Uniform syntax for the sparse direct and completed inverse constructors. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSparseBoundsFormula : SetTheorySemisentence 2 :=
  f“b θ. ∀ z, z ∈ b ↔ ∃ i ∈ θ, z = !kpair.dfn i (!succ.dfn (!sparseWoodinSourceIndexFormula i))”

def woodinSparseInverseBaseFormula : SetTheorySemisentence 3 :=
  “C θ c. ∃ b, ∃ P, ∃ U, !woodinSparseBoundsFormula b θ ∧ !forcingCodePFormula P c ∧
    !forcingCodeUniverseFormula U c ∧ !sparseThreadCarrierFormula C θ θ b P U”

def woodinSparseInverseOrderFormula : SetTheorySemisentence 3 :=
  “T θ c. ∃ b, ∃ R, ∃ C, !woodinSparseBoundsFormula b θ ∧ !forcingCodeRFormula R c ∧
    !woodinSparseInverseBaseFormula C θ c ∧ !sparseThreadOrderFormula T θ b R C”

def woodinSparseInverseFlattenFormula : SetTheorySemisentence 3 :=
  “f θ c. ∃ b, ∃ P, ∃ U, !woodinSparseBoundsFormula b θ ∧ !forcingCodePFormula P c ∧
    !forcingCodeUniverseFormula U c ∧ !sparseThreadEncodeFormula f θ b P U”

def woodinSparseDirectBaseFormula : SetTheorySemisentence 3 :=
  f“C θ c. ∀ q, q ∈ C ↔ q ∈ !woodinSparseInverseBaseFormula θ c ∧
    ∃ i ∈ θ, !domain.dfn q ⊆ !succ.dfn (!sparseWoodinSourceIndexFormula i)”

def woodinSparseDirectOrderFormula : SetTheorySemisentence 3 :=
  “T θ c. ∃ b, ∃ R, ∃ C, !woodinSparseBoundsFormula b θ ∧ !forcingCodeRFormula R c ∧
    !woodinSparseDirectBaseFormula C θ c ∧ !sparseThreadOrderFormula T θ b R C”

def sparseThreadFlattenOnFormula : SetTheorySemisentence 2 :=
  f“f D. ∀ z, z ∈ f ↔ ∃ t ∈ D, z = !kpair.dfn t (!sUnion.dfn (!range.dfn t))”

def woodinSparseDirectFlattenFormula : SetTheorySemisentence 3 :=
  “f θ c. ∃ P, ∃ π, ∃ E, ∃ U, ∃ D,
    !forcingCodePFormula P c ∧ !forcingCodeπFormula π c ∧ !forcingCodeEFormula E c ∧
    !forcingCodeUniverseFormula U c ∧ !forcingDirectLimitFormula D θ P π E U ∧
    !sparseThreadFlattenOnFormula f D”

def woodinSparseDirectDecodeFormula : SetTheorySemisentence 3 :=
  “f θ c. ∃ C, ∃ b, !woodinSparseDirectBaseFormula C θ c ∧ !woodinSparseBoundsFormula b θ ∧
    ∀ z, z ∈ f ↔ ∃ q ∈ C, ∃ t, !sparseThreadDecodeValueFormula t θ b q ∧ !kpair.dfn z q t”

def woodinSparseInverseCutoffFormula : SetTheorySemisentence 3 :=
  “δ θ c. ∃ A, ∃ B, ∃ K, ∃ γ, ∃ o, ∃ g, ∃ h,
    !woodinSparseInverseBaseFormula A θ c ∧ !woodinSparseInverseOrderFormula B θ c ∧
    !woodinIterationCardinalPrefixFormula K θ ∧ !woodinLimitCardinalFormula γ K ∧
    !isEmpty o ∧ !checkNameFormula g o γ ∧ !hartogsNumberNameFormula h A B g ∧
    !woodinNamedPrefixCutoffValueFormula δ A B o γ h”

def woodinSparseInversePoolFormula : SetTheorySemisentence 3 :=
  “W θ c. ∃ A, ∃ B, ∃ K, ∃ γ, ∃ δ, ∃ o, ∃ Q,
    !woodinSparseInverseBaseFormula A θ c ∧ !woodinSparseInverseOrderFormula B θ c ∧
    !woodinIterationCardinalPrefixFormula K θ ∧ !woodinLimitCardinalFormula γ K ∧
    !woodinSparseInverseCutoffFormula δ θ c ∧ !isEmpty o ∧
    !saturatedHartogsPosetNameFormula Q A B o γ δ ∧ !normalizedNamePoolFormula W A B o δ Q”

def woodinSparseCompletedInverseCarrierFormula : SetTheorySemisentence 3 :=
  “C θ c. ∃ A, ∃ W, !woodinSparseInverseBaseFormula A θ c ∧
    !woodinSparseInversePoolFormula W θ c ∧ !sparsePairCarrierFormula C θ A W”

def woodinSparseInversePairCarrierFormula : SetTheorySemisentence 3 :=
  “C θ c. ∃ A, ∃ W, !woodinSparseInverseBaseFormula A θ c ∧
    !woodinSparseInversePoolFormula W θ c ∧ !prod.dfn C A W”

def woodinSparseInversePairOrderFormula : SetTheorySemisentence 3 :=
  “T θ c. ∃ A, ∃ B, ∃ K, ∃ γ, ∃ δ, ∃ o, ∃ S, ∃ C,
    !woodinSparseInverseBaseFormula A θ c ∧ !woodinSparseInverseOrderFormula B θ c ∧
    !woodinIterationCardinalPrefixFormula K θ ∧ !woodinLimitCardinalFormula γ K ∧
    !woodinSparseInverseCutoffFormula δ θ c ∧ !isEmpty o ∧
    !saturatedHartogsOrderNameFormula S A B o γ δ ∧
    !woodinSparseInversePairCarrierFormula C θ c ∧ !nameTwoStepOrderOnFormula T A B S C”

def woodinSparseCompletedInverseOrderFormula : SetTheorySemisentence 3 :=
  “T θ c. ∃ A, ∃ W, ∃ C, ∃ O, ∃ f,
    !woodinSparseInverseBaseFormula A θ c ∧ !woodinSparseInversePoolFormula W θ c ∧
    !woodinSparseCompletedInverseCarrierFormula C θ c ∧ !woodinSparseInversePairOrderFormula O θ c ∧
    !sparsePairDecodeFormula f θ A W ∧ !sparsePullbackOrderFormula T C O f”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinSparseBoundsFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseBounds via woodinSparseBoundsFormula :=
  ⟨fun v ↦ by
    change woodinSparseBoundsFormula.Evalb v ↔ v 0 = woodinSparseBounds (v 1)
    rw [mem_ext_iff]
    simp [woodinSparseBoundsFormula, woodinSparseBounds, mem_definableGraph_iff]⟩

instance woodinSparseInverseBaseFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseInverseBase via woodinSparseInverseBaseFormula :=
  ⟨fun v ↦ by simp [woodinSparseInverseBaseFormula, woodinSparseInverseBase]⟩

instance woodinSparseInverseOrderFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseInverseOrder via woodinSparseInverseOrderFormula :=
  ⟨fun v ↦ by simp [woodinSparseInverseOrderFormula, woodinSparseInverseOrder]⟩

instance woodinSparseInverseFlattenFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseInverseFlatten via woodinSparseInverseFlattenFormula :=
  ⟨fun v ↦ by simp [woodinSparseInverseFlattenFormula, woodinSparseInverseFlatten]⟩

instance woodinSparseDirectBaseFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseDirectBase via woodinSparseDirectBaseFormula :=
  ⟨fun v ↦ by
    change woodinSparseDirectBaseFormula.Evalb v ↔ v 0 = woodinSparseDirectBase (v 1) (v 2)
    rw [mem_ext_iff]
    simp [woodinSparseDirectBaseFormula, woodinSparseDirectBase]⟩

instance woodinSparseDirectOrderFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseDirectOrder via woodinSparseDirectOrderFormula :=
  ⟨fun v ↦ by simp [woodinSparseDirectOrderFormula, woodinSparseDirectOrder]⟩

instance sparseThreadFlattenOnFormula_defined :
    ℒₛₑₜ-function₁[V] (fun D ↦ definableGraph D (fun t ↦ ⋃ˢ range t) (by definability))
      via sparseThreadFlattenOnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [sparseThreadFlattenOnFormula, mem_definableGraph_iff]⟩

instance woodinSparseDirectFlattenFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseDirectFlatten via woodinSparseDirectFlattenFormula :=
  ⟨fun v ↦ by simp [woodinSparseDirectFlattenFormula, woodinSparseDirectFlatten]⟩

instance woodinSparseDirectDecodeFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseDirectDecode via woodinSparseDirectDecodeFormula :=
  ⟨fun v ↦ by
    simp [woodinSparseDirectDecodeFormula]
    rw [mem_ext_iff]
    simp [woodinSparseDirectDecode, mem_definableGraph_iff]⟩

instance woodinSparseInverseCutoffFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseInverseCutoff via woodinSparseInverseCutoffFormula :=
  ⟨fun v ↦ by simp [woodinSparseInverseCutoffFormula, woodinSparseInverseCutoff,
    isEmpty_iff_eq_empty]⟩

instance woodinSparseInversePoolFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseInversePool via woodinSparseInversePoolFormula :=
  ⟨fun v ↦ by simp [woodinSparseInversePoolFormula, woodinSparseInversePool,
    isEmpty_iff_eq_empty]⟩

instance woodinSparseCompletedInverseCarrierFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseCompletedInverseCarrier via woodinSparseCompletedInverseCarrierFormula :=
  ⟨fun v ↦ by simp [woodinSparseCompletedInverseCarrierFormula, woodinSparseCompletedInverseCarrier]⟩

instance woodinSparseInversePairCarrierFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseInversePairCarrier via woodinSparseInversePairCarrierFormula :=
  ⟨fun v ↦ by simp [woodinSparseInversePairCarrierFormula, woodinSparseInversePairCarrier]⟩

instance woodinSparseInversePairOrderFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseInversePairOrder via woodinSparseInversePairOrderFormula :=
  ⟨fun v ↦ by simp [woodinSparseInversePairOrderFormula, woodinSparseInversePairOrder,
    isEmpty_iff_eq_empty]⟩

instance woodinSparseCompletedInverseOrderFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseCompletedInverseOrder via woodinSparseCompletedInverseOrderFormula :=
  ⟨fun v ↦ by simp [woodinSparseCompletedInverseOrderFormula, woodinSparseCompletedInverseOrder]⟩

def woodinSparseLimitsDictionary : SetFormulaDictionary :=
  [⟨2, woodinSparseBoundsFormula⟩, ⟨3, woodinSparseInverseBaseFormula⟩,
   ⟨3, woodinSparseInverseOrderFormula⟩, ⟨3, woodinSparseInverseFlattenFormula⟩,
   ⟨3, woodinSparseDirectBaseFormula⟩, ⟨3, woodinSparseDirectOrderFormula⟩,
   ⟨3, woodinSparseDirectFlattenFormula⟩, ⟨3, woodinSparseDirectDecodeFormula⟩,
   ⟨3, woodinSparseInverseCutoffFormula⟩, ⟨3, woodinSparseInversePoolFormula⟩,
   ⟨3, woodinSparseCompletedInverseCarrierFormula⟩, ⟨3, woodinSparseInversePairCarrierFormula⟩,
   ⟨3, woodinSparseInversePairOrderFormula⟩, ⟨3, woodinSparseCompletedInverseOrderFormula⟩]

def woodinSparseLimitsDictionaryBound : ℕ := levyDictionaryBound woodinSparseLimitsDictionary

theorem woodinSparseLimitsDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ woodinSparseLimitsDictionary) (p : LevyPolarity) :
    IsLevyFormula p woodinSparseLimitsDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
