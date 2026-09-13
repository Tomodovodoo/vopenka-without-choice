import ZFVP.ModelTheory.UniformWoodinNormalizationRecursion
import ZFVP.ModelTheory.UniformForcingSparseMaps
import ZFVP.ModelTheory.UniformWoodinSparseLimits
import ZFVP.ModelTheory.WoodinSparseDirectTransport

/-! The actual maps used in the sparse recursion, with fixed syntax. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinNormalizedSuccessorCutoffFormula : SetTheorySemisentence 2 :=
  “δ k. ∃ c, ∃ P, ∃ R, ∃ o, ∃ κ,
    !woodinNormalizedStageCodeFormula c k ∧ !woodinSparseSuccessorParametersFormula P R o κ k c ∧
    !woodinPrefixCutoffValueFormula δ P R o κ”

def woodinRecodedSuccessorMapFormula : SetTheorySemisentence 4 :=
  “f k c m. ∃ s, ∃ P, ∃ R, ∃ o, ∃ κ, ∃ δ, ∃ Q,
    ∃ A, ∃ B, ∃ t, ∃ CP, ∃ CR, ∃ Ct, ∃ r,
    !woodinNormalizedStageCodeFormula s k ∧ !woodinSparseSuccessorParametersFormula P R o κ k s ∧
    !woodinNormalizedSuccessorCutoffFormula δ k ∧ !saturatedWoodinPrefixPosetNameFormula Q P R o κ δ ∧
    !forcingCodePFormula CP c ∧ !forcingCodeRFormula CR c ∧ !forcingCodetFormula Ct c ∧
    !value.dfn A CP k ∧ !value.dfn B CR k ∧ !value.dfn t Ct k ∧ !value.dfn r m k ∧
    !normalizedTwoStepIsoMapFormula f P R o δ Q A B t r”

def woodinSparseSuccessorMapFormula : SetTheorySemisentence 4 :=
  f“f k c m. ∃ r, ∃ a, ∃ P, ∃ W, ∃ e,
    !woodinRecodedSuccessorMapFormula r k c m ∧
    !sparseWoodinSourceIndexFormula a (!succ.dfn k) ∧
    !value.dfn P (!forcingCodePFormula c) k ∧ !woodinSparseSuccessorPoolFormula W k c ∧
    !sparsePairEncodeFormula e a P W ∧ !composeFormula f r e”

def woodinNormalizedInverseBaseFormula : SetTheorySemisentence 2 :=
  “D θ. ∃ N, ∃ s, ∃ P, ∃ π, ∃ U,
    !woodinNormalizedPrefixCodeFormula N θ ∧ !woodinIterationPrefixFormula s θ ∧
    !forcingCodePFormula P N ∧ !forcingCodeπFormula π N ∧ !forcingCodeUniverseFormula U s ∧
    !forcingInverseLimitFormula D θ P π U”

def woodinNormalizedInverseOrderFormula : SetTheorySemisentence 2 :=
  “T θ. ∃ N, ∃ R, ∃ D, !woodinNormalizedPrefixCodeFormula N θ ∧ !forcingCodeRFormula R N ∧
    !woodinNormalizedInverseBaseFormula D θ ∧ !forcingThreadOrderFormula T θ R D”

def woodinNormalizedInverseCutoffFormula : SetTheorySemisentence 2 :=
  “δ θ. ∃ P, ∃ R, ∃ s, ∃ o, ∃ K, ∃ γ, ∃ g, ∃ h,
    !woodinNormalizedInverseBaseFormula P θ ∧ !woodinNormalizedInverseOrderFormula R θ ∧
    !woodinIterationPrefixFormula s θ ∧ !forcingInverseCodeTopFormula o θ s ∧
    !woodinIterationCardinalPrefixFormula K θ ∧ !woodinLimitCardinalFormula γ K ∧
    !checkNameFormula g o γ ∧ !hartogsNumberNameFormula h P R g ∧
    !woodinNamedPrefixCutoffValueFormula δ P R o γ h”

def woodinRecodedInverseBaseMapFormula : SetTheorySemisentence 3 :=
  f“f θ m. !forcingThreadActionMapFormula f θ m (!woodinNormalizedInverseBaseFormula θ)”

def woodinSparseInverseBaseMapFormula : SetTheorySemisentence 4 :=
  f“f θ c m. !composeFormula f (!woodinRecodedInverseBaseMapFormula θ m)
    (!woodinSparseInverseFlattenFormula θ c)”

def woodinSparseInversePairMapFormula : SetTheorySemisentence 4 :=
  “f θ c m. ∃ P, ∃ R, ∃ s, ∃ o, ∃ δ, ∃ K, ∃ γ, ∃ Q, ∃ A, ∃ B, ∃ t, ∃ r,
    !woodinNormalizedInverseBaseFormula P θ ∧ !woodinNormalizedInverseOrderFormula R θ ∧
    !woodinIterationPrefixFormula s θ ∧ !forcingInverseCodeTopFormula o θ s ∧
    !woodinNormalizedInverseCutoffFormula δ θ ∧
    !woodinIterationCardinalPrefixFormula K θ ∧ !woodinLimitCardinalFormula γ K ∧
    !saturatedHartogsPosetNameFormula Q P R o γ δ ∧
    !woodinSparseInverseBaseFormula A θ c ∧ !woodinSparseInverseOrderFormula B θ c ∧
    !isEmpty t ∧ !woodinSparseInverseBaseMapFormula r θ c m ∧
    !normalizedTwoStepIsoMapFormula f P R o δ Q A B t r”

def woodinSparseCompletedInverseMapFormula : SetTheorySemisentence 4 :=
  “f θ c m. ∃ r, ∃ A, ∃ W, ∃ e, !woodinSparseInversePairMapFormula r θ c m ∧
    !woodinSparseInverseBaseFormula A θ c ∧ !woodinSparseInversePoolFormula W θ c ∧
    !sparsePairEncodeFormula e θ A W ∧ !composeFormula f r e”

def woodinRecodedDirectMapFormula : SetTheorySemisentence 4 :=
  “f θ c m. ∃ N, ∃ s, ∃ U,
    !woodinNormalizedPrefixCodeFormula N θ ∧ !woodinIterationPrefixFormula s θ ∧
    !forcingCodeUniverseFormula U s ∧ !forcingRecodedSparseMapFormula f θ N c m U”

def woodinSparseDirectMapFormula : SetTheorySemisentence 4 :=
  f“f θ c m. !composeFormula f
    (!composeFormula (!woodinRecodedDirectMapFormula θ c m)
      (!forcingSparseDecodeFormula θ c (!forcingCodeUniverseFormula c)))
    (!woodinSparseDirectFlattenFormula θ c)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinNormalizedSuccessorCutoffFormula_defined :
    ℒₛₑₜ-function₁[V] woodinNormalizedSuccessorCutoff via woodinNormalizedSuccessorCutoffFormula :=
  ⟨fun v ↦ by simp [woodinNormalizedSuccessorCutoffFormula, woodinNormalizedSuccessorCutoff]⟩

instance woodinRecodedSuccessorMapFormula_defined :
    ℒₛₑₜ-function₃[V] woodinRecodedSuccessorMap via woodinRecodedSuccessorMapFormula :=
  ⟨fun v ↦ by simp [woodinRecodedSuccessorMapFormula, woodinRecodedSuccessorMap]⟩

instance woodinSparseSuccessorMapFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSparseSuccessorMap via woodinSparseSuccessorMapFormula :=
  ⟨fun v ↦ by simp [woodinSparseSuccessorMapFormula, woodinSparseSuccessorMap]⟩

instance woodinNormalizedInverseBaseFormula_defined :
    ℒₛₑₜ-function₁[V] woodinNormalizedInverseBase via woodinNormalizedInverseBaseFormula :=
  ⟨fun v ↦ by simp [woodinNormalizedInverseBaseFormula, woodinNormalizedInverseBase]⟩

instance woodinNormalizedInverseOrderFormula_defined :
    ℒₛₑₜ-function₁[V] woodinNormalizedInverseOrder via woodinNormalizedInverseOrderFormula :=
  ⟨fun v ↦ by simp [woodinNormalizedInverseOrderFormula, woodinNormalizedInverseOrder]⟩

instance woodinNormalizedInverseCutoffFormula_defined :
    ℒₛₑₜ-function₁[V] woodinNormalizedInverseCutoff via woodinNormalizedInverseCutoffFormula :=
  ⟨fun v ↦ by simp [woodinNormalizedInverseCutoffFormula, woodinNormalizedInverseCutoff]⟩

instance woodinRecodedInverseBaseMapFormula_defined :
    ℒₛₑₜ-function₂[V] woodinRecodedInverseBaseMap via woodinRecodedInverseBaseMapFormula :=
  ⟨fun v ↦ by simp [woodinRecodedInverseBaseMapFormula, woodinRecodedInverseBaseMap]⟩

instance woodinSparseInverseBaseMapFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSparseInverseBaseMap via woodinSparseInverseBaseMapFormula :=
  ⟨fun v ↦ by simp [woodinSparseInverseBaseMapFormula, woodinSparseInverseBaseMap]⟩

instance woodinSparseInversePairMapFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSparseInversePairMap via woodinSparseInversePairMapFormula :=
  ⟨fun v ↦ by simp [woodinSparseInversePairMapFormula, woodinSparseInversePairMap, isEmpty_iff_eq_empty]⟩

instance woodinSparseCompletedInverseMapFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSparseCompletedInverseMap via woodinSparseCompletedInverseMapFormula :=
  ⟨fun v ↦ by simp [woodinSparseCompletedInverseMapFormula, woodinSparseCompletedInverseMap]⟩

instance woodinRecodedDirectMapFormula_defined :
    ℒₛₑₜ-function₃[V] woodinRecodedDirectMap via woodinRecodedDirectMapFormula :=
  ⟨fun v ↦ by simp [woodinRecodedDirectMapFormula, woodinRecodedDirectMap]⟩

instance woodinSparseDirectMapFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSparseDirectMap via woodinSparseDirectMapFormula :=
  ⟨fun v ↦ by simp [woodinSparseDirectMapFormula, woodinSparseDirectMap]⟩

def woodinSparseMapsDictionary : SetFormulaDictionary :=
  [⟨2, woodinNormalizedSuccessorCutoffFormula⟩, ⟨4, woodinRecodedSuccessorMapFormula⟩,
   ⟨4, woodinSparseSuccessorMapFormula⟩, ⟨2, woodinNormalizedInverseBaseFormula⟩,
   ⟨2, woodinNormalizedInverseOrderFormula⟩, ⟨2, woodinNormalizedInverseCutoffFormula⟩,
   ⟨3, woodinRecodedInverseBaseMapFormula⟩, ⟨4, woodinSparseInverseBaseMapFormula⟩,
   ⟨4, woodinSparseInversePairMapFormula⟩, ⟨4, woodinSparseCompletedInverseMapFormula⟩,
   ⟨4, woodinRecodedDirectMapFormula⟩, ⟨4, woodinSparseDirectMapFormula⟩]

def woodinSparseMapsDictionaryBound : ℕ := levyDictionaryBound woodinSparseMapsDictionary

theorem woodinSparseMapsDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ woodinSparseMapsDictionary) (p : LevyPolarity) :
    IsLevyFormula p woodinSparseMapsDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
