import ZFVP.ModelTheory.UniformNormalizationMaps
import ZFVP.ModelTheory.WoodinRecursionUniform
import ZFVP.ModelTheory.WoodinNormalizedCode

/-! Fixed formulas for the actual normalization recursion and its completed codes.
The recursion formula includes the specified empty value at non-ordinals. -/

set_option maxRecDepth 4096

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def forcingNormalizationDirectMapFormula : SetTheorySemisentence 4 :=
  f“z θ s m. !forcingThreadActionMapFormula z θ m
    (!value.dfn (!forcingCodePFormula (!forcingDirectCodeFormula θ s)) θ)”

@[irreducible] def forcingNormalizationInverseMapFormula : SetTheorySemisentence 4 :=
  f“z θ s m. !forcingThreadActionMapFormula z θ m
    (!value.dfn (!forcingCodePFormula (!forcingInverseCodeFormula θ s)) θ)”

@[irreducible] def woodinNormalizationInitialMapFormula : SetTheorySemisentence 1 :=
  “z. ∃ e, ∃ P, ∃ R, ∃ κ, ∃ c, ∃ Q,
    !isEmpty e ∧ !singleton.dfn P e ∧ !prod.dfn R P P ∧ !woodinSeedCardinalFormula κ ∧
    !woodinPrefixCutoffValueFormula c P R e κ ∧ !saturatedWoodinPrefixPosetNameFormula Q P R e κ c ∧
    !normalizedTwoStepRetractionFormula z P R e c Q”

@[irreducible] def woodinNormalizationSuccessorMapFormula : SetTheorySemisentence 5 :=
  “z k s K m. ∃ A, ∃ B, ∃ t, ∃ P, ∃ R, ∃ o, ∃ κ, ∃ c, ∃ r, ∃ N, ∃ T, ∃ Q,
    !forcingCodePFormula A s ∧ !forcingCodeRFormula B s ∧ !forcingCodetFormula t s ∧
    !value.dfn P A k ∧ !value.dfn R B k ∧ !value.dfn o t k ∧ !value.dfn κ K k ∧
    !woodinPrefixCutoffValueFormula c P R o κ ∧
    !value.dfn r m k ∧ !forcingMapFixedPointsFormula N P r ∧ !forcingOrderRestrictionFormula T N R ∧
    !saturatedWoodinPrefixPosetNameFormula Q P R o κ c ∧
    !normalizedBaseTwoStepMapFormula z P R N T o c Q r”

@[irreducible] def woodinNormalizationInverseMapFormula : SetTheorySemisentence 5 :=
  “z θ s K m. ∃ P, ∃ R, ∃ o, ∃ γ, ∃ c, ∃ r, ∃ N, ∃ T, ∃ Q,
    !forcingInverseCodePosetFormula P θ s ∧ !forcingInverseCodeOrderFormula R θ s ∧
    !forcingInverseCodeTopFormula o θ s ∧ !woodinLimitCardinalFormula γ K ∧
    !forcingInverseSourceCutoffFormula c θ s γ ∧ !forcingNormalizationInverseMapFormula r θ s m ∧
    !forcingMapFixedPointsFormula N P r ∧ !forcingOrderRestrictionFormula T N R ∧
    !saturatedHartogsPosetNameFormula Q P R o γ c ∧ !normalizedBaseTwoStepMapFormula z P R N T o c Q r”

@[irreducible] def woodinNormalizationRuleFormula : SetTheorySemisentence 5 :=
  f“z θ s K m.
    (θ = !isEmpty ∧ !woodinNormalizationInitialMapFormula z) ∨
    (θ ≠ !isEmpty ∧ θ = !succ.dfn (!sUnion.dfn θ) ∧
      !woodinNormalizationSuccessorMapFormula z (!sUnion.dfn θ) s K m) ∨
    (θ ≠ !isEmpty ∧ θ ≠ !succ.dfn (!sUnion.dfn θ) ∧
      !choicelessInaccessibleFormula (!woodinLimitCardinalFormula K) ∧
      !forcingNormalizationDirectMapFormula z θ s m) ∨
    (θ ≠ !isEmpty ∧ θ ≠ !succ.dfn (!sUnion.dfn θ) ∧
      ¬!choicelessInaccessibleFormula (!woodinLimitCardinalFormula K) ∧
      !woodinNormalizationInverseMapFormula z θ s K m)”

@[irreducible] def woodinNormalizationRecursionStepFormula : SetTheorySemisentence 2 :=
  f“z H. !woodinNormalizationRuleFormula z (!domain.dfn H)
    (!woodinIterationPrefixFormula (!domain.dfn H))
    (!woodinIterationCardinalPrefixFormula (!domain.dfn H)) H”

@[irreducible] def woodinNormalizationRecFormula : SetTheorySemisentence 2 :=
  transfiniteRecFormula woodinNormalizationRecursionStepFormula

@[irreducible] def woodinNormalizationHistoryFormula : SetTheorySemisentence 2 :=
  f“H θ. ∀ z, z ∈ H ↔ ∃ i ∈ θ, z = !kpair.dfn i (!woodinNormalizationRecFormula i)”

@[irreducible] def forcingNormalizationCarriersFormula : SetTheorySemisentence 4 :=
  f“N θ s m. ∀ z, z ∈ N ↔ ∃ i ∈ θ,
    z = !kpair.dfn i (!forcingMapFixedPointsFormula (!value.dfn (!forcingCodePFormula s) i) (!value.dfn m i))”

@[irreducible] def forcingNormalizationOrdersFormula : SetTheorySemisentence 4 :=
  f“T θ s m. ∀ z, z ∈ T ↔ ∃ i ∈ θ,
    z = !kpair.dfn i (!forcingOrderRestrictionFormula
      (!value.dfn (!forcingNormalizationCarriersFormula θ s m) i) (!value.dfn (!forcingCodeRFormula s) i))”

@[irreducible] def forcingNormalizationProjectionsFormula : SetTheorySemisentence 4 :=
  f“M θ s m. ∀ w, w ∈ M ↔ ∃ z ∈ !prod.dfn θ θ,
    w = !kpair.dfn z (!restrict.dfn (!value.dfn (!forcingCodeπFormula s) z)
      (!value.dfn (!forcingNormalizationCarriersFormula θ s m) (!kpair.π₂.dfn z)))”

@[irreducible] def forcingNormalizationSectionsFormula : SetTheorySemisentence 4 :=
  f“M θ s m. ∀ w, w ∈ M ↔ ∃ z ∈ !prod.dfn θ θ,
    w = !kpair.dfn z (!restrict.dfn (!value.dfn (!forcingCodeEFormula s) z)
      (!value.dfn (!forcingNormalizationCarriersFormula θ s m) (!kpair.π₁.dfn z)))”

@[irreducible] def forcingMapOnFormula : SetTheorySemisentence 3 :=
  f“g A f. ∀ z, z ∈ g ↔ ∃ p ∈ A, z = !kpair.dfn p (!value.dfn f p)”

@[irreducible] def forcingNormalizationLiftsFormula : SetTheorySemisentence 4 :=
  f“M θ s m. ∀ w, w ∈ M ↔ ∃ z ∈ !prod.dfn θ θ,
    w = !kpair.dfn z (!forcingMapOnFormula
      (!prod.dfn (!value.dfn (!forcingNormalizationCarriersFormula θ s m) (!kpair.π₂.dfn z))
        (!value.dfn (!forcingNormalizationCarriersFormula θ s m) (!kpair.π₁.dfn z)))
      (!value.dfn (!forcingCodeLFormula s) z))”

@[irreducible] def forcingNormalizedCodeFormula : SetTheorySemisentence 4 :=
  f“z θ s m. !forcingIterationCodeFormula z (!forcingNormalizationCarriersFormula θ s m)
    (!forcingNormalizationOrdersFormula θ s m) (!forcingNormalizationProjectionsFormula θ s m)
    (!forcingNormalizationSectionsFormula θ s m) (!forcingNormalizationLiftsFormula θ s m) (!forcingCodetFormula s)”

@[irreducible] def woodinNormalizedPrefixCodeFormula : SetTheorySemisentence 2 :=
  f“z θ. !forcingNormalizedCodeFormula z θ (!woodinIterationPrefixFormula θ) (!woodinNormalizationHistoryFormula θ)”

@[irreducible] def woodinNormalizedStageCodeFormula : SetTheorySemisentence 2 :=
  f“z θ. !forcingNormalizedCodeFormula z (!succ.dfn θ)
    (!kpair.π₁.dfn (!woodinIterationRecFormula θ)) (!woodinNormalizationHistoryFormula (!succ.dfn θ))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingNormalizationDirectMapFormula_defined :
    ℒₛₑₜ-function₃[V] forcingNormalizationDirectMap via forcingNormalizationDirectMapFormula :=
  ⟨fun v ↦ by simp [forcingNormalizationDirectMapFormula, forcingNormalizationDirectMap]⟩

instance forcingNormalizationInverseMapFormula_defined :
    ℒₛₑₜ-function₃[V] forcingNormalizationInverseMap via forcingNormalizationInverseMapFormula :=
  ⟨fun v ↦ by simp [forcingNormalizationInverseMapFormula, forcingNormalizationInverseMap]⟩

instance woodinNormalizationInitialMapFormula_defined :
    ℒₛₑₜ-function₀[V] woodinNormalizationInitialMap via woodinNormalizationInitialMapFormula :=
  ⟨fun v ↦ by simp [woodinNormalizationInitialMapFormula, woodinNormalizationInitialMap,
    isEmpty_iff_eq_empty]⟩

instance woodinNormalizationSuccessorMapFormula_defined :
    ℒₛₑₜ-function₄[V] woodinNormalizationSuccessorMap via woodinNormalizationSuccessorMapFormula :=
  ⟨fun v ↦ by simp [woodinNormalizationSuccessorMapFormula, woodinNormalizationSuccessorMap]⟩

instance woodinNormalizationInverseMapFormula_defined :
    ℒₛₑₜ-function₄[V] woodinNormalizationInverseMap via woodinNormalizationInverseMapFormula :=
  ⟨fun v ↦ by simp [woodinNormalizationInverseMapFormula, woodinNormalizationInverseMap]⟩

instance woodinNormalizationRuleFormula_defined :
    ℒₛₑₜ-function₄[V] woodinNormalizationRule via woodinNormalizationRuleFormula := by
  refine ⟨fun v ↦ ?_⟩
  classical
  simp [woodinNormalizationRuleFormula]
  simp only [← not_isEmpty_iff_isNonempty, isEmpty_iff_eq_empty]
  unfold woodinNormalizationRule
  split_ifs <;> tauto

instance woodinNormalizationRecursionStepFormula_defined :
    ℒₛₑₜ-function₁[V] woodinNormalizationRecursionStep via woodinNormalizationRecursionStepFormula :=
  ⟨fun v ↦ by simp [woodinNormalizationRecursionStepFormula, woodinNormalizationRecursionStep]⟩

instance woodinNormalizationRecFormula_defined :
    ℒₛₑₜ-function₁[V] woodinNormalizationRec via woodinNormalizationRecFormula := by
  unfold woodinNormalizationRecFormula woodinNormalizationRec
  exact transfiniteRecFormula_defined woodinNormalizationRecursionStep woodinNormalizationRecursionStepFormula

instance woodinNormalizationHistoryFormula_defined :
    ℒₛₑₜ-function₁[V] woodinNormalizationHistory via woodinNormalizationHistoryFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [woodinNormalizationHistoryFormula, woodinNormalizationHistory, mem_definableGraph_iff]⟩

instance forcingNormalizationCarriersFormula_defined :
    ℒₛₑₜ-function₃[V] forcingNormalizationCarriers via forcingNormalizationCarriersFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingNormalizationCarriersFormula, forcingNormalizationCarriers, mem_definableGraph_iff]⟩

instance forcingNormalizationOrdersFormula_defined :
    ℒₛₑₜ-function₃[V] forcingNormalizationOrders via forcingNormalizationOrdersFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingNormalizationOrdersFormula, forcingNormalizationOrders, mem_definableGraph_iff]⟩

instance forcingNormalizationProjectionsFormula_defined :
    ℒₛₑₜ-function₃[V] forcingNormalizationProjections via forcingNormalizationProjectionsFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingNormalizationProjectionsFormula, forcingNormalizationProjections, mem_definableGraph_iff]⟩

instance forcingNormalizationSectionsFormula_defined :
    ℒₛₑₜ-function₃[V] forcingNormalizationSections via forcingNormalizationSectionsFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingNormalizationSectionsFormula, forcingNormalizationSections, mem_definableGraph_iff]⟩

instance forcingMapOnFormula_defined : ℒₛₑₜ-function₂[V] forcingMapOn via forcingMapOnFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingMapOnFormula, forcingMapOn, mem_definableGraph_iff]⟩

instance forcingNormalizationLiftsFormula_defined :
    ℒₛₑₜ-function₃[V] forcingNormalizationLifts via forcingNormalizationLiftsFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingNormalizationLiftsFormula, forcingNormalizationLifts, mem_definableGraph_iff]⟩

instance forcingNormalizedCodeFormula_defined :
    ℒₛₑₜ-function₃[V] forcingNormalizedCode via forcingNormalizedCodeFormula :=
  ⟨fun v ↦ by simp [forcingNormalizedCodeFormula, forcingNormalizedCode]⟩

instance woodinNormalizedPrefixCodeFormula_defined :
    ℒₛₑₜ-function₁[V] woodinNormalizedPrefixCode via woodinNormalizedPrefixCodeFormula :=
  ⟨fun v ↦ by simp [woodinNormalizedPrefixCodeFormula, woodinNormalizedPrefixCode]⟩

instance woodinNormalizedStageCodeFormula_defined :
    ℒₛₑₜ-function₁[V] woodinNormalizedStageCode via woodinNormalizedStageCodeFormula :=
  ⟨fun v ↦ by simp [woodinNormalizedStageCodeFormula, woodinNormalizedStageCode]⟩

def woodinNormalizationDictionary : SetFormulaDictionary :=
  [⟨4, forcingNormalizationDirectMapFormula⟩, ⟨4, forcingNormalizationInverseMapFormula⟩,
   ⟨1, woodinNormalizationInitialMapFormula⟩, ⟨5, woodinNormalizationSuccessorMapFormula⟩,
   ⟨5, woodinNormalizationInverseMapFormula⟩, ⟨5, woodinNormalizationRuleFormula⟩,
   ⟨2, woodinNormalizationRecursionStepFormula⟩, ⟨2, woodinNormalizationRecFormula⟩,
   ⟨2, woodinNormalizationHistoryFormula⟩, ⟨4, forcingNormalizationCarriersFormula⟩,
   ⟨4, forcingNormalizationOrdersFormula⟩, ⟨4, forcingNormalizationProjectionsFormula⟩,
   ⟨4, forcingNormalizationSectionsFormula⟩, ⟨3, forcingMapOnFormula⟩,
   ⟨4, forcingNormalizationLiftsFormula⟩, ⟨4, forcingNormalizedCodeFormula⟩,
   ⟨2, woodinNormalizedPrefixCodeFormula⟩, ⟨2, woodinNormalizedStageCodeFormula⟩]

def woodinNormalizationDictionaryBound : ℕ := levyDictionaryBound woodinNormalizationDictionary

theorem woodinNormalizationDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ woodinNormalizationDictionary) (p : LevyPolarity) :
    IsLevyFormula p woodinNormalizationDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
