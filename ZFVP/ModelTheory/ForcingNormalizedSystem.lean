import ZFVP.ModelTheory.ForcingNormalizedCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s m : V} [IsOrdinal θ]
  (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
local notation "N" => forcingNormalizationCarriers θ s m
local notation "T" => forcingNormalizationOrders θ s m
local notation "π" => forcingNormalizationProjections θ s m
local notation "E" => forcingNormalizationSections θ s m

include h hs

theorem forcingNormalized_split : IsSplitForcingSystem θ N π E := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij p hp
    rw [forcingNormalizationProjections_apply h hs hi hj hij hp]
    exact h.projection_mem hs hi hj hij hp
  · intro i hi j hj hij p hp
    rw [forcingNormalizationSections_apply h hs hi hj hij hp]
    exact h.section_mem hs hi hj hij hp
  · intro i hi p hp
    rw [forcingNormalizationSections_apply h hs hi hi (subset_refl _) hp,
      hs.system.split.secId i hi p (h.inclusion i hi p hp)]
  · intro i hi j hj k hk hij hjk p hp
    have hik : i ⊆ k := fun x hx ↦ hjk x (hij x hx)
    rw [forcingNormalizationProjections_apply h hs hj hk hjk hp,
      forcingNormalizationProjections_apply h hs hi hj hij (h.projection_mem hs hj hk hjk hp),
      forcingNormalizationProjections_apply h hs hi hk hik hp,
      hs.system.split.projComp i hi j hj k hk hij hjk p (h.inclusion k hk p hp)]
  · intro i hi j hj k hk hij hjk p hp
    have hik : i ⊆ k := fun x hx ↦ hjk x (hij x hx)
    rw [forcingNormalizationSections_apply h hs hi hj hij hp,
      forcingNormalizationSections_apply h hs hj hk hjk (h.section_mem hs hi hj hij hp),
      forcingNormalizationSections_apply h hs hi hk hik hp,
      hs.system.split.secComp i hi j hj k hk hij hjk p (h.inclusion i hi p hp)]
  · intro i hi j hj hij p hp
    rw [forcingNormalizationSections_apply h hs hi hj hij hp,
      forcingNormalizationProjections_apply h hs hi hj hij (h.section_mem hs hi hj hij hp),
      hs.system.split.retraction i hi j hj hij p (h.inclusion i hi p hp)]

theorem forcingNormalized_order : IsOrderedSplitForcingSystem θ N T π E := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [forcingNormalizationOrders_value hi]
    exact forcingOrderRestriction_preorder (hs.system.order.preorder i hi) (h.inclusion i hi)
  · intro i hi j hj hij p hp q hq hpq
    rw [forcingNormalizationOrders_value hj] at hpq
    rw [forcingNormalizationProjections_apply h hs hi hj hij hp,
      forcingNormalizationProjections_apply h hs hi hj hij hq, forcingNormalizationOrders_value hi]
    exact (pair_mem_forcingOrderRestriction _ _ _ _).mpr ⟨h.projection_mem hs hi hj hij hp,
      h.projection_mem hs hi hj hij hq, hs.system.order.projMono i hi j hj hij
        p (h.inclusion j hj p hp) q (h.inclusion j hj q hq)
          ((pair_mem_forcingOrderRestriction _ _ _ _).mp hpq).2.2⟩
  · intro i hi j hj hij p hp q hq
    rw [forcingNormalizationSections_apply h hs hi hj hij hq,
      forcingNormalizationProjections_apply h hs hi hj hij hp,
      forcingNormalizationOrders_value hi, forcingNormalizationOrders_value hj]
    simp only [pair_mem_forcingOrderRestriction, hp, hq, h.section_mem hs hi hj hij hq,
      h.projection_mem hs hi hj hij hp, true_and]
    exact hs.system.order.below i hi j hj hij p (h.inclusion j hj p hp) q (h.inclusion i hi q hq)

theorem forcingNormalized_functions : IsFunctionalSplitForcingSystem θ N π E := by
  constructor
  · intro i hi j hj hij
    have hf := hs.system.functions.projection i hi j hj hij
    let := IsFunction.of_mem hf
    rw [forcingNormalizationProjections_value hi hj]
    apply restrict_mem_function_of_values
    · rw [domain_eq_of_mem_function hf]
      exact h.inclusion j hj
    · intro p hp
      exact h.projection_mem hs hi hj hij hp
  · intro i hi j hj hij
    have hf := hs.system.functions.sectionMap i hi j hj hij
    let := IsFunction.of_mem hf
    rw [forcingNormalizationSections_value hi hj]
    apply restrict_mem_function_of_values
    · rw [domain_eq_of_mem_function hf]
      exact h.inclusion i hi
    · intro p hp
      exact h.section_mem hs hi hj hij hp

omit [IsOrdinal θ] in
theorem forcingNormalized_top_mem {i : V} (hi : i ∈ θ) : (forcingCodet s) ‘ i ∈ N ‘ i := by
  rw [forcingNormalizationCarriers_value hi]
  exact mem_sep_iff.mpr ⟨(hs.system.tops.top i hi).1, h.fixesTop i hi⟩

omit [IsOrdinal θ] in
theorem forcingNormalized_tops : IsToppedSplitForcingSystem θ N T π E (forcingCodet s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    refine ⟨forcingNormalized_top_mem h hs hi, ?_⟩
    intro p hp
    rw [forcingNormalizationOrders_value hi]
    exact (pair_mem_forcingOrderRestriction _ _ _ _).mpr
      ⟨hp, forcingNormalized_top_mem h hs hi, (hs.system.tops.top i hi).2 p (h.inclusion i hi p hp)⟩
  · intro i hi j hj hij
    rw [forcingNormalizationProjections_apply h hs hi hj hij (forcingNormalized_top_mem h hs hj),
      hs.system.tops.projTop i hi j hj hij]
  · intro i hi j hj hij
    rw [forcingNormalizationSections_apply h hs hi hj hij (forcingNormalized_top_mem h hs hi),
      hs.system.tops.secTop i hi j hj hij]

variable (hL : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
  ∀ a ∈ (forcingNormalizationCarriers θ s m) ‘ j,
  ∀ b ∈ (forcingNormalizationCarriers θ s m) ‘ i,
  ⟨b, ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ a⟩ₖ ∈ (forcingCodeR s) ‘ i →
  ((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ ∈ (forcingNormalizationCarriers θ s m) ‘ j)

include hL

theorem forcingNormalized_lifts :
    IsCoherentForcingLift θ N T π (forcingNormalizationLifts θ s m) := by
  constructor
  · intro i hi j hj hij a ha b hb hle
    rw [forcingNormalizationProjections_apply h hs hi hj hij ha,
      forcingNormalizationOrders_value hi] at hle
    have hleP := ((pair_mem_forcingOrderRestriction _ _ _ _).mp hle).2.2
    have hl := hs.system.lifts.lift i hi j hj hij a (h.inclusion j hj a ha)
      b (h.inclusion i hi b hb) hleP
    have hlN := hL i hi j hj hij a ha b hb hleP
    rw [forcingNormalizationLifts_apply hi hj ha hb]
    refine ⟨hlN, ?_, ?_⟩
    · rw [forcingNormalizationOrders_value hj]
      exact (pair_mem_forcingOrderRestriction _ _ _ _).mpr ⟨hlN, ha, hl.2.1⟩
    · rw [forcingNormalizationProjections_apply h hs hi hj hij hlN]
      exact hl.2.2
  · intro i hi j hj k hk hij hjk a ha b hb hle
    have hik : i ⊆ k := fun x hx ↦ hjk x (hij x hx)
    rw [forcingNormalizationProjections_apply h hs hi hk hik ha,
      forcingNormalizationOrders_value hi] at hle
    have hleP := ((pair_mem_forcingOrderRestriction _ _ _ _).mp hle).2.2
    rw [forcingNormalizationLifts_apply hi hk ha hb,
      forcingNormalizationProjections_apply h hs hj hk hjk (hL i hi k hk hik a ha b hb hleP),
      forcingNormalizationProjections_apply h hs hj hk hjk ha,
      forcingNormalizationLifts_apply hi hj (h.projection_mem hs hj hk hjk ha) hb]
    exact hs.system.lifts.commute i hi j hj k hk hij hjk a (h.inclusion k hk a ha)
      b (h.inclusion i hi b hb) hleP

omit [IsOrdinal θ] in
theorem forcingNormalized_compatible :
    IsSectionCompatibleForcingLift θ N T π E (forcingNormalizationLifts θ s m) := by
  constructor
  intro i hi k hk j hj hik hkj a ha b hb hle
  rw [forcingNormalizationProjections_apply h hs hi hk hik ha,
    forcingNormalizationOrders_value hi] at hle
  have hleP := ((pair_mem_forcingOrderRestriction _ _ _ _).mp hle).2.2
  rw [forcingNormalizationSections_apply h hs hk hj hkj ha,
    forcingNormalizationLifts_apply hi hj (h.section_mem hs hk hj hkj ha) hb,
    forcingNormalizationLifts_apply hi hk ha hb,
    forcingNormalizationSections_apply h hs hk hj hkj (hL i hi k hk hik a ha b hb hleP)]
  exact hs.system.compatible.compatible i hi k hk j hj hik hkj a (h.inclusion k hk a ha)
    b (h.inclusion i hi b hb) hleP

/-- Prefix-replacement closure is the additional obligation beyond normalization. -/
theorem forcingNormalized_system : IsForcingIterationSystem θ N T π E
    (forcingNormalizationLifts θ s m) (forcingCodet s) :=
  ⟨forcingNormalized_split h hs, forcingNormalized_order h hs,
    forcingNormalized_functions h hs, forcingNormalized_tops h hs,
    forcingNormalized_lifts h hs hL, forcingNormalized_compatible h hs hL⟩

theorem forcingNormalized_code : IsForcingIterationCode θ (forcingNormalizedCode θ s m) := by
  unfold forcingNormalizedCode
  constructor <;> simp only [forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code,
    forcingCodeE_code, forcingCodeL_code, forcingCodet_code]
  · exact forcingNormalized_system h hs hL
  · unfold forcingNormalizationCarriers
    exact ⟨inferInstance, domain_definableGraph _ _ _⟩
  · unfold forcingNormalizationOrders
    exact ⟨inferInstance, domain_definableGraph _ _ _⟩
  · unfold forcingNormalizationProjections
    exact ⟨inferInstance, domain_definableGraph _ _ _⟩
  · unfold forcingNormalizationSections
    exact ⟨inferInstance, domain_definableGraph _ _ _⟩
  · unfold forcingNormalizationLifts
    exact ⟨inferInstance, domain_definableGraph _ _ _⟩
  · exact hs.tablet

end ZFVP
