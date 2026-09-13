import ZFVP.ModelTheory.ForcingNormalizationFamily
import ZFVP.ModelTheory.WoodinNormalizationInitial

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinNormalizationInitial_family {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    IsForcingNormalizationFamily (succ ∅) (woodinInitialCode : V) woodinNormalizationInitial := by
  have hzero : ∀ i ∈ succ (∅ : V), i = ∅ := by
    intro i hi
    simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
  refine ⟨woodinNormalizationInitial_table, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain rfl := hzero i hi
    rw [woodinNormalizationInitial_value]
    have hr := woodinNormalizationInitial_retraction hΩ
    obtain ⟨_, _, _, hI⟩ := woodinNormalizationInitial_inputs hΩ
    have ht := normalizedNameTwoStep_preorder
      (δ := woodinPrefixCutoff ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal)
      (singletonForcing_preorder (∅ : V))
      (singletonForcing_top ∅) hI.posetName hI.orderName hI.preorder
    rw [hr.fixedPoints_eq, hr.orderRestriction_eq ht]
    exact hr
  · intro i hi p hp
    obtain rfl := hzero i hi
    rw [woodinNormalizationInitial_value]
    exact woodinNormalizationInitial_equivalent hΩ hp
  · intro i hi
    obtain rfl := hzero i hi
    rw [woodinNormalizationInitial_value]
    exact woodinNormalizationInitial_top hΩ
  · intro j hj i hij
    obtain rfl := hzero j hj
    exact (not_mem_empty hij).elim
  · intro i hi j hj _ p hp
    obtain rfl := hzero i hi
    obtain rfl := hzero j hj
    rw [woodinNormalizationInitial_value]
    exact woodinNormalizationInitial_section_coherent hΩ hp

end ZFVP
