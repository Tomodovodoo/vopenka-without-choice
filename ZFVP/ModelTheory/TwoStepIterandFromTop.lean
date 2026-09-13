import ZFVP.ModelTheory.SaturatedEmptyIterand

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem reverseInclusion_empty_iterand_of_top_pair {P R one Q : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one) (hQ : IsForcingName P Q)
    (ht : ⟨one, ∅⟩ₖ ∈ twoStepConditions P R Q ∅) :
    IsForcingIterand P R Q (reverseInclusionOrderName P R Q) ∅ where
  posetName := hQ
  orderName := reverseInclusionOrderName_isName _ _ _
  topName := empty_forcingName P
  preorder := fun _ hp ↦ reverseInclusionOrderName_preorder hR ho hp ⟨Q, hQ⟩
  top := by
    intro p hp
    apply reverseInclusionOrderName_empty_top hR ho hp ⟨Q, hQ⟩
    have hm := ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp ht).2.2
    rw [← forcingFormula_nameMember] at hm ⊢
    exact (forcingFormula_regular hR nameMemberFormula _).2.1 one hm p hp (ho.2 p hp)

end ZFVP
