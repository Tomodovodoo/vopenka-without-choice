import ZFVP.ModelTheory.TwoStepQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R Q S t one : V} (hR : IsForcingPreorder P R)
  (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) {G : Set V}
  (hG : IsExternalForcingGeneric (twoStepConditions P R Q t) (twoStepOrder P R Q S t) G)

/-- The first quotient sits inside the total quotient through the inverse
successive-forcing isomorphism. The end-extension property is proved, rather
than an assumption about an ambient universe containing both quotients. -/
noncomputable def twoStepIntermediateEmbedding :
    MembershipEndExtension (twoStepFirstContext hR htop h hG).Model
      (twoStepTotalContext hR htop h hG).Model where
  toFun := fun x ↦ (twoStepQuotientEquiv hR htop h hG).symm
    ((twoStepSecondContext hR htop h hG).check x)
  injective := (twoStepQuotientEquiv hR htop h hG).symm.injective.comp
    (twoStepSecondContext hR htop h hG).checkEmbedding.injective
  mem_iff := by
    intro x y
    let e := twoStepQuotientEquiv hR htop h hG
    let B := twoStepSecondContext hR htop h hG
    have he := twoStepQuotientEquiv_mem_iff hR htop h hG
      (e.symm (B.check x)) (e.symm (B.check y))
    change e (e.symm (B.check x)) ∈ e (e.symm (B.check y)) ↔ _ at he
    rw [e.apply_symm_apply, e.apply_symm_apply] at he
    exact he.symm.trans (B.check_mem_iff x y)
  endExtension := by
    intro x y hy
    let e := twoStepQuotientEquiv hR htop h hG
    let B := twoStepSecondContext hR htop h hG
    have he := (twoStepQuotientEquiv_mem_iff hR htop h hG y
      (e.symm (B.check x))).mpr hy
    change e y ∈ e (e.symm (B.check x)) at he
    rw [e.apply_symm_apply] at he
    obtain ⟨z, hz, hez⟩ := (B.mem_check_iff x (e y)).mp he
    exact ⟨z, hz, e.injective (hez.trans (e.apply_symm_apply (B.check z)).symm)⟩

theorem twoStepIntermediateEmbedding_check (x : V) :
    twoStepIntermediateEmbedding hR htop h hG ((twoStepFirstContext hR htop h hG).check x) =
      (twoStepTotalContext hR htop h hG).check x := by
  exact (twoStepQuotientEquiv hR htop h hG).symm_apply_eq.mpr
    (twoStepQuotientEquiv_check hR htop h hG x).symm

theorem twoStepQuotientEquiv_intermediate (x : (twoStepFirstContext hR htop h hG).Model) :
    twoStepQuotientEquiv hR htop h hG (twoStepIntermediateEmbedding hR htop h hG x) =
      (twoStepSecondContext hR htop h hG).check x :=
  (twoStepQuotientEquiv hR htop h hG).apply_symm_apply _

end ZFVP
