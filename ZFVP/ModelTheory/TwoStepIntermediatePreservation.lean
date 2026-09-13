import ZFVP.ModelTheory.TwoStepIntermediate
import ZFVP.ModelTheory.ForcingClosedSequences
import ZFVP.ModelTheory.ProjectionInclusion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R Q S t one : V} (hR : IsForcingPreorder P R)
  (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) {G : Set V}
  (hG : IsExternalForcingGeneric (twoStepConditions P R Q t) (twoStepOrder P R Q S t) G)

noncomputable def twoStepQuotientEmbedding :
    MembershipEndExtension (twoStepTotalContext hR htop h hG).Model
      (twoStepSecondContext hR htop h hG).Model where
  toFun := twoStepQuotientEquiv hR htop h hG
  injective := (twoStepQuotientEquiv hR htop h hG).injective
  mem_iff := twoStepQuotientEquiv_mem_iff hR htop h hG
  endExtension := by
    intro x y hy
    obtain ⟨z, rfl⟩ := (twoStepQuotientEquiv hR htop h hG).surjective y
    exact ⟨z, (twoStepQuotientEquiv_mem_iff hR htop h hG z x).mp hy, rfl⟩

theorem twoStepIntermediate_eq_projection (x : (twoStepFirstContext hR htop h hG).Model) :
    twoStepIntermediateEmbedding hR htop h hG x =
      (twoStepFirstContext hR htop h hG).projectionInclusion (twoStepTotalContext hR htop h hG)
        (twoStep_splitProjection hR htop h) rfl x := by
  apply (twoStepFirstContext hR htop h hG).endExtension_ext
  intro a
  rw [twoStepIntermediateEmbedding_check]
  exact ((twoStepFirstContext hR htop h hG).projectionInclusion_check
    (twoStepTotalContext hR htop h hG) (twoStep_splitProjection hR htop h) rfl a).symm

theorem twoStepIntermediate_function_of_closed
    {γ X : (twoStepFirstContext hR htop h hG).Model} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ →
      IsForcingClosedAt (twoStepSecondContext hR htop h hG).P
        (twoStepSecondContext hR htop h hG).R α)
    {f : (twoStepTotalContext hR htop h hG).Model}
    (hf : f ∈ twoStepIntermediateEmbedding hR htop h hG X ^
      twoStepIntermediateEmbedding hR htop h hG γ) :
    ∃ g ∈ X ^ γ, twoStepIntermediateEmbedding hR htop h hG g = f := by
  let e := twoStepQuotientEquiv hR htop h hG
  let B := twoStepSecondContext hR htop h hG
  have hf' := (twoStepQuotientEmbedding hR htop h hG).function_iff f
    (twoStepIntermediateEmbedding hR htop h hG γ) (twoStepIntermediateEmbedding hR htop h hG X) |>.mpr hf
  change e f ∈ e (twoStepIntermediateEmbedding hR htop h hG X) ^
    e (twoStepIntermediateEmbedding hR htop h hG γ) at hf'
  rw [twoStepQuotientEquiv_intermediate, twoStepQuotientEquiv_intermediate] at hf'
  obtain ⟨g, hg, he⟩ := B.function_eq_check_of_closed hDC hclosed hf'
  refine ⟨g, hg, e.injective ?_⟩
  exact (twoStepQuotientEquiv_intermediate hR htop h hG g).trans he

end ZFVP
