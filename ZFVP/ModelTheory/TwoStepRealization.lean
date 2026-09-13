import ZFVP.ModelTheory.TwoStepCombinedGeneric
import ZFVP.ModelTheory.ForcingModelEvaluation
import ZFVP.ModelTheory.ForcingModelGeneric
import ZFVP.ModelTheory.ForcingRealizationEmbedding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)
  {H : Set A.Model}
  (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H)

noncomputable def iterandContext : ForcingContext A.Model where
  P := A.ofName ⟨Q, h.posetName⟩
  R := A.ofName ⟨S, h.orderName⟩
  one := A.ofName ⟨t, h.topName⟩
  G := H
  order := preorder A h
  top := top A h
  generic := hH

noncomputable def successiveGround : MembershipEndExtension V (iterandContext A h hH).Model where
  toFun := fun x ↦ (iterandContext A h hH).check (A.check x)
  injective := fun x y he ↦ (A.check_eq_iff x y).mp
    (((iterandContext A h hH).check_eq_iff _ _).mp he)
  mem_iff := fun x y ↦ ((iterandContext A h hH).check_mem_iff _ _).trans (A.check_mem_iff x y)
  endExtension := by
    intro x y hy
    obtain ⟨z, hz, rfl⟩ := ((iterandContext A h hH).mem_check_iff (A.check x) y).mp hy
    obtain ⟨a, ha, rfl⟩ := (A.mem_check_iff x z).mp hz
    exact ⟨a, ha, rfl⟩

noncomputable def internalGeneric : (iterandContext A h hH).Model :=
  let B := iterandContext A h hH
  let f := A.evaluationGraph (twoStepNames Q t) (fun _ hσ ↦ h.name hσ)
  {a ∈ B.check (A.check (twoStepConditions A.P A.R Q t)) ;
    kpair.π₁ a ∈ B.check A.genericSet ∧ (B.check f) ‘ (kpair.π₂ a) ∈ B.genericSet}

theorem internalGeneric_subset : internalGeneric A h hH ⊆
    (iterandContext A h hH).check (A.check (twoStepConditions A.P A.R Q t)) := by
  intro a ha
  unfold internalGeneric at ha
  exact (mem_sep_iff.mp ha).1

theorem internalGeneric_pair_iff (p : V) (τ : ForcingName A.P)
    (hc : ⟨p, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t) :
    successiveGround A h hH ⟨p, τ.val⟩ₖ ∈ internalGeneric A h hH ↔
      p ∈ A.G ∧ A.ofName τ ∈ H := by
  let B := iterandContext A h hH
  let f := A.evaluationGraph (twoStepNames Q t) (fun _ hσ ↦ h.name hσ)
  have hτN := ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hc).2.1
  have hdom : A.check τ.val ∈ domain f := by
    rw [A.evaluationGraph_domain]
    exact (A.check_mem_iff _ _).mpr hτN
  have hval : (B.check f) ‘ (B.check (A.check τ.val)) = B.check (A.ofName τ) := by
    rw [B.check_value hdom, A.evaluationGraph_value _ _ _ hτN]
  change B.check (A.check ⟨p, τ.val⟩ₖ) ∈
    {a ∈ B.check (A.check (twoStepConditions A.P A.R Q t)) ;
      kpair.π₁ a ∈ B.check A.genericSet ∧ (B.check f) ‘ (kpair.π₂ a) ∈ B.genericSet} ↔ _
  have hc' : B.check (A.check ⟨p, τ.val⟩ₖ) ∈ B.check (A.check (twoStepConditions A.P A.R Q t)) :=
    (B.check_mem_iff _ _).mpr ((A.check_mem_iff _ _).mpr hc)
  rw [mem_sep_iff]
  simp only [hc', true_and]
  simp only [A.check_kpair, B.check_kpair, kpair.π₁_kpair, kpair.π₂_kpair, hval,
    B.check_mem_iff, A.check_mem_genericSet_iff, B.check_mem_genericSet_iff]
  rfl

theorem internalGeneric_mem_iff (a : V) :
    successiveGround A h hH a ∈ internalGeneric A h hH ↔ a ∈ twoStepCombinedFilter A Q t H := by
  constructor
  · intro ha
    have hc' := internalGeneric_subset A h hH _ ha
    have hc : a ∈ twoStepConditions A.P A.R Q t :=
      (A.check_mem_iff _ _).mp (((iterandContext A h hH).check_mem_iff _ _).mp hc')
    obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
    let σ : ForcingName A.P := ⟨τ, h.name hτ⟩
    have hh := (internalGeneric_pair_iff A h hH p σ hc).mp ha
    exact ⟨p, σ, rfl, hc, hh.1, hh.2⟩
  · rintro ⟨p, τ, rfl, hc, hp, hτ⟩
    exact (internalGeneric_pair_iff A h hH p τ hc).mpr ⟨hp, hτ⟩

noncomputable def combinedRealization : ForcingRealization (combinedContext A h hH) (iterandContext A h hH).Model where
  ground := successiveGround A h hH
  genericSet := internalGeneric A h hH
  generic_subset := internalGeneric_subset A h hH
  generic_mem := internalGeneric_mem_iff A h hH

noncomputable def combinedEmbedding : MembershipEndExtension (combinedContext A h hH).Model
    (iterandContext A h hH).Model := (combinedRealization A h hH).embedding

end TwoStepModel
end ZFVP
