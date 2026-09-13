import ZFVP.ModelTheory.TwoStepSecondFilter
import ZFVP.ModelTheory.TwoStepDenseNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def twoStepDensePreimage (P R Q t D : V) : V :=
  {a ∈ twoStepConditions P R Q t ; kpair.π₁ a ∈ atomicMembership P R (kpair.π₂ a) D}

theorem twoStepDensePreimage_denseBelow {P R Q S t one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) (D : ForcingName P) (hp : p ∈ P)
    (hD : p ∈ forcingFormula P R forcingDenseFormula (standardTuple ![Q, S, D.val])) :
    ForcingDenseBelow (twoStepConditions P R Q t) (twoStepOrder P R Q S t)
      (twoStepDensePreimage P R Q t D.val) ⟨p, t⟩ₖ := by
  refine ⟨fun a ha ↦ (mem_sep_iff.mp ha).1, ?_⟩
  intro a ha hap
  have hqp := (twoStep_below_section hR htop h ha hp).mp hap
  obtain ⟨q, hq, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
  simp only [kpair.π₁_kpair] at hqp
  have hqD := (forcingFormula_regular hR forcingDenseFormula _).2.1 p hD q hq hqp
  obtain ⟨r, hr, σ, hσ, hrq, hrQ, hrD, hrτ⟩ :=
    twoStep_dense_names hR htop ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ D
      ⟨τ, h.name hτ⟩ hq hqD hm q hq (hR.2.1 q hq)
  have hσN : σ ∈ twoStepNames Q t := by
    exact mem_union_iff.mpr (Or.inl hσ)
  have hb : ⟨r, σ⟩ₖ ∈ twoStepConditions P R Q t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hr, hσN, hrQ⟩
  refine ⟨⟨r, σ⟩ₖ, ?_, ?_⟩
  · apply mem_sep_iff.mpr
    exact ⟨hb, by simpa using hrD⟩
  · apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
    exact ⟨hb, ha, by simpa using hrq, by simpa using hrτ⟩

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t) {G : Set V}
  (hG : IsExternalForcingGeneric (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t) G)
  (hA : A.G = forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q t) G)
include h hG hA

set_option maxHeartbeats 200000 in
theorem second_generic : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩)
    (A.ofName ⟨S, h.orderName⟩)
    (twoStepSecondFilter A ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ G) := by
  refine ⟨second_filter A h hG hA, ?_⟩
  intro D hD
  obtain ⟨δ, rfl⟩ := A.ofName_surjective D
  have he : forcingDenseFormula.Evalb (fun i ↦ A.ofName (![⟨Q, h.posetName⟩, ⟨S, h.orderName⟩, δ] i)) :=
    (Defined.eval_iff _).mpr hD
  obtain ⟨p, hp, hf⟩ := (A.formula_truth forcingDenseFormula ![⟨Q, h.posetName⟩, ⟨S, h.orderName⟩, δ]).mp he
  have hpProj : p ∈ forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q t) G := by
    rw [← hA]
    exact hp
  have hp' : ⟨p, t⟩ₖ ∈ G :=
    (twoStep_projected_generic_iff_section A.order A.top h hG.1).mp hpProj
  have hd := twoStepDensePreimage_denseBelow A.order A.top h δ (A.generic.1.1 p hp) hf
  obtain ⟨a, haG, haD⟩ := externalForcingGeneric_meets_denseBelow
    (twoStep_preorder A.order A.top h) hG hp' hd
  have ha := hG.1.1 a haG
  obtain ⟨q, hq, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
  let σ : ForcingName A.P := ⟨τ, h.name hτ⟩
  refine ⟨A.ofName σ, value_in_second A h hG hA (τ := σ) haG, ?_⟩
  apply A.ofName_mem_of_forcedMember σ δ (first_mem A h hG hA (τ := σ) haG)
  simpa using (mem_sep_iff.mp haD).2

end TwoStepModel
end ZFVP
