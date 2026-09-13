import ZFVP.ModelTheory.TwoStepCombinationFilter

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def twoStepImageName (P Q t D : V) : V :=
  {z ∈ twoStepNames Q t ×ˢ P ; ⟨kpair.π₂ z, kpair.π₁ z⟩ₖ ∈ D}

theorem kpair_mem_twoStepImageName (P Q t D σ p : V) :
    ⟨σ, p⟩ₖ ∈ twoStepImageName P Q t D ↔
      σ ∈ twoStepNames Q t ∧ p ∈ P ∧ ⟨p, σ⟩ₖ ∈ D := by
  simp [twoStepImageName, and_assoc]

theorem twoStepImageName_isName {P R Q S t : V} (h : IsForcingIterand P R Q S t) (D : V) :
    IsForcingName P (twoStepImageName P Q t D) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨σ, p, hp, rfl, h.name hσ⟩

noncomputable def twoStepFirstDense (P T D τ : V) : V :=
  {q ∈ P ; ∃ b ∈ D, q = kpair.π₁ b ∧ ∃ s ∈ P, ⟨b, ⟨s, τ⟩ₖ⟩ₖ ∈ T}

theorem twoStepFirstDense_denseBelow {P R Q S t p τ D : V}
    (hR : IsForcingPreorder P R)
    (hD : ForcingDense (twoStepConditions P R Q t) (twoStepOrder P R Q S t) D)
    (hτ : τ ∈ twoStepNames Q t) (hm : p ∈ atomicMembership P R τ Q) :
    ForcingDenseBelow P R (twoStepFirstDense P (twoStepOrder P R Q S t) D τ) p := by
  refine ⟨fun q hq ↦ (mem_sep_iff.mp hq).1, ?_⟩
  intro q hq hqp
  have hqC : ⟨q, τ⟩ₖ ∈ twoStepConditions P R Q t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hq, hτ, atomicMembership_mono hR hm hq hqp⟩
  obtain ⟨b, hbD, hbq⟩ := hD.2 _ hqC
  obtain ⟨r, hr, σ, hσ, rfl, hrσ⟩ := (mem_twoStepConditions _ _ _ _ _).mp (hD.1 b hbD)
  refine ⟨r, mem_sep_iff.mpr ⟨hr, ⟨r, σ⟩ₖ, hbD, by simp, q, hq, hbq⟩, ?_⟩
  simpa using ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hbq).2.2.1

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)
include h

theorem mem_imageName_iff (D : V) (x : A.Model) :
    x ∈ A.ofName ⟨twoStepImageName A.P Q t D, twoStepImageName_isName h D⟩ ↔
      ∃ p : V, ∃ τ : ForcingName A.P, p ∈ A.G ∧ τ.val ∈ twoStepNames Q t ∧
        ⟨p, τ.val⟩ₖ ∈ D ∧ x = A.ofName τ := by
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨τ, p, hp, hτp, he⟩
    obtain ⟨hτ, _, hpτ⟩ := (kpair_mem_twoStepImageName _ _ _ _ _ _).mp hτp
    exact ⟨p, τ, hp, hτ, hpτ, he⟩
  · rintro ⟨p, τ, hp, hτ, hpτ, he⟩
    exact ⟨τ, p, hp, (kpair_mem_twoStepImageName _ _ _ _ _ _).mpr
      ⟨hτ, A.generic.1.1 p hp, hpτ⟩, he⟩

theorem imageName_dense {D : V}
    (hD : ForcingDense (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t) D) :
    ForcingDense (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩)
      (A.ofName ⟨twoStepImageName A.P Q t D, twoStepImageName_isName h D⟩) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨p, τ, hp, _, hpD, rfl⟩ := (mem_imageName_iff A h D x).mp hx
    exact A.ofName_mem_of_forcedMember τ ⟨Q, h.posetName⟩ hp
      (((kpair_mem_twoStepConditions _ _ _ _ _ _).mp (hD.1 _ hpD)).2.2)
  · intro x hx
    obtain ⟨τ, p, hp, hτp, rfl⟩ := (A.mem_ofName_iff ⟨Q, h.posetName⟩ x).mp hx
    have hτN : τ.val ∈ twoStepNames Q t := mem_union_iff.mpr (Or.inl (mem_domain_of_kpair_mem hτp))
    have hm := atomicMembership_of_pair A.order (A.generic.1.1 p hp) hτp
    obtain ⟨q, hq, hqE⟩ := externalForcingGeneric_meets_denseBelow A.order A.generic hp
      (twoStepFirstDense_denseBelow A.order hD hτN hm)
    obtain ⟨_, b, hbD, heq, s, hs, hbs⟩ := mem_sep_iff.mp hqE
    obtain ⟨r, hr, σ, hσ, rfl, hrσ⟩ := (mem_twoStepConditions _ _ _ _ _).mp (hD.1 b hbD)
    simp only [kpair.π₁_kpair] at heq
    subst q
    let ν : ForcingName A.P := ⟨σ, h.name hσ⟩
    refine ⟨A.ofName ν, (mem_imageName_iff A h D _).mpr ⟨r, ν, hq, hσ, hbD, rfl⟩, ?_⟩
    apply A.ofName_pair_mem_of_forced ⟨S, h.orderName⟩ ν τ hq
    simpa using ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hbs).2.2.2

end TwoStepModel
end ZFVP
