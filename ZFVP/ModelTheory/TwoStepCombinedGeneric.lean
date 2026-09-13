import ZFVP.ModelTheory.TwoStepDenseImage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)
include h

theorem combined_generic {H : Set A.Model}
    (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H) :
    IsExternalForcingGeneric (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t)
      (twoStepCombinedFilter A Q t H) := by
  refine ⟨combined_filter A h hH.1, ?_⟩
  intro D hD
  obtain ⟨x, hxH, hxD⟩ := hH.2 _ (imageName_dense A h hD)
  obtain ⟨p, τ, hp, hτ, hpD, rfl⟩ := (mem_imageName_iff A h D x).mp hxD
  exact ⟨⟨p, τ.val⟩ₖ, ⟨p, τ, rfl, hD.1 _ hpD, hp, hxH⟩, hpD⟩

theorem combined_first {H : Set A.Model}
    (hH : IsExternalForcingFilter (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H) :
    A.G = forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q t)
      (twoStepCombinedFilter A Q t H) := by
  ext p
  constructor
  · intro hp
    have hpC := twoStep_section_mem A.order A.top h (A.generic.1.1 p hp)
    refine ⟨A.generic.1.1 p hp, ⟨p, t⟩ₖ, ?_, ?_⟩
    · exact ⟨p, ⟨t, h.topName⟩, rfl, hpC, hp, externalForcingFilter_top hH (top A h)⟩
    · rw [twoStepProjection_value hpC, kpair.π₁_kpair]
      exact A.order.2.1 p (A.generic.1.1 p hp)
  · rintro ⟨hp, a, ⟨q, τ, rfl, hc, hq, hτ⟩, hqp⟩
    rw [twoStepProjection_value hc, kpair.π₁_kpair] at hqp
    exact A.generic.1.2.2.1 q hq p hp hqp

theorem combined_second {H : Set A.Model}
    (hH : IsExternalForcingFilter (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H) :
    twoStepSecondFilter A ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ (twoStepCombinedFilter A Q t H) = H := by
  ext x
  constructor
  · rintro ⟨hxQ, p, τ, hp, hτx⟩
    have hτH := ((kpair_mem_twoStepCombinedFilter A Q t p τ H).mp hp).2.2
    exact hH.2.2.1 _ hτH x hxQ hτx
  · intro hxH
    have hxQ := hH.1 x hxH
    obtain ⟨τ, p, hp, hτp, rfl⟩ := (A.mem_ofName_iff ⟨Q, h.posetName⟩ x).mp hxQ
    have hτN : τ.val ∈ twoStepNames Q t := mem_union_iff.mpr (Or.inl (mem_domain_of_kpair_mem hτp))
    have hpC : ⟨p, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t :=
      (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨A.generic.1.1 p hp, hτN,
        atomicMembership_of_pair A.order (A.generic.1.1 p hp) hτp⟩
    exact ⟨hxQ, p, τ, ⟨p, τ, rfl, hpC, hp, hxH⟩, (preorder A h).2.1 _ hxQ⟩

theorem original_combination {G : Set V}
    (hG : IsExternalForcingGeneric (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t) G)
    (hA : A.G = forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q t) G) :
    twoStepCombinedFilter A Q t (twoStepSecondFilter A ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ G) = G := by
  ext a
  constructor
  · rintro ⟨p, τ, rfl, hc, hp, hτ⟩
    exact mem_of_first_second A h hG hA hc hp hτ
  · intro ha
    have hc := hG.1.1 a ha
    obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
    let σ : ForcingName A.P := ⟨τ, h.name hτ⟩
    exact ⟨p, σ, rfl, hc, first_mem A h hG hA (τ := σ) ha,
      value_in_second A h hG hA (τ := σ) ha⟩

noncomputable def combinedContext {H : Set A.Model}
    (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H) :
    ForcingContext V where
  P := twoStepConditions A.P A.R Q t
  R := twoStepOrder A.P A.R Q S t
  one := ⟨A.one, t⟩ₖ
  G := twoStepCombinedFilter A Q t H
  order := twoStep_preorder A.order A.top h
  top := twoStep_top A.order A.top h
  generic := combined_generic A h hH

end TwoStepModel
end ZFVP
