import ZFVP.SetTheory.TwoStepForcing
import ZFVP.ModelTheory.ForcingProjection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def twoStepProjection (P R Q t : V) : V :=
  definableGraph (twoStepConditions P R Q t) kpair.π₁ (by definability)

theorem twoStepProjection_value {P R Q t a : V} (ha : a ∈ twoStepConditions P R Q t) :
    (twoStepProjection P R Q t) ‘ a = kpair.π₁ a := value_definableGraph _ _ _ ha

theorem twoStepProjection_maps (P R Q t : V) :
    twoStepProjection P R Q t ∈ P ^ twoStepConditions P R Q t := by
  apply definableGraph_mem_function_of_mapsTo
  intro a ha
  obtain ⟨p, hp, τ, _, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
  simpa using hp

theorem twoStep_below_section {P R Q S t one a p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t)
    (ha : a ∈ twoStepConditions P R Q t) (hp : p ∈ P) :
    ⟨a, ⟨p, t⟩ₖ⟩ₖ ∈ twoStepOrder P R Q S t ↔ ⟨kpair.π₁ a, p⟩ₖ ∈ R := by
  constructor
  · intro hr
    simpa using ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hr).2.2.1
  · intro hr
    obtain ⟨q, hq, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
    apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
    refine ⟨ha, twoStep_section_mem hR htop h hp, ?_, ?_⟩
    · simpa using hr
    · simpa using forcedTop_above hR htop hq ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩
        ⟨t, h.topName⟩ ⟨τ, h.name hτ⟩ (h.top q hq) hm

theorem twoStep_projection {P R Q S t one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) :
    IsForcingProjection P R (twoStepConditions P R Q t) (twoStepOrder P R Q S t)
      (twoStepProjection P R Q t) := by
  refine ⟨twoStepProjection_maps _ _ _ _, ?_, ?_⟩
  · intro a ha b hb hab
    rw [twoStepProjection_value ha, twoStepProjection_value hb]
    exact ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hab).2.2.1
  · intro a ha p hp hpa
    obtain ⟨q, hq, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
    rw [twoStepProjection_value ha, kpair.π₁_kpair] at hpa
    have hpm := atomicMembership_mono hR hm hp hpa
    have hr : ⟨p, τ⟩ₖ ∈ twoStepConditions P R Q t :=
      (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp, hτ, hpm⟩
    refine ⟨⟨p, τ⟩ₖ, hr, ?_, ?_⟩
    · apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
      refine ⟨hr, ha, ?_, ?_⟩
      · simpa using hpa
      · simpa using forcedPreorder_refl hR htop hp ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩
          ⟨τ, h.name hτ⟩ (h.preorder p hp) hpm
    · rw [twoStepProjection_value hr, kpair.π₁_kpair]

theorem twoStep_projected_generic {P R Q S t one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) {G : Set V}
    (hG : IsExternalForcingGeneric (twoStepConditions P R Q t) (twoStepOrder P R Q S t) G) :
    IsExternalForcingGeneric P R (forcingProjectionGeneric P R (twoStepProjection P R Q t) G) :=
  (twoStep_projection hR htop h).generic hR hG

theorem twoStep_projected_generic_iff_section {P R Q S t one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t)
    {G : Set V} (hG : IsExternalForcingFilter (twoStepConditions P R Q t) (twoStepOrder P R Q S t) G) :
    p ∈ forcingProjectionGeneric P R (twoStepProjection P R Q t) G ↔ ⟨p, t⟩ₖ ∈ G := by
  constructor
  · rintro ⟨hp, a, ha, hap⟩
    have haC := hG.1 a ha
    rw [twoStepProjection_value haC] at hap
    exact hG.2.2.1 a ha _ (twoStep_section_mem hR htop h hp)
      ((twoStep_below_section hR htop h haC hp).mpr hap)
  · intro hpG
    have hpC := hG.1 _ hpG
    have hp := ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hpC).1
    refine ⟨hp, ⟨p, t⟩ₖ, hpG, ?_⟩
    rw [twoStepProjection_value hpC, kpair.π₁_kpair]
    exact hR.2.1 p hp

end ZFVP
