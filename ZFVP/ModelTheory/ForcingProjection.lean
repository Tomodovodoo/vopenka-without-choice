import ZFVP.SetTheory.ForcingRetraction
import ZFVP.ModelTheory.ForcingGeneric

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A monotone projection with exact lifting of stronger target conditions. -/
structure IsForcingProjection (P R Q S π : V) : Prop where
  maps : π ∈ P ^ Q
  monotone : ∀ p ∈ Q, ∀ q ∈ Q, ⟨p, q⟩ₖ ∈ S → ⟨π ‘ p, π ‘ q⟩ₖ ∈ R
  lift : ∀ q ∈ Q, ∀ p ∈ P, ⟨p, π ‘ q⟩ₖ ∈ R →
    ∃ r ∈ Q, ⟨r, q⟩ₖ ∈ S ∧ π ‘ r = p

theorem IsForcingRetraction.projection {P R Q S π : V} (h : IsForcingRetraction P R Q S π) :
    IsForcingProjection P R Q S π := ⟨h.maps, h.monotone, h.lift⟩

/-- The upward closure of the projected generic filter. -/
def forcingProjectionGeneric (P R π : V) (G : Set V) : Set V :=
  {p | p ∈ P ∧ ∃ q ∈ G, ⟨π ‘ q, p⟩ₖ ∈ R}

theorem IsForcingProjection.image_mem {P R Q S π : V} (h : IsForcingProjection P R Q S π)
    (hR : IsForcingPreorder P R) {G : Set V} (hG : IsExternalForcingFilter Q S G)
    {q : V} (hq : q ∈ G) : π ‘ q ∈ forcingProjectionGeneric P R π G := by
  have hp := function_value_mem h.maps (hG.1 q hq)
  exact ⟨hp, q, hq, hR.2.1 _ hp⟩

theorem IsForcingProjection.filter {P R Q S π : V} (h : IsForcingProjection P R Q S π)
    (hR : IsForcingPreorder P R) {G : Set V} (hG : IsExternalForcingFilter Q S G) :
    IsExternalForcingFilter P R (forcingProjectionGeneric P R π G) := by
  refine ⟨fun p hp ↦ hp.1, ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hG.2.1
    exact ⟨π ‘ q, h.image_mem hR hG hq⟩
  · intro p hp r hr hpr
    obtain ⟨q, hq, hqp⟩ := hp.2
    exact ⟨hr, q, hq, hR.2.2 _ (function_value_mem h.maps (hG.1 q hq)) p hp.1 r hr hqp hpr⟩
  · intro p hp r hr
    obtain ⟨q, hq, hqp⟩ := hp.2
    obtain ⟨s, hs, hsr⟩ := hr.2
    obtain ⟨t, ht, htq, hts⟩ := hG.2.2.2 q hq s hs
    have htP := function_value_mem h.maps (hG.1 t ht)
    refine ⟨π ‘ t, h.image_mem hR hG ht, ?_, ?_⟩
    · exact hR.2.2 _ htP _ (function_value_mem h.maps (hG.1 q hq)) p hp.1
        (h.monotone t (hG.1 t ht) q (hG.1 q hq) htq) hqp
    · exact hR.2.2 _ htP _ (function_value_mem h.maps (hG.1 s hs)) r hr.1
        (h.monotone t (hG.1 t ht) s (hG.1 s hs) hts) hsr

theorem IsForcingProjection.dense_preimage {P R Q S π D : V}
    (h : IsForcingProjection P R Q S π) (hD : ForcingDense P R D) :
    ForcingDense Q S {q ∈ Q ; π ‘ q ∈ D} := by
  refine ⟨fun q hq ↦ (mem_sep_iff.mp hq).1, ?_⟩
  intro q hq
  obtain ⟨p, hpD, hpq⟩ := hD.2 _ (function_value_mem h.maps hq)
  obtain ⟨r, hr, hrq, he⟩ := h.lift q hq p (hD.1 p hpD) hpq
  exact ⟨r, mem_sep_iff.mpr ⟨hr, he.symm ▸ hpD⟩, hrq⟩

theorem IsForcingProjection.generic {P R Q S π : V} (h : IsForcingProjection P R Q S π)
    (hR : IsForcingPreorder P R) {G : Set V} (hG : IsExternalForcingGeneric Q S G) :
    IsExternalForcingGeneric P R (forcingProjectionGeneric P R π G) := by
  refine ⟨h.filter hR hG.1, ?_⟩
  intro D hD
  obtain ⟨q, hq, hqD⟩ := hG.2 _ (h.dense_preimage hD)
  exact ⟨π ‘ q, h.image_mem hR hG.1 hq, (mem_sep_iff.mp hqD).2⟩

end ZFVP
