import ZFVP.ModelTheory.ForcingProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R Q S u : V}

def forcingProjectionPreimage (P u : V) (H : Set V) : Set V := {p | p ∈ P ∧ u ‘ p ∈ H}

theorem IsForcingProjection.image_member_iff
    (hu : IsForcingProjection Q S P R u)
    (hreflect : ∀ p ∈ P, ∀ q ∈ P, ⟨u ‘ p, u ‘ q⟩ₖ ∈ S → ⟨p, q⟩ₖ ∈ R)
    (hS : IsForcingPreorder Q S) {G : Set V} (hG : IsExternalForcingFilter P R G)
    {p : V} (hp : p ∈ P) : u ‘ p ∈ forcingProjectionGeneric Q S u G ↔ p ∈ G := by
  constructor
  · rintro ⟨_, q, hq, hqp⟩
    exact hG.2.2.1 q hq p hp (hreflect q (hG.1 q hq) p hp hqp)
  · intro hpG
    exact hu.image_mem hS hG hpG

theorem IsForcingProjection.preimage_filter
    (hu : IsForcingProjection Q S P R u)
    (hreflect : ∀ p ∈ P, ∀ q ∈ P, ⟨u ‘ p, u ‘ q⟩ₖ ∈ S → ⟨p, q⟩ₖ ∈ R)
    (hsurj : ∀ q ∈ Q, ∃ p ∈ P, u ‘ p = q)
    {H : Set V} (hH : IsExternalForcingFilter Q S H) :
    IsExternalForcingFilter P R (forcingProjectionPreimage P u H) := by
  refine ⟨fun _ hp ↦ hp.1, ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hH.2.1
    obtain ⟨p, hp, he⟩ := hsurj q (hH.1 q hq)
    exact ⟨p, hp, he.symm ▸ hq⟩
  · intro p hp q hq hpq
    exact ⟨hq, hH.2.2.1 _ hp.2 _ (function_value_mem hu.maps hq) (hu.monotone p hp.1 q hq hpq)⟩
  · intro p hp q hq
    obtain ⟨r, hr, hrp, hrq⟩ := hH.2.2.2 _ hp.2 _ hq.2
    obtain ⟨s, hs, he⟩ := hsurj r (hH.1 r hr)
    exact ⟨s, ⟨hs, he.symm ▸ hr⟩, hreflect s hs p hp.1 (he.symm ▸ hrp),
      hreflect s hs q hq.1 (he.symm ▸ hrq)⟩

theorem IsForcingProjection.preimage_generic
    (hu : IsForcingProjection Q S P R u)
    (hreflect : ∀ p ∈ P, ∀ q ∈ P, ⟨u ‘ p, u ‘ q⟩ₖ ∈ S → ⟨p, q⟩ₖ ∈ R)
    (hsurj : ∀ q ∈ Q, ∃ p ∈ P, u ‘ p = q)
    {H : Set V} (hH : IsExternalForcingGeneric Q S H) :
    IsExternalForcingGeneric P R (forcingProjectionPreimage P u H) := by
  refine ⟨hu.preimage_filter hreflect hsurj hH.1, ?_⟩
  intro D hD
  let E := {q ∈ Q; ∃ p ∈ D, q = u ‘ p}
  have hE : ForcingDense Q S E := by
    refine ⟨fun _ hq ↦ (mem_sep_iff.mp hq).1, ?_⟩
    intro q hq
    obtain ⟨p, hp, he⟩ := hsurj q hq
    obtain ⟨d, hd, hdp⟩ := hD.2 p hp
    refine ⟨u ‘ d, mem_sep_iff.mpr ⟨function_value_mem hu.maps (hD.1 d hd), d, hd, rfl⟩, ?_⟩
    rw [← he]
    exact hu.monotone d (hD.1 d hd) p hp hdp
  obtain ⟨q, hq, hqE⟩ := hH.2 E hE
  obtain ⟨p, hp, he⟩ := (mem_sep_iff.mp hqE).2
  exact ⟨p, ⟨hD.1 p hp, he ▸ hq⟩, hp⟩

theorem IsForcingProjection.preimage_image
    (hu : IsForcingProjection Q S P R u)
    (hreflect : ∀ p ∈ P, ∀ q ∈ P, ⟨u ‘ p, u ‘ q⟩ₖ ∈ S → ⟨p, q⟩ₖ ∈ R)
    (hS : IsForcingPreorder Q S) {G : Set V} (hG : IsExternalForcingFilter P R G) :
    forcingProjectionPreimage P u (forcingProjectionGeneric Q S u G) = G := by
  ext p
  constructor
  · intro hp
    exact (hu.image_member_iff hreflect hS hG hp.1).mp hp.2
  · intro hp
    exact ⟨hG.1 p hp, (hu.image_member_iff hreflect hS hG (hG.1 p hp)).mpr hp⟩

theorem IsForcingProjection.image_preimage
    (hu : IsForcingProjection Q S P R u)
    (hsurj : ∀ q ∈ Q, ∃ p ∈ P, u ‘ p = q)
    (hS : IsForcingPreorder Q S) {H : Set V} (hH : IsExternalForcingFilter Q S H) :
    forcingProjectionGeneric Q S u (forcingProjectionPreimage P u H) = H := by
  ext q
  constructor
  · rintro ⟨hq, p, hp, hpq⟩
    exact hH.2.2.1 _ hp.2 q hq hpq
  · intro hq
    obtain ⟨p, hp, he⟩ := hsurj q (hH.1 q hq)
    exact ⟨hH.1 q hq, p, ⟨hp, he.symm ▸ hq⟩, he.symm ▸ hS.2.1 q (hH.1 q hq)⟩

end ZFVP
