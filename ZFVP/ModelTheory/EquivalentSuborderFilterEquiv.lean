import ZFVP.ModelTheory.EquivalentSuborderGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def suborderGeneratedFilter (P R : V) (H : Set V) : Set V :=
  {p | p ∈ P ∧ ∃ n ∈ H, ⟨n, p⟩ₖ ∈ R}

theorem suborderGeneratedFilter_filter {P R N S : V} {H : Set V}
    (hR : IsForcingPreorder P R) (hN : N ⊆ P)
    (hrel : ∀ n ∈ N, ∀ m ∈ N, ⟨n, m⟩ₖ ∈ S ↔ ⟨n, m⟩ₖ ∈ R)
    (hH : IsExternalForcingFilter N S H) :
    IsExternalForcingFilter P R (suborderGeneratedFilter P R H) := by
  have hi (n : V) (hn : n ∈ H) : n ∈ suborderGeneratedFilter P R H :=
    ⟨hN n (hH.1 n hn), n, hn, hR.2.1 n (hN n (hH.1 n hn))⟩
  refine ⟨fun _ hp ↦ hp.1, ?_, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hH.2.1
    exact ⟨n, hi n hn⟩
  · intro p hp q hq hpq
    obtain ⟨n, hn, hnp⟩ := hp.2
    exact ⟨hq, n, hn, hR.2.2 n (hN n (hH.1 n hn)) p hp.1 q hq hnp hpq⟩
  · intro p hp q hq
    obtain ⟨n, hn, hnp⟩ := hp.2
    obtain ⟨m, hm, hmq⟩ := hq.2
    obtain ⟨k, hk, hkn, hkm⟩ := hH.2.2.2 n hn m hm
    exact ⟨k, hi k hk,
      hR.2.2 k (hN k (hH.1 k hk)) n (hN n (hH.1 n hn)) p hp.1
        ((hrel k (hH.1 k hk) n (hH.1 n hn)).mp hkn) hnp,
      hR.2.2 k (hN k (hH.1 k hk)) m (hN m (hH.1 m hm)) q hq.1
        ((hrel k (hH.1 k hk) m (hH.1 m hm)).mp hkm) hmq⟩

theorem suborderGeneratedFilter_restrict {P R N S : V} {H : Set V}
    (hR : IsForcingPreorder P R) (hN : N ⊆ P)
    (hrel : ∀ n ∈ N, ∀ m ∈ N, ⟨n, m⟩ₖ ∈ S ↔ ⟨n, m⟩ₖ ∈ R)
    (hH : IsExternalForcingFilter N S H) :
    {p | p ∈ suborderGeneratedFilter P R H ∧ p ∈ N} = H := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨⟨_, n, hn, hnp⟩, hp⟩
    exact hH.2.2.1 n hn p hp ((hrel n (hH.1 n hn) p hp).mpr hnp)
  · intro hp
    have hpN := hH.1 p hp
    exact ⟨⟨hN p hpN, p, hp, hR.2.1 p (hN p hpN)⟩, hpN⟩

theorem suborderGeneratedFilter_generic {P R N S : V} {H : Set V}
    (hR : IsForcingPreorder P R) (hN : N ⊆ P)
    (hrel : ∀ n ∈ N, ∀ m ∈ N, ⟨n, m⟩ₖ ∈ S ↔ ⟨n, m⟩ₖ ∈ R)
    (hrep : ∀ p ∈ P, ∃ n ∈ N, ⟨n, p⟩ₖ ∈ R ∧ ⟨p, n⟩ₖ ∈ R)
    (hH : IsExternalForcingGeneric N S H) :
    IsExternalForcingGeneric P R (suborderGeneratedFilter P R H) := by
  apply (equivalentSuborder_generic_iff hR hN hrel hrep
    (suborderGeneratedFilter_filter hR hN hrel hH.1)).mpr
  rwa [suborderGeneratedFilter_restrict hR hN hrel hH.1]

theorem suborderGeneratedFilter_of_restrict {P R N : V} {G : Set V}
    (hN : N ⊆ P)
    (hrep : ∀ p ∈ P, ∃ n ∈ N, ⟨n, p⟩ₖ ∈ R ∧ ⟨p, n⟩ₖ ∈ R)
    (hG : IsExternalForcingFilter P R G) :
    suborderGeneratedFilter P R {n | n ∈ G ∧ n ∈ N} = G := by
  apply Set.ext
  intro p
  rw [equivalentSuborder_filter_recover hN hrep hG p]
  change (p ∈ P ∧ ∃ n, (n ∈ G ∧ n ∈ N) ∧ ⟨n, p⟩ₖ ∈ R) ↔ _
  simp only [and_assoc]

noncomputable def equivalentSuborderGenericsEquiv {P R N S : V}
    (hR : IsForcingPreorder P R) (hN : N ⊆ P)
    (hrel : ∀ n ∈ N, ∀ m ∈ N, ⟨n, m⟩ₖ ∈ S ↔ ⟨n, m⟩ₖ ∈ R)
    (hrep : ∀ p ∈ P, ∃ n ∈ N, ⟨n, p⟩ₖ ∈ R ∧ ⟨p, n⟩ₖ ∈ R) :
    {G : Set V // IsExternalForcingGeneric P R G} ≃ {H : Set V // IsExternalForcingGeneric N S H} where
  toFun G := ⟨{n | n ∈ G.val ∧ n ∈ N}, (equivalentSuborder_generic_iff hR hN hrel hrep G.property.1).mp G.property⟩
  invFun H := ⟨suborderGeneratedFilter P R H.val, suborderGeneratedFilter_generic hR hN hrel hrep H.property⟩
  left_inv G := Subtype.ext (suborderGeneratedFilter_of_restrict hN hrep G.property.1)
  right_inv H := Subtype.ext (suborderGeneratedFilter_restrict hR hN hrel H.property.1)

end ZFVP
