import ZFVP.ModelTheory.ForcingGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Restricting a filter to a suborder containing an equivalent representative
of every condition preserves genericity in both directions. -/
theorem equivalentSuborder_generic_iff {P R N S : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hN : N ⊆ P)
    (hrel : ∀ n ∈ N, ∀ m ∈ N, ⟨n, m⟩ₖ ∈ S ↔ ⟨n, m⟩ₖ ∈ R)
    (hrep : ∀ p ∈ P, ∃ n ∈ N, ⟨n, p⟩ₖ ∈ R ∧ ⟨p, n⟩ₖ ∈ R)
    (hG : IsExternalForcingFilter P R G) :
    IsExternalForcingGeneric P R G ↔
      IsExternalForcingGeneric N S {n | n ∈ G ∧ n ∈ N} := by
  have hfilter : IsExternalForcingFilter N S {n | n ∈ G ∧ n ∈ N} := by
    refine ⟨fun _ hn ↦ hn.2, ?_, ?_, ?_⟩
    · obtain ⟨p, hp⟩ := hG.2.1
      obtain ⟨n, hn, _, hpn⟩ := hrep p (hG.1 p hp)
      exact ⟨n, hG.2.2.1 p hp n (hN n hn) hpn, hn⟩
    · intro n hn m hm hnm
      exact ⟨hG.2.2.1 n hn.1 m (hN m hm) ((hrel n hn.2 m hm).mp hnm), hm⟩
    · intro n hn m hm
      obtain ⟨p, hp, hpn, hpm⟩ := hG.2.2.2 n hn.1 m hm.1
      obtain ⟨k, hk, hkp, hpk⟩ := hrep p (hG.1 p hp)
      exact ⟨k, ⟨hG.2.2.1 p hp k (hN k hk) hpk, hk⟩,
        (hrel k hk n hn.2).mpr (hR.2.2 k (hN k hk) p (hG.1 p hp) n (hN n hn.2) hkp hpn),
        (hrel k hk m hm.2).mpr (hR.2.2 k (hN k hk) p (hG.1 p hp) m (hN m hm.2) hkp hpm)⟩
  constructor
  · intro hg
    refine ⟨hfilter, ?_⟩
    intro D hD
    have hd : ForcingDense P R D := by
      refine ⟨SetTheory.subset_trans hD.1 hN, ?_⟩
      intro p hp
      obtain ⟨n, hn, hnp, _⟩ := hrep p hp
      obtain ⟨d, hd, hdn⟩ := hD.2 n hn
      exact ⟨d, hd, hR.2.2 d (hN d (hD.1 d hd)) n (hN n hn) p hp
        ((hrel d (hD.1 d hd) n hn).mp hdn) hnp⟩
    obtain ⟨d, hdG, hdD⟩ := hg.2 D hd
    exact ⟨d, ⟨hdG, hD.1 d hdD⟩, hdD⟩
  · intro hg
    refine ⟨hG, ?_⟩
    intro D hD
    let E := {n ∈ N ; ∃ d ∈ D, ⟨n, d⟩ₖ ∈ R}
    have hE : ForcingDense N S E := by
      refine ⟨sep_subset, ?_⟩
      intro n hn
      obtain ⟨d, hd, hdn⟩ := hD.2 n (hN n hn)
      obtain ⟨k, hk, hkd, _⟩ := hrep d (hD.1 d hd)
      exact ⟨k, mem_sep_iff.mpr ⟨hk, d, hd, hkd⟩,
        (hrel k hk n hn).mpr (hR.2.2 k (hN k hk) d (hD.1 d hd) n (hN n hn) hkd hdn)⟩
    obtain ⟨n, hn, hnE⟩ := hg.2 E hE
    obtain ⟨d, hd, hnd⟩ := (mem_sep_iff.mp hnE).2
    exact ⟨d, hG.2.2.1 n hn.1 d (hD.1 d hd) hnd, hd⟩

theorem equivalentSuborder_filter_recover {P R N : V} {G : Set V}
    (hN : N ⊆ P)
    (hrep : ∀ p ∈ P, ∃ n ∈ N, ⟨n, p⟩ₖ ∈ R ∧ ⟨p, n⟩ₖ ∈ R)
    (hG : IsExternalForcingFilter P R G) (p : V) :
    p ∈ G ↔ p ∈ P ∧ ∃ n ∈ G, n ∈ N ∧ ⟨n, p⟩ₖ ∈ R := by
  constructor
  · intro hp
    obtain ⟨n, hn, hnp, hpn⟩ := hrep p (hG.1 p hp)
    exact ⟨hG.1 p hp, n, hG.2.2.1 p hp n (hN n hn) hpn, hn, hnp⟩
  · rintro ⟨hp, n, hn, _, hnp⟩
    exact hG.2.2.1 n hn p hp hnp

end ZFVP
