import ZFVP.ModelTheory.ForcingPredense

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Inclusion preserving order, reflecting compatibility, and preserving predense
sets restricts external generic filters. -/
theorem externalForcingGeneric_restrict_of_predense {P R Q S : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hPQ : P ⊆ Q)
    (hord : ∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R → ⟨p, q⟩ₖ ∈ S)
    (hcomp : ∀ p ∈ P, ∀ q ∈ P,
      ForcingCompatible Q S p q → ForcingCompatible P R p q)
    (hpre : ∀ D : V, D ⊆ P → (∀ p ∈ P, ∃ d ∈ D, ForcingCompatible P R p d) →
      ∀ q ∈ Q, ∃ d ∈ D, ForcingCompatible Q S q d)
    (hG : IsExternalForcingGeneric Q S G) :
    IsExternalForcingGeneric P R {p | p ∈ G ∧ p ∈ P} := by
  classical
  have hmeet (D : V) (hD : ForcingDense P R D) : ∃ p ∈ G, p ∈ D := by
    apply externalForcingGeneric_meets_predense hG (fun p hp ↦ hPQ p (hD.1 p hp))
    apply hpre D hD.1
    intro p hp
    obtain ⟨d, hd, hdp⟩ := hD.2 p hp
    exact ⟨d, hd, d, hD.1 d hd, hdp, hR.2.1 d (hD.1 d hd)⟩
  refine ⟨⟨fun p hp ↦ hp.2, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨p, hpG, hp⟩ := hmeet P ⟨fun _ hp ↦ hp, fun p hp ↦ ⟨p, hp, hR.2.1 p hp⟩⟩
    exact ⟨p, hpG, hp⟩
  · intro p hp q hq hpq
    exact ⟨hG.1.2.2.1 p hp.1 q (hPQ q hq) (hord p hp.2 q hq hpq), hq⟩
  · intro p hp q hq
    let D := {r ∈ P ; ¬ForcingCompatible P R r p ∨ ¬ForcingCompatible P R r q ∨
      (⟨r, p⟩ₖ ∈ R ∧ ⟨r, q⟩ₖ ∈ R)}
    have hD : ForcingDense P R D := by
      refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
      intro r hr
      by_cases hrp : ForcingCompatible P R r p
      · obtain ⟨s, hs, hsr, hsp⟩ := hrp
        by_cases hsq : ForcingCompatible P R s q
        · obtain ⟨t, ht, hts, htq⟩ := hsq
          exact ⟨t, mem_sep_iff.mpr ⟨ht, Or.inr (Or.inr
            ⟨hR.2.2 t ht s hs p hp.2 hts hsp, htq⟩)⟩,
            hR.2.2 t ht s hs r hr hts hsr⟩
        · exact ⟨s, mem_sep_iff.mpr ⟨hs, Or.inr (Or.inl hsq)⟩, hsr⟩
      · exact ⟨r, mem_sep_iff.mpr ⟨hr, Or.inl hrp⟩, hR.2.1 r hr⟩
    obtain ⟨r, hrG, hrD⟩ := hmeet D hD
    obtain ⟨hr, hcase⟩ := mem_sep_iff.mp hrD
    rcases hcase with hrp | hrq | ⟨hrp, hrq⟩
    · exact False.elim (hrp (hcomp r hr p hp.2 (externalForcingFilter_compatible hG.1 hrG hp.1)))
    · exact False.elim (hrq (hcomp r hr q hq.2 (externalForcingFilter_compatible hG.1 hrG hq.1)))
    · exact ⟨r, ⟨hrG, hr⟩, hrp, hrq⟩
  · intro D hD
    obtain ⟨p, hpG, hpD⟩ := hmeet D hD
    exact ⟨p, ⟨hpG, hD.1 p hpD⟩, hpD⟩

end ZFVP
