import ZFVP.ModelTheory.ForcingQuotientNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingPairName {P : V} (σ τ : ForcingName P) (p : V) (hp : p ∈ P) : ForcingName P :=
  ⟨{⟨σ.val, p⟩ₖ, ⟨τ.val, p⟩ₖ}, forcingName_pair σ.property τ.property hp⟩

theorem forcingQuotient_pairName (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (σ τ : ForcingName P) (p : V) (hpG : p ∈ G)
    (x : ForcingQuotient P R G hR hG.1) :
    x ∈ forcingQuotientMk P R G hR hG.1 (forcingPairName σ τ p (hG.1.1 p hpG)) ↔
      x = forcingQuotientMk P R G hR hG.1 σ ∨ x = forcingQuotientMk P R G hR hG.1 τ := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨ξ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
  rw [forcingQuotientMk_mem_subname_iff P R G hR hG]
  constructor
  · rintro ⟨ν, s, _, hs, he⟩
    have hc : (ν.val = σ.val ∧ s = p) ∨ (ν.val = τ.val ∧ s = p) := by
      simpa only [forcingPairName, mem_insert, mem_singleton_iff, kpair_iff] using hs
    rcases hc with hσ | hτ
    · exact Or.inl (he.trans (congrArg (forcingQuotientMk P R G hR hG.1) (Subtype.ext hσ.1)))
    · exact Or.inr (he.trans (congrArg (forcingQuotientMk P R G hR hG.1) (Subtype.ext hτ.1)))
  · rintro (he | he)
    · exact ⟨σ, p, hpG, by simp [forcingPairName], he⟩
    · exact ⟨τ, p, hpG, by simp [forcingPairName], he⟩

theorem forcingQuotient_pairing (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (x y : ForcingQuotient P R G hR hG.1) :
    ∃ z : ForcingQuotient P R G hR hG.1, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 y
  obtain ⟨p, hpG⟩ := hG.1.2.1
  exact ⟨forcingQuotientMk P R G hR hG.1 (forcingPairName σ τ p (hG.1.1 p hpG)),
    forcingQuotient_pairName P R G hR hG σ τ p hpG⟩

end ZFVP
