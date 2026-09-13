import ZFVP.SetTheory.AtomicMembership
import ZFVP.SetTheory.AtomicEqualityTransitivity

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicMembership_subst_left {P R σ σ' τ p : V} (hR : IsForcingPreorder P R)
    (he : p ∈ atomicEquality P R σ σ') (hm : p ∈ atomicMembership P R σ τ) :
    p ∈ atomicMembership P R σ' τ := by
  obtain ⟨hp, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hm
  apply (mem_atomicMembership_iff _ _ _ _ _).mpr
  refine ⟨hp, ?_⟩
  intro q hq hqp
  obtain ⟨r, hr, hrq, ν, s, hs, hrs, hσν⟩ := hh q hq hqp
  have hσ'σ : r ∈ atomicEquality P R σ' σ := atomicEquality_symm P R σ σ' ▸
    atomicEquality_mono hR he hr (hR.2.2 r hr q hq p hp hrq hqp)
  exact ⟨r, hr, hrq, ν, s, hs, hrs, atomicEquality_trans hR σ' σ ν r hσ'σ hσν⟩

theorem atomicMembership_subst_right {P R σ τ τ' p : V} (hR : IsForcingPreorder P R)
    (he : p ∈ atomicEquality P R τ τ') (hm : p ∈ atomicMembership P R σ τ) :
    p ∈ atomicMembership P R σ τ' := by
  obtain ⟨hp, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hm
  obtain ⟨_, hl, _⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp he
  apply (mem_atomicMembership_iff _ _ _ _ _).mpr
  refine ⟨hp, ?_⟩
  intro q hq hqp
  obtain ⟨r, hr, hrq, ν, s, hs, hrs, hσν⟩ := hh q hq hqp
  obtain ⟨v, hv, hvr, υ, t, ht, hvt, hνυ⟩ := hl ν s hs r hr
    (hR.2.2 r hr q hq p hp hrq hqp) hrs
  exact ⟨v, hv, hR.2.2 v hv r hr q hq hvr hrq, υ, t, ht, hvt,
    atomicEquality_trans hR σ ν υ v (atomicEquality_mono hR hσν hv hvr) hνυ⟩

theorem atomicEquality_membership_iff {P R σ τ p : V} (hR : IsForcingPreorder P R)
    (he : p ∈ atomicEquality P R σ τ) (υ : V) :
    (p ∈ atomicMembership P R σ υ ↔ p ∈ atomicMembership P R τ υ) ∧
    (p ∈ atomicMembership P R υ σ ↔ p ∈ atomicMembership P R υ τ) := by
  have he' : p ∈ atomicEquality P R τ σ := atomicEquality_symm P R σ τ ▸ he
  exact ⟨⟨atomicMembership_subst_left hR he, atomicMembership_subst_left hR he'⟩,
    ⟨atomicMembership_subst_right hR he, atomicMembership_subst_right hR he'⟩⟩

theorem atomicEquality_iff_membership (P R σ τ p : V) (hR : IsForcingPreorder P R) :
    p ∈ atomicEquality P R σ τ ↔ p ∈ P ∧
      (∀ υ s, ⟨υ, s⟩ₖ ∈ σ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R →
        q ∈ atomicMembership P R υ τ) ∧
      (∀ ν t, ⟨ν, t⟩ₖ ∈ τ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, t⟩ₖ ∈ R →
        q ∈ atomicMembership P R ν σ) := by
  rw [mem_atomicEquality_iff]
  constructor
  · rintro ⟨hp, hl, hr⟩
    refine ⟨hp, ?_, ?_⟩
    · intro υ s hs q hq hqp hqs
      apply (mem_atomicMembership_iff _ _ _ _ _).mpr
      refine ⟨hq, ?_⟩
      intro r hrP hrq
      exact hl υ s hs r hrP (hR.2.2 r hrP q hq p hp hrq hqp)
        (hR.2.2 r hrP q hq s (forcingOrder_right_mem hR hqs) hrq hqs)
    · intro ν t ht q hq hqp hqt
      apply (mem_atomicMembership_iff _ _ _ _ _).mpr
      refine ⟨hq, ?_⟩
      intro r hrP hrq
      obtain ⟨v, hv, hvr, υ, s, hs, hvs, he⟩ := hr ν t ht r hrP
        (hR.2.2 r hrP q hq p hp hrq hqp)
        (hR.2.2 r hrP q hq t (forcingOrder_right_mem hR hqt) hrq hqt)
      exact ⟨v, hv, hvr, υ, s, hs, hvs, atomicEquality_symm P R υ ν ▸ he⟩
  · rintro ⟨hp, hl, hr⟩
    refine ⟨hp, ?_, ?_⟩
    · intro υ s hs q hq hqp hqs
      exact ((mem_atomicMembership_iff _ _ _ _ _).mp (hl υ s hs q hq hqp hqs)).2 q hq (hR.2.1 q hq)
    · intro ν t ht q hq hqp hqt
      obtain ⟨v, hv, hvq, υ, s, hs, hvs, he⟩ :=
        ((mem_atomicMembership_iff _ _ _ _ _).mp (hr ν t ht q hq hqp hqt)).2 q hq (hR.2.1 q hq)
      exact ⟨v, hv, hvq, υ, s, hs, hvs, atomicEquality_symm P R ν υ ▸ he⟩

end ZFVP
