import ZFVP.SetTheory.NameAction
import ZFVP.SetTheory.AtomicMembership

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Replacing each condition by an order-equivalent condition preserves every
name up to forced equality, without an injectivity requirement on the map. -/
theorem nameAction_forced_equal_of_equivalent_conditions {P R f τ : V}
    (hR : IsForcingPreorder P R) (hf : f ∈ P ^ P)
    (he : ∀ q ∈ P, ⟨f ‘ q, q⟩ₖ ∈ R ∧ ⟨q, f ‘ q⟩ₖ ∈ R)
    (hτ : IsForcingName P τ) : ∀ p ∈ P, p ∈ atomicEquality P R τ (nameAction f τ) := by
  apply forcingName_induction P (fun τ ↦ ∀ p ∈ P, p ∈ atomicEquality P R τ (nameAction f τ))
    (by definability) ?_ τ hτ
  intro ν hν ih p hp
  apply (mem_atomicEquality_iff _ _ _ _ _).mpr
  refine ⟨hp, ?_, ?_⟩
  · intro σ s hs q hq _ hqs
    have hsP := forcingName_condition hν hs
    exact ⟨q, hq, hR.2.1 q hq, nameAction f σ, f ‘ s,
      (mem_nameAction_iff hν f _).mpr ⟨σ, s, hs, rfl⟩,
      hR.2.2 q hq s hsP (f ‘ s) (function_value_mem hf hsP) hqs (he s hsP).2,
      ih σ s hs q hq⟩
  · intro σ' s' hs' q hq _ hqs'
    obtain ⟨σ, s, hs, heq⟩ := (mem_nameAction_iff hν f _).mp hs'
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp heq
    have hsP := forcingName_condition hν hs
    exact ⟨q, hq, hR.2.1 q hq, σ, s, hs,
      hR.2.2 q hq (f ‘ s) (function_value_mem hf hsP) s hsP hqs' (he s hsP).1,
      ih σ s hs q hq⟩

theorem nameAction_eq_self_of_fixes_conditions {P f τ : V}
    (hf : ∀ p ∈ P, f ‘ p = p) (hτ : IsForcingName P τ) : nameAction f τ = τ := by
  apply forcingName_induction P (fun τ ↦ nameAction f τ = τ) (by definability) ?_ τ hτ
  intro ν hν ih
  apply mem_ext
  intro z
  rw [mem_nameAction_iff hν]
  constructor
  · rintro ⟨σ, p, hp, rfl⟩
    rw [ih σ p hp, hf p (forcingName_condition hν hp)]
    exact hp
  · intro hz
    obtain ⟨σ, p, _, rfl, _⟩ := (forcingName_iff P ν).mp hν z hz
    exact ⟨σ, p, hz, by rw [ih σ p hz, hf p (forcingName_condition hν hz)]⟩

end ZFVP
