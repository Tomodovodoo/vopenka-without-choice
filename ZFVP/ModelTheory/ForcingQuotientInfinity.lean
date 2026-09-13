import ZFVP.ModelTheory.ForcingQuotientCheckNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingCheck_empty (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (one : V) (hone : IsForcingTop P R one)
    (x : ForcingQuotient P R G hR hG.1) : x ∉ forcingCheck P R G hR hG.1 one hone ∅ := by
  intro hx
  obtain ⟨z, hz, _⟩ := (forcingCheck_endExtension P R G hR hG one hone ∅ x).mp hx
  exact not_mem_empty hz

theorem forcingCheck_succ (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (one : V) (hone : IsForcingTop P R one)
    (a : V) (x : ForcingQuotient P R G hR hG.1) :
    x ∈ forcingCheck P R G hR hG.1 one hone (succ a) ↔
      x = forcingCheck P R G hR hG.1 one hone a ∨ x ∈ forcingCheck P R G hR hG.1 one hone a := by
  unfold IsExternalForcingGeneric at hG
  rw [forcingCheck_endExtension P R G hR hG]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases mem_succ_iff.mp hz with rfl | hz
    · exact Or.inl rfl
    · exact Or.inr ((forcingCheck_mem_iff P R G hR hG.1 one hone z a).mpr hz)
  · rintro (he | hm)
    · exact ⟨a, mem_succ_self a, he⟩
    · obtain ⟨z, hz, he⟩ := (forcingCheck_endExtension P R G hR hG one hone a x).mp hm
      exact ⟨z, mem_succ_iff.mpr (Or.inr hz), he⟩

theorem forcingQuotient_infinity (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (one : V) (hone : IsForcingTop P R one) :
    ∃ I : ForcingQuotient P R G hR hG.1,
      (∀ e, (∀ z, z ∉ e) → e ∈ I) ∧
      (∀ x, x ∈ I → ∀ y, (∀ z, z ∈ y ↔ z = x ∨ z ∈ x) → y ∈ I) := by
  unfold IsExternalForcingGeneric at hG
  refine ⟨forcingCheck P R G hR hG.1 one hone ω, ?_, ?_⟩
  · intro e he
    have heq : e = forcingCheck P R G hR hG.1 one hone ∅ := by
      apply forcingQuotient_extensionality P R G hR hG
      intro z
      exact iff_of_false (he z) (forcingCheck_empty P R G hR hG one hone z)
    rw [heq]
    exact (forcingCheck_mem_iff P R G hR hG.1 one hone ∅ ω).mpr empty_mem_ω
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (forcingCheck_endExtension P R G hR hG one hone ω x).mp hx
    have heq : y = forcingCheck P R G hR hG.1 one hone (succ a) := by
      apply forcingQuotient_extensionality P R G hR hG
      intro z
      exact (hy z).trans (forcingCheck_succ P R G hR hG one hone a z).symm
    rw [heq]
    exact (forcingCheck_mem_iff P R G hR hG.1 one hone (succ a) ω).mpr (ω_succ_closed ha)

end ZFVP
