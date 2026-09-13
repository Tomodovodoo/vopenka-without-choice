import ZFVP.SetTheory.FiniteSets

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internallyFinite_sUnion {A : V} (hA : IsInternallyFinite A)
    (hall : ∀ B ∈ A, IsInternallyFinite B) : IsInternallyFinite (⋃ˢ A) := by
  have h : ∀ A : V, IsInternallyFinite A → (∀ B ∈ A, IsInternallyFinite B) →
      IsInternallyFinite (⋃ˢ A) := by
    apply internallyFinite_induction
      (fun A ↦ (∀ B ∈ A, IsInternallyFinite B) → IsInternallyFinite (⋃ˢ A)) (by definability)
    · intro _
      simpa using (internallyFinite_empty (V := V))
    · intro A B ih hB
      have hAf := ih (fun C hC ↦ hB C (mem_insert.mpr (Or.inr hC)))
      have hBf := hB B (by simp)
      have he : ⋃ˢ (insert B A) = B ∪ ⋃ˢ A := by
        ext x
        simp only [mem_sUnion_iff, mem_insert, mem_union_iff]
        constructor
        · rintro ⟨C, rfl | hC, hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨C, hC, hx⟩
        · rintro (hx | ⟨C, hC, hx⟩)
          · exact ⟨B, Or.inl rfl, hx⟩
          · exact ⟨C, Or.inr hC, hx⟩
      rw [he]
      exact internallyFinite_union hBf hAf
  exact h A hA hall

end ZFVP
