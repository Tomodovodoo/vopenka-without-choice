import ZFVP.SetTheory.FiniteSets

/-! An internal finite subset of a directed union is contained in one member.
The induction includes sets of internally finite, nonstandard size. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internallyFinite_subset_directed_sUnion {G S : V} (hne : IsNonempty G)
    (hdir : ∀ A ∈ G, ∀ B ∈ G, ∃ C ∈ G, A ⊆ C ∧ B ⊆ C)
    (hS : IsInternallyFinite S) (hSG : S ⊆ ⋃ˢ G) : ∃ A ∈ G, S ⊆ A := by
  have hall : ∀ S, IsInternallyFinite S → S ⊆ ⋃ˢ G → ∃ A ∈ G, S ⊆ A := by
    apply internallyFinite_induction (fun S ↦ S ⊆ ⋃ˢ G → ∃ A ∈ G, S ⊆ A) (by definability)
    · intro _
      obtain ⟨A, hA⟩ := hne
      exact ⟨A, hA, empty_subset _⟩
    · intro S x ih hsub
      obtain ⟨A, hA, hSA⟩ := ih (fun y hy ↦ hsub y (mem_insert.mpr (Or.inr hy)))
      obtain ⟨B, hB, hxB⟩ := mem_sUnion_iff.mp (hsub x (mem_insert.mpr (Or.inl rfl)))
      obtain ⟨C, hC, hAC, hBC⟩ := hdir A hA B hB
      refine ⟨C, hC, ?_⟩
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact hBC _ hxB
      · exact hAC y (hSA y hy)
  exact hall S hS hSG

end ZFVP
