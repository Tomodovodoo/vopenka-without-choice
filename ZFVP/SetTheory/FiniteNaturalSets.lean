import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.FiniteCofinality

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internallyFinite_naturals_bounded {A : V} (hA : IsInternallyFinite A)
    (hsub : A ⊆ (ω : V)) : ∃ n ∈ (ω : V), A ⊆ n := by
  have h : ∀ A, IsInternallyFinite A → A ⊆ (ω : V) → ∃ n ∈ (ω : V), A ⊆ n := by
    apply internallyFinite_induction
      (fun A ↦ A ⊆ (ω : V) → ∃ n ∈ (ω : V), A ⊆ n) (by definability)
    · intro _
      exact ⟨∅, empty_mem_ω, subset_refl _⟩
    · intro B b ih hb
      have hbω : b ∈ (ω : V) := hb _ (by simp)
      obtain ⟨n, hn, hBn⟩ := ih (fun x hx ↦ hb x (mem_insert.mpr (Or.inr hx)))
      refine ⟨n ∪ succ b, ordinal_union_mem hn (ω_succ_closed hbω), ?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_union_iff.mpr (Or.inr (by simp))
      · exact mem_union_iff.mpr (Or.inl (hBn x hx))
  exact h A hA hsub

theorem internallyFinite_fresh_natural {A : V} (hA : IsInternallyFinite A) :
    ∃ n ∈ (ω : V), n ∉ A := by
  have hi : IsInternallyFinite (A ∩ (ω : V)) :=
    internallyFinite_subset hA (fun x hx ↦ (mem_inter_iff.mp hx).1)
  obtain ⟨n, hn, hbound⟩ := internallyFinite_naturals_bounded hi
    (fun x hx ↦ (mem_inter_iff.mp hx).2)
  exact ⟨n, hn, fun hna ↦ mem_irrefl n (hbound n (mem_inter_iff.mpr ⟨hna, hn⟩))⟩

theorem omega_internallyInfinite : IsInternallyInfinite (ω : V) := by
  intro hf
  obtain ⟨n, hn, hn'⟩ := internallyFinite_fresh_natural hf
  exact hn' hn

end ZFVP
