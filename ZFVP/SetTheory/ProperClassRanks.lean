import ZFVP.SetTheory.Cn

/-! A class not covered by a set has members of arbitrarily high rank. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsProperClass (P : V → Prop) : Prop := ∀ A : V, ∃ x : V, P x ∧ x ∉ A

theorem IsProperClass.rank_unbounded {P : V → Prop} (hP : IsProperClass P)
    (γ : V) [IsOrdinal γ] : ∃ x : V, P x ∧ γ ∈ rank x := by
  obtain ⟨x, hx, hnot⟩ := hP (hierarchy (succ γ))
  refine ⟨x, hx, ?_⟩
  have hr : rank x ∉ succ γ := by simpa only [mem_hierarchy_iff_rank_mem] using hnot
  rcases IsOrdinal.mem_trichotomy (rank x) γ with hlt | he | hgt
  · exact False.elim (hr (mem_succ_iff.mpr (Or.inr hlt)))
  · exact False.elim (hr (mem_succ_iff.mpr (Or.inl he)))
  · exact hgt

end ZFVP
