import ZFVP.ModelTheory.InfinitarySyntax

/-! Every infinitary formula has countably many constructor subformulas, including
across binder depths. Embedded first-order formulas are counted as single nodes. -/

namespace ZFVP.Infinitary
open LO LO.FirstOrder

namespace Formula
variable {L : Language}

def subformulas : {n : ℕ} → Formula L n → Set (Σ m, Formula L m)
  | n, .fo φ => {⟨n, .fo φ⟩}
  | n, .neg φ => insert ⟨n, .neg φ⟩ (subformulas φ)
  | n, .conj φ => insert ⟨n, .conj φ⟩ (⋃ i, subformulas (φ i))
  | n, .exs φ => insert ⟨n, .exs φ⟩ (subformulas φ)
  | n, .q φ => insert ⟨n, .q φ⟩ (subformulas φ)

theorem self_mem_subformulas {n : ℕ} (φ : Formula L n) :
    ⟨n, φ⟩ ∈ subformulas φ := by
  cases φ <;> simp [subformulas]

theorem subformulas_countable {n : ℕ} (φ : Formula L n) :
    (subformulas φ).Countable := by
  induction φ with
  | fo φ => exact Set.countable_singleton _
  | neg φ ih => exact ih.insert _
  | conj φ ih => exact (Set.countable_iUnion ih).insert _
  | exs φ ih => exact ih.insert _
  | q φ ih => exact ih.insert _

theorem subformulas_subset_of_mem {n m : ℕ} {φ : Formula L n} {ψ : Formula L m}
    (h : ⟨m, ψ⟩ ∈ subformulas φ) : subformulas ψ ⊆ subformulas φ := by
  induction φ with
  | fo φ =>
      have he : (⟨m, ψ⟩ : Σ k, Formula L k) = ⟨_, .fo φ⟩ := h
      cases he
      exact Set.Subset.rfl
  | neg φ ih =>
      rcases h with he | h
      · cases he; exact Set.Subset.rfl
      · exact (ih h).trans (Set.subset_insert _ _)
  | conj φ ih =>
      rcases h with he | h
      · cases he; exact Set.Subset.rfl
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
        intro a ha
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, ih i hi ha⟩)
  | exs φ ih =>
      rcases h with he | h
      · cases he; exact Set.Subset.rfl
      · exact (ih h).trans (Set.subset_insert _ _)
  | q φ ih =>
      rcases h with he | h
      · cases he; exact Set.Subset.rfl
      · exact (ih h).trans (Set.subset_insert _ _)

end Formula
end ZFVP.Infinitary
