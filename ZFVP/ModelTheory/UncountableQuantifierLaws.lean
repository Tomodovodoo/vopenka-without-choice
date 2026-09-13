import Mathlib.Data.Set.Countable

/-! Semantic laws for the standard uncountability quantifier. -/

namespace ZFVP.UncountableQuantifierLaws

universe u v

variable {α : Type u} {β : Type v}

theorem countable_exists_nat_iff (P : ℕ → α → Prop) :
    Set.Countable {x | ∃ n : ℕ, P n x} ↔ ∀ n : ℕ, Set.Countable {x | P n x} := by
  have he : {x | ∃ n : ℕ, P n x} = ⋃ n : ℕ, {x | P n x} := by
    ext x
    simp
  rw [he, Set.countable_iUnion_iff]

theorem uncountable_exists_nat_iff (P : ℕ → α → Prop) :
    ¬Set.Countable {x | ∃ n : ℕ, P n x} ↔ ∃ n : ℕ, ¬Set.Countable {x | P n x} := by
  classical
  rw [countable_exists_nat_iff]
  exact not_forall

/-- If a relation has uncountable range, some fiber or its domain is uncountable. -/
theorem interchange (R : α → β → Prop)
    (h : ¬Set.Countable {y | ∃ x, R x y}) :
    (∃ x, ¬Set.Countable {y | R x y}) ∨ ¬Set.Countable {x | ∃ y, R x y} := by
  classical
  by_cases hf : ∃ x, ¬Set.Countable {y | R x y}
  · exact Or.inl hf
  right
  intro hd
  have hfs : ∀ x, Set.Countable {y | R x y} := by
    simpa only [not_exists, not_not] using hf
  have hu := hd.biUnion (fun x _ ↦ hfs x)
  apply h
  apply hu.mono
  rintro y ⟨x, hxy⟩
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨⟨y, hxy⟩, hxy⟩⟩

theorem uncountable_mono {s t : Set α} (h : s ⊆ t) (hs : ¬s.Countable) :
    ¬t.Countable := fun ht ↦ hs (ht.mono h)

theorem uncountable_predicate_mono {P Q : α → Prop} (h : ∀ x, P x → Q x)
    (hP : ¬Set.Countable {x | P x}) : ¬Set.Countable {x | Q x} :=
  uncountable_mono h hP

theorem countable_two_points (a b : α) : Set.Countable {x | x = a ∨ x = b} := by
  have he : {x | x = a ∨ x = b} = ({a, b} : Set α) := by
    ext x
    simp
  rw [he]
  exact (Set.toFinite _).countable

end ZFVP.UncountableQuantifierLaws
