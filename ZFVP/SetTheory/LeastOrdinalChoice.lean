import ZFVP.SetTheory.Rank

/-! A definable least-ordinal operation, with zero as its value when no
ordinal satisfies the relation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def leastOrdinalOrZero (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (x : V) : V := by
  classical
  exact if h : ∃ y, IsOrdinal y ∧ R x y then
    Classical.choose! (leastOrdinal_existsUnique (R x) (by definability) h) else 0

theorem leastOrdinalOrZero_eq_iff (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (x α : V) :
    α = leastOrdinalOrZero R hR x ↔
      IsLeastOrdinal (R x) α ∨ (¬∃ y, IsOrdinal y ∧ R x y) ∧ α = 0 := by
  classical
  by_cases h : ∃ y, IsOrdinal y ∧ R x y
  · have hu := leastOrdinal_existsUnique (R x) (by definability) h
    have hs := Classical.choose!_spec hu
    simp only [h, not_true_eq_false, false_and, or_false, leastOrdinalOrZero, ↓reduceDIte]
    exact ⟨fun he ↦ he.symm ▸ hs, fun ha ↦ hu.unique ha hs⟩
  · have hn : ¬IsLeastOrdinal (R x) α := fun ha ↦ h ⟨α, ha.1, ha.2.1⟩
    simp [leastOrdinalOrZero, h, hn]

instance leastOrdinalOrZero_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-function₁ (leastOrdinalOrZero R hR) := by
  have h : ℒₛₑₜ-relation (fun α x : V ↦
      IsLeastOrdinal (R x) α ∨ (¬∃ y, IsOrdinal y ∧ R x y) ∧ α = 0) := by
    unfold IsLeastOrdinal
    definability
  apply Language.Definable.of_iff h
  intro v
  exact leastOrdinalOrZero_eq_iff R hR (v 1) (v 0)

theorem leastOrdinalOrZero_spec (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (x : V) (hx : ∃ y, IsOrdinal y ∧ R x y) :
    IsLeastOrdinal (R x) (leastOrdinalOrZero R hR x) :=
  ((leastOrdinalOrZero_eq_iff R hR x _).mp rfl).resolve_right (fun h ↦ h.1 hx)

instance leastOrdinalOrZero_ordinal (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (x : V) :
    IsOrdinal (leastOrdinalOrZero R hR x) := by
  rcases (leastOrdinalOrZero_eq_iff R hR x _).mp rfl with h | ⟨_, he⟩
  · exact h.1
  · rw [he]
    infer_instance

end ZFVP
