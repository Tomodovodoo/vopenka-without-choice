import ZFVP.ModelTheory.InternalNaturalPairing

/-! Uniform inverse projections for the natural-number pairing used by the syntax encoding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

def naturalSquareLeftFormula : SetTheorySemisentence 2 :=
  f“z n. (n ∈ !isω ∧ z ∈ !isω ∧ ∃ y ∈ !isω, n = !naturalSquarePairFormula z y) ∨
    (n ∉ !isω ∧ z = !isEmpty)”

def naturalSquareRightFormula : SetTheorySemisentence 2 :=
  f“z n. (n ∈ !isω ∧ z ∈ !isω ∧ ∃ x ∈ !isω, n = !naturalSquarePairFormula x z) ∨
    (n ∉ !isω ∧ z = !isEmpty)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalSquareUnpair_exists {n : V} (hn : n ∈ (ω : V)) :
    ∃ p : V × V, p.1 ∈ (ω : V) ∧ p.2 ∈ (ω : V) ∧ naturalSquarePair p.1 p.2 = n := by
  obtain ⟨a, ha, b, hb, he⟩ := naturalSquarePair_surjective hn
  exact ⟨(a, b), ha, hb, he⟩

noncomputable def naturalSquareUnpair (n : V) : V × V := by
  classical
  exact if hn : n ∈ (ω : V) then Classical.choose (naturalSquareUnpair_exists hn) else (0, 0)

noncomputable abbrev naturalSquareLeft (n : V) : V := (naturalSquareUnpair n).1
noncomputable abbrev naturalSquareRight (n : V) : V := (naturalSquareUnpair n).2

theorem naturalSquareUnpair_spec {n : V} (hn : n ∈ (ω : V)) :
    naturalSquareLeft n ∈ (ω : V) ∧ naturalSquareRight n ∈ (ω : V) ∧
      naturalSquarePair (naturalSquareLeft n) (naturalSquareRight n) = n := by
  simpa only [naturalSquareLeft, naturalSquareRight, naturalSquareUnpair, dite_eq_left hn] using
    Classical.choose_spec (naturalSquareUnpair_exists hn)

theorem naturalSquareLeft_natural (n : V) : naturalSquareLeft n ∈ (ω : V) := by
  by_cases hn : n ∈ (ω : V)
  · exact (naturalSquareUnpair_spec hn).1
  · simp [naturalSquareLeft, naturalSquareUnpair, hn]

theorem naturalSquareRight_natural (n : V) : naturalSquareRight n ∈ (ω : V) := by
  by_cases hn : n ∈ (ω : V)
  · exact (naturalSquareUnpair_spec hn).2.1
  · simp [naturalSquareRight, naturalSquareUnpair, hn]

theorem naturalSquareLeft_graph (z n : V) :
    z = naturalSquareLeft n ↔
      (n ∈ (ω : V) ∧ z ∈ (ω : V) ∧ ∃ y ∈ (ω : V), n = naturalSquarePair z y) ∨
        (n ∉ (ω : V) ∧ z = 0) := by
  by_cases hn : n ∈ (ω : V)
  · simp only [hn, true_and, not_true_eq_false, false_and, or_false]
    constructor
    · rintro rfl
      exact ⟨naturalSquareLeft_natural n, naturalSquareRight n,
        naturalSquareRight_natural n, (naturalSquareUnpair_spec hn).2.2.symm⟩
    · rintro ⟨hz, y, hy, he⟩
      exact (naturalSquarePair_injective hz hy (naturalSquareLeft_natural n)
        (naturalSquareRight_natural n) (he.symm.trans (naturalSquareUnpair_spec hn).2.2.symm)).1
  · simp [hn, naturalSquareLeft, naturalSquareUnpair]

theorem naturalSquareRight_graph (z n : V) :
    z = naturalSquareRight n ↔
      (n ∈ (ω : V) ∧ z ∈ (ω : V) ∧ ∃ x ∈ (ω : V), n = naturalSquarePair x z) ∨
        (n ∉ (ω : V) ∧ z = 0) := by
  by_cases hn : n ∈ (ω : V)
  · simp only [hn, true_and, not_true_eq_false, false_and, or_false]
    constructor
    · rintro rfl
      exact ⟨naturalSquareRight_natural n, naturalSquareLeft n,
        naturalSquareLeft_natural n, (naturalSquareUnpair_spec hn).2.2.symm⟩
    · rintro ⟨hz, x, hx, he⟩
      exact (naturalSquarePair_injective hx hz (naturalSquareLeft_natural n)
        (naturalSquareRight_natural n) (he.symm.trans (naturalSquareUnpair_spec hn).2.2.symm)).2
  · simp [hn, naturalSquareRight, naturalSquareUnpair]

instance naturalSquareLeft_defined : ℒₛₑₜ-function₁[V] naturalSquareLeft via naturalSquareLeftFormula :=
  ⟨fun v ↦ by simp [naturalSquareLeftFormula, naturalSquareLeft_graph, zero_def]⟩

instance naturalSquareRight_defined : ℒₛₑₜ-function₁[V] naturalSquareRight via naturalSquareRightFormula :=
  ⟨fun v ↦ by simp [naturalSquareRightFormula, naturalSquareRight_graph, zero_def]⟩

instance naturalSquareLeft_definable : ℒₛₑₜ-function₁[V] naturalSquareLeft := naturalSquareLeft_defined.to_definable
instance naturalSquareRight_definable : ℒₛₑₜ-function₁[V] naturalSquareRight := naturalSquareRight_defined.to_definable

theorem naturalSquareUnpair_pair {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    naturalSquareUnpair (naturalSquarePair a b) = (a, b) := by
  have he := (naturalSquareUnpair_spec (naturalSquarePair_natural ha hb)).2.2
  have h := naturalSquarePair_injective (naturalSquareLeft_natural _) (naturalSquareRight_natural _) ha hb he
  exact Prod.ext h.1 h.2

theorem naturalSquareUnpair_natCast (n : ℕ) :
    naturalSquareUnpair (n : V) = ((((Nat.unpair n).1 : ℕ) : V), (((Nat.unpair n).2 : ℕ) : V)) := by
  have he : naturalSquarePair (((Nat.unpair n).1 : ℕ) : V) (((Nat.unpair n).2 : ℕ) : V) = (n : V) := by
    rw [naturalSquarePair_natCast, Nat.pair_unpair]
  rw [← he]
  exact naturalSquareUnpair_pair (by simp) (by simp)

theorem naturalSquareUnpair_internalArithmeticVal (x : InternalArithmetic V) :
    naturalSquareUnpair (internalArithmeticVal x) =
      (internalArithmeticVal (Arithmetic.pi₁ x), internalArithmeticVal (Arithmetic.pi₂ x)) := by
  have he : naturalSquarePair (internalArithmeticVal (Arithmetic.pi₁ x))
      (internalArithmeticVal (Arithmetic.pi₂ x)) = internalArithmeticVal x := by
    rw [← internalArithmeticVal_pair, Arithmetic.pair_unpair]
  rw [← he]
  exact naturalSquareUnpair_pair (internalArithmeticVal_mem _) (internalArithmeticVal_mem _)

theorem naturalSquareLeft_subset {n : V} (hn : n ∈ (ω : V)) : naturalSquareLeft n ⊆ n := by
  obtain ⟨x, rfl⟩ := internalArithmeticVal_surjective hn
  change (naturalSquareUnpair (internalArithmeticVal x)).1 ⊆ _
  rw [naturalSquareUnpair_internalArithmeticVal]
  exact (internalArithmetic_le _ _).mp (Arithmetic.pi₁_le_self x)

theorem naturalSquareRight_subset {n : V} (hn : n ∈ (ω : V)) : naturalSquareRight n ⊆ n := by
  obtain ⟨x, rfl⟩ := internalArithmeticVal_surjective hn
  change (naturalSquareUnpair (internalArithmeticVal x)).2 ⊆ _
  rw [naturalSquareUnpair_internalArithmeticVal]
  exact (internalArithmetic_le _ _).mp (Arithmetic.pi₂_le_self x)

end ZFVP
