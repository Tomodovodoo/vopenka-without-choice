import ZFVP.SetTheory.DefinableGraph

/-! The standard natural-number embedding into an arbitrary internal ZF model.
This does not assert that all internal natural numbers are standard. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem natCast_mem_of_lt {m n : ℕ} (h : m < n) : (m : V) ∈ (n : V) := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero m h)
  | succ n ih =>
    rw [num_succ_def, mem_succ_iff]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact Or.inr (ih h)
    · exact Or.inl rfl

theorem natCast_injective : Function.Injective (fun n : ℕ ↦ (n : V)) := by
  intro m n h
  change (m : V) = (n : V) at h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · have hm : (m : V) ∈ (n : V) := natCast_mem_of_lt hlt
    rw [h] at hm
    exact False.elim (mem_irrefl _ hm)
  · exact heq
  · have hn : (n : V) ∈ (m : V) := natCast_mem_of_lt hgt
    rw [h] at hn
    exact False.elim (mem_irrefl _ hn)

theorem natCast_eq_iff (m n : ℕ) : (m : V) = (n : V) ↔ m = n := natCast_injective.eq_iff

theorem natCast_mem_iff (m n : ℕ) : (m : V) ∈ (n : V) ↔ m < n := by
  induction n with
  | zero => simp [show ((0 : ℕ) : V) = ∅ from rfl]
  | succ n ih =>
    rw [num_succ_def, mem_succ_iff, natCast_eq_iff, ih]
    exact or_comm.trans Nat.lt_succ_iff_lt_or_eq.symm

theorem mem_natCast_iff (x : V) (n : ℕ) :
    x ∈ (n : V) ↔ ∃ i : Fin n, x = (i.val : V) := by
  induction n with
  | zero => simp [zero_def]
  | succ n ih =>
    rw [num_succ_def, mem_succ_iff, ih]
    constructor
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
      · exact ⟨i.castSucc, rfl⟩
    · rintro ⟨i, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp i.isLt with h | h
      · exact Or.inr ⟨⟨i.val, h⟩, rfl⟩
      · exact Or.inl (congrArg (fun k : ℕ ↦ (k : V)) h)

end ZFVP
