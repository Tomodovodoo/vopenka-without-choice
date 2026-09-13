import ZFVP.SetTheory.OrdinalAddition
import ZFVP.SetTheory.UniformRecursion
import ZFVP.SetTheory.NaturalPredecessor

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance ordinalAddStep_all_definable : ℒₛₑₜ-function₂[V] ordinalAddStep := by
  unfold ordinalAddStep
  definability

instance ordinalAdd_definable : ℒₛₑₜ-function₂[V] ordinalAdd := by
  have h : ℒₛₑₜ-relation₃ (fun y α β : V ↦
    (∃ f, IsAttempt (ordinalAddStep α) β f ∧ y = ordinalAddStep α f) ∨
      (¬IsOrdinal β ∧ y = ∅)) := by
    unfold IsAttempt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact transfiniteRec_eq_iff (ordinalAddStep (v 1)) (ordinalAddStep_definable (v 1)) (v 2) (v 0)

theorem ordinalAdd_natural {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    ordinalAdd a b ∈ (ω : V) := by
  have : IsOrdinal a := IsOrdinal.of_mem ha
  apply naturalNumber_induction (fun b ↦ ordinalAdd a b ∈ (ω : V)) (by definability) ?_ ?_ b hb
  · simpa only [zero_def, ordinalAdd_zero] using ha
  · intro n hn ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    rw [ordinalAdd_succ]
    exact ω_succ_closed ih

theorem ordinalAdd_zero_left_natural {n : V} (hn : n ∈ (ω : V)) : ordinalAdd (0 : V) n = n := by
  apply naturalNumber_induction (fun n ↦ ordinalAdd (0 : V) n = n) (by definability) ?_ ?_ n hn
  · exact ordinalAdd_zero _
  · intro n hn ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    rw [ordinalAdd_succ, ih]

theorem ordinalAdd_succ_left_natural {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    ordinalAdd (succ a) b = succ (ordinalAdd a b) := by
  have : IsOrdinal a := IsOrdinal.of_mem ha
  apply naturalNumber_induction (fun b ↦ ordinalAdd (succ a) b = succ (ordinalAdd a b)) (by definability) ?_ ?_ b hb
  · simp only [zero_def, ordinalAdd_zero]
  · intro n hn ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    rw [ordinalAdd_succ, ih, ordinalAdd_succ]

theorem ordinalAdd_comm_natural {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    ordinalAdd a b = ordinalAdd b a := by
  have : IsOrdinal a := IsOrdinal.of_mem ha
  apply naturalNumber_induction (fun b ↦ ordinalAdd a b = ordinalAdd b a) (by definability) ?_ ?_ b hb
  · rw [show (0 : V) = ∅ from rfl, ordinalAdd_zero]
    exact (ordinalAdd_zero_left_natural ha).symm
  · intro n hn ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    rw [ordinalAdd_succ, ordinalAdd_succ_left_natural hn ha, ih]

theorem ordinalAdd_right_injective {a b c : V} [IsOrdinal b] [IsOrdinal c]
    (h : ordinalAdd a b = ordinalAdd a c) : b = c := by
  rcases IsOrdinal.mem_trichotomy b c with hlt | he | hgt
  · have hh := ordinalAdd_mem (α := a) hlt
    rw [h] at hh
    exact False.elim (mem_irrefl _ hh)
  · exact he
  · have hh := ordinalAdd_mem (α := a) hgt
    rw [h] at hh
    exact False.elim (mem_irrefl _ hh)

end ZFVP
