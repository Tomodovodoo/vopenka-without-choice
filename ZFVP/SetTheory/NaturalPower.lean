import ZFVP.SetTheory.NaturalArithmeticLaws
import ZFVP.SetTheory.NaturalArithmeticOrder

/-! Exponentiation by recursion over every element of internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def naturalPowStepFormula : SetTheorySemisentence 3 :=
  f“z a g. (!domain.dfn g = !isEmpty ∧ z = !succ.dfn (!isEmpty)) ∨
    (!domain.dfn g ≠ !isEmpty ∧ z = !naturalMulFormula
      (!value.dfn g (!sUnion.dfn (!domain.dfn g))) a)”

def naturalPowFormula : SetTheorySemisentence 3 := parameterRecursionFormula naturalPowStepFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def naturalPowStep (a g : V) : V :=
  naturalIterationStep (fun x ↦ naturalMul x a) 1 g

instance naturalPowStepFormula_defined : ℒₛₑₜ-function₂[V] naturalPowStep via naturalPowStepFormula :=
  ⟨fun v ↦ by
    have h1 : (1 : V) = succ ∅ := rfl
    by_cases h : domain (v 2) = 0
    · simp_all [naturalPowStepFormula, naturalPowStep, naturalIterationStep, zero_def]
    · simp_all [naturalPowStepFormula, naturalPowStep, naturalIterationStep, zero_def,
        -ne_empty_iff_isNonempty]⟩

instance naturalPowStep_definable : ℒₛₑₜ-function₂[V] naturalPowStep :=
  naturalPowStepFormula_defined.to_definable

noncomputable def naturalPow (a n : V) : V :=
  naturalIteration (fun x ↦ naturalMul x a) (by definability) 1 n

instance naturalPowFormula_defined : ℒₛₑₜ-function₂[V] naturalPow via naturalPowFormula :=
  parameterRecursionFormula_defined naturalPowStep naturalPowStepFormula

instance naturalPow_definable : ℒₛₑₜ-function₂[V] naturalPow := naturalPowFormula_defined.to_definable

@[simp] theorem naturalPow_zero (a : V) : naturalPow a 0 = 1 := naturalIteration_zero _ _ _

theorem naturalPow_succ (a : V) {n : V} (hn : n ∈ (ω : V)) :
    naturalPow a (succ n) = naturalMul (naturalPow a n) a := naturalIteration_succ _ _ _ hn

theorem naturalPow_natural {a n : V} (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    naturalPow a n ∈ (ω : V) :=
  naturalIteration_invariant _ (by definability) 1 (fun x ↦ x ∈ (ω : V)) (by definability)
    (by simp) (fun x hx ↦ naturalMul_natural hx ha) n hn

theorem naturalPow_positive {a n : V} (ha : a ∈ (ω : V)) (ha0 : (0 : V) ∈ a)
    (hn : n ∈ (ω : V)) : (0 : V) ∈ naturalPow a n := by
  apply naturalNumber_induction (fun n ↦ (0 : V) ∈ naturalPow a n) (by definability) ?_ ?_ n hn
  · simp
  · intro n hn ih
    rw [naturalPow_succ _ hn]
    have h := naturalMul_lt_first (show (0 : V) ∈ ω by simp)
      (naturalPow_natural ha hn) ha ih ha0
    simpa only [naturalMul_zero_left ha] using h

theorem naturalPow_add {a n m : V} (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hm : m ∈ (ω : V)) :
    naturalPow a (ordinalAdd n m) = naturalMul (naturalPow a n) (naturalPow a m) := by
  let := IsOrdinal.of_mem hn
  apply naturalNumber_induction
    (fun m ↦ naturalPow a (ordinalAdd n m) = naturalMul (naturalPow a n) (naturalPow a m))
    (by definability) ?_ ?_ m hm
  · change naturalPow a (ordinalAdd n ∅) = naturalMul (naturalPow a n) (naturalPow a 0)
    rw [ordinalAdd_zero, naturalPow_zero, naturalMul_one (naturalPow_natural ha hn)]
  · intro m hm ih
    let := IsOrdinal.of_mem hm
    rw [ordinalAdd_succ, naturalPow_succ _ (ordinalAdd_natural hn hm), ih,
      naturalPow_succ _ hm, naturalMul_assoc (naturalPow_natural ha hn) (naturalPow_natural ha hm) ha]

theorem naturalMul_two {a : V} (ha : a ∈ (ω : V)) :
    naturalMul a (2 : V) = ordinalAdd a a := by
  change naturalMul a (succ 1) = ordinalAdd a a
  rw [naturalMul_succ a (show (1 : V) ∈ ω by simp), naturalMul_one ha]

theorem one_subset_positive_natural {a : V} (ha0 : (0 : V) ∈ a) : (1 : V) ⊆ a := by
  intro z hz
  have he : z = (0 : V) := by simpa only [one_def, mem_singleton_iff] using hz
  exact he ▸ ha0

theorem naturalPow_two_growth {n : V} (hn : n ∈ (ω : V)) : succ n ⊆ naturalPow (2 : V) n := by
  apply naturalNumber_induction (fun n ↦ succ n ⊆ naturalPow (2 : V) n) (by definability) ?_ ?_ n hn
  · rw [naturalPow_zero]
    exact subset_refl (1 : V)
  · intro n hn ih
    have hp := naturalPow_natural (show (2 : V) ∈ ω by simp) hn
    have hp0 := naturalPow_positive (show (2 : V) ∈ ω by simp) (show (0 : V) ∈ 2 by simp) hn
    let := IsOrdinal.of_mem hp
    let := IsOrdinal.of_mem (show (1 : V) ∈ ω by simp)
    rw [naturalPow_succ _ hn, naturalMul_two hp]
    rw [← ordinalAdd_one_natural (ω_succ_closed hn)]
    exact subset_trans
      (ordinalAdd_mono_first_natural (ω_succ_closed hn) hp (by simp) ih)
      (ordinalAdd_mono_right _ (one_subset_positive_natural hp0))

end ZFVP
