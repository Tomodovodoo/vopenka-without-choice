import ZFVP.SetTheory.NaturalAddition
import ZFVP.SetTheory.NaturalIteration
import ZFVP.SetTheory.UniformCodingUniverse

/-! Multiplication on the whole internal omega of an arbitrary ZF model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def naturalMulStepFormula : SetTheorySemisentence 3 :=
  f“z a g. (!domain.dfn g = !isEmpty ∧ z = !isEmpty) ∨
    (!domain.dfn g ≠ !isEmpty ∧ z = !ordinalAddFormula
      (!value.dfn g (!sUnion.dfn (!domain.dfn g))) a)”

def naturalMulFormula : SetTheorySemisentence 3 := parameterRecursionFormula naturalMulStepFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def naturalMulStep (a g : V) : V :=
  naturalIterationStep (fun x ↦ ordinalAdd x a) 0 g

instance naturalMulStepFormula_defined : ℒₛₑₜ-function₂[V] naturalMulStep via naturalMulStepFormula :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = 0
    · simp_all [naturalMulStepFormula, naturalMulStep, naturalIterationStep, zero_def]
    · simp_all [naturalMulStepFormula, naturalMulStep, naturalIterationStep, zero_def, -ne_empty_iff_isNonempty]⟩

instance naturalMulStep_definable : ℒₛₑₜ-function₂[V] naturalMulStep :=
  naturalMulStepFormula_defined.to_definable

noncomputable def naturalMul (a n : V) : V :=
  naturalIteration (fun x ↦ ordinalAdd x a) (by definability) 0 n

instance naturalMulFormula_defined : ℒₛₑₜ-function₂[V] naturalMul via naturalMulFormula :=
  parameterRecursionFormula_defined naturalMulStep naturalMulStepFormula

instance naturalMul_definable : ℒₛₑₜ-function₂[V] naturalMul := naturalMulFormula_defined.to_definable

@[simp] theorem naturalMul_zero (a : V) : naturalMul a 0 = 0 := naturalIteration_zero _ _ _

@[simp] theorem naturalMul_empty (a : V) : naturalMul a ∅ = ∅ := naturalMul_zero a

theorem naturalMul_succ (a : V) {n : V} (hn : n ∈ (ω : V)) :
    naturalMul a (succ n) = ordinalAdd (naturalMul a n) a := naturalIteration_succ _ _ _ hn

theorem naturalMul_natural {a n : V} (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    naturalMul a n ∈ (ω : V) :=
  naturalIteration_invariant _ (by definability) 0 (fun x ↦ x ∈ (ω : V)) (by definability)
    (by simp) (fun x hx ↦ ordinalAdd_natural hx ha) n hn

theorem naturalMul_zero_left {n : V} (hn : n ∈ (ω : V)) : naturalMul (0 : V) n = 0 := by
  apply naturalNumber_induction (fun n ↦ naturalMul (0 : V) n = 0) (by definability) ?_ ?_ n hn
  · simp
  · intro n hn ih
    rw [naturalMul_succ _ hn, ih]
    exact ordinalAdd_zero _

theorem naturalMul_one {a : V} (ha : a ∈ (ω : V)) : naturalMul a 1 = a := by
  change naturalMul a (succ 0) = a
  rw [naturalMul_succ _ (by simp), naturalMul_zero, ordinalAdd_zero_left_natural ha]

theorem ordinalAdd_natCast (m n : ℕ) : ordinalAdd (m : V) (n : V) = ((m + n : ℕ) : V) := by
  induction n with
  | zero => simpa only [Nat.add_zero, show ((0 : ℕ) : V) = ∅ from rfl] using ordinalAdd_zero (m : V)
  | succ n ih =>
    let := IsOrdinal.of_mem (by simp : (m : V) ∈ ω)
    let := IsOrdinal.of_mem (by simp : (n : V) ∈ ω)
    rw [num_succ_def, ordinalAdd_succ, ih, ← num_succ_def]
    rfl

theorem naturalMul_natCast (m n : ℕ) : naturalMul (m : V) (n : V) = ((m * n : ℕ) : V) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [num_succ_def, naturalMul_succ _ (by simp), ih, ordinalAdd_natCast]
    exact congrArg (fun k : ℕ ↦ (k : V)) (Nat.mul_succ m n).symm

end ZFVP
