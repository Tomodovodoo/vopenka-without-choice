import ZFVP.SetTheory.DyadicRationals
import ZFVP.SetTheory.CantorSpace

/-! The numerator of an internal binary prefix, computed by internal recursion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def binaryNumeratorStepFormula : SetTheorySemisentence 3 :=
  f“z c p. z = !kpair.dfn (!succ.dfn (!kpair.π₁.dfn p))
    (!ordinalAddFormula (!ordinalAddFormula (!kpair.π₂.dfn p) (!kpair.π₂.dfn p))
      (!value.dfn c (!kpair.π₁.dfn p)))”

def binaryNumeratorRecStepFormula : SetTheorySemisentence 3 :=
  f“z c g. (!domain.dfn g = !isEmpty ∧ z = !kpair.dfn (!isEmpty) (!isEmpty)) ∨
    (!domain.dfn g ≠ !isEmpty ∧ z = !binaryNumeratorStepFormula c
      (!value.dfn g (!sUnion.dfn (!domain.dfn g))))”

def binaryNumeratorStateFormula : SetTheorySemisentence 3 :=
  parameterRecursionFormula binaryNumeratorRecStepFormula

def binaryNumeratorFormula : SetTheorySemisentence 3 :=
  f“a c n. a = !kpair.π₂.dfn (!binaryNumeratorStateFormula c n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryNumeratorStep (c p : V) : V :=
  ⟨succ (kpair.π₁ p), ordinalAdd (ordinalAdd (kpair.π₂ p) (kpair.π₂ p)) (c ‘ (kpair.π₁ p))⟩ₖ

instance binaryNumeratorStepFormula_defined :
    ℒₛₑₜ-function₂[V] binaryNumeratorStep via binaryNumeratorStepFormula :=
  ⟨fun v ↦ by simp [binaryNumeratorStepFormula, binaryNumeratorStep]⟩

instance binaryNumeratorStep_definable : ℒₛₑₜ-function₂[V] binaryNumeratorStep :=
  binaryNumeratorStepFormula_defined.to_definable

noncomputable def binaryNumeratorRecStep (c g : V) : V :=
  naturalIterationStep (binaryNumeratorStep c) ⟨0, 0⟩ₖ g

instance binaryNumeratorRecStepFormula_defined :
    ℒₛₑₜ-function₂[V] binaryNumeratorRecStep via binaryNumeratorRecStepFormula :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = 0
    · simp_all [binaryNumeratorRecStepFormula, binaryNumeratorRecStep, naturalIterationStep, zero_def]
    · simp_all [binaryNumeratorRecStepFormula, binaryNumeratorRecStep, naturalIterationStep,
        zero_def, -ne_empty_iff_isNonempty]⟩

instance binaryNumeratorRecStep_definable : ℒₛₑₜ-function₂[V] binaryNumeratorRecStep :=
  binaryNumeratorRecStepFormula_defined.to_definable

noncomputable def binaryNumeratorState (c n : V) : V :=
  naturalIteration (binaryNumeratorStep c) (by definability) ⟨0, 0⟩ₖ n

instance binaryNumeratorStateFormula_defined :
    ℒₛₑₜ-function₂[V] binaryNumeratorState via binaryNumeratorStateFormula :=
  parameterRecursionFormula_defined binaryNumeratorRecStep binaryNumeratorRecStepFormula

instance binaryNumeratorState_definable : ℒₛₑₜ-function₂[V] binaryNumeratorState :=
  binaryNumeratorStateFormula_defined.to_definable

noncomputable def binaryNumerator (c n : V) : V := kpair.π₂ (binaryNumeratorState c n)

instance binaryNumeratorFormula_defined :
    ℒₛₑₜ-function₂[V] binaryNumerator via binaryNumeratorFormula :=
  ⟨fun v ↦ by simp [binaryNumeratorFormula, binaryNumerator]⟩

instance binaryNumerator_definable : ℒₛₑₜ-function₂[V] binaryNumerator :=
  binaryNumeratorFormula_defined.to_definable

@[simp] theorem binaryNumeratorState_zero (c : V) : binaryNumeratorState c 0 = ⟨0, 0⟩ₖ :=
  naturalIteration_zero _ _ _

theorem binaryNumeratorState_succ (c : V) {n : V} (hn : n ∈ (ω : V)) :
    binaryNumeratorState c (succ n) = binaryNumeratorStep c (binaryNumeratorState c n) :=
  naturalIteration_succ _ _ _ hn

theorem binaryNumeratorState_index (c : V) {n : V} (hn : n ∈ (ω : V)) :
    kpair.π₁ (binaryNumeratorState c n) = n := by
  apply naturalNumber_induction (fun n ↦ kpair.π₁ (binaryNumeratorState c n) = n)
    (by definability) ?_ ?_ n hn
  · simp
  · intro n hn ih
    rw [binaryNumeratorState_succ _ hn]
    simp only [binaryNumeratorStep, kpair.π₁_kpair, ih]

@[simp] theorem binaryNumerator_zero (c : V) : binaryNumerator c 0 = 0 := by
  simp [binaryNumerator]

theorem binaryNumerator_succ (c : V) {n : V} (hn : n ∈ (ω : V)) :
    binaryNumerator c (succ n) = ordinalAdd (ordinalAdd (binaryNumerator c n)
      (binaryNumerator c n)) (c ‘ n) := by
  simp only [binaryNumerator, binaryNumeratorState_succ _ hn, binaryNumeratorStep,
    kpair.π₂_kpair, binaryNumeratorState_index _ hn]

namespace InternalNatural

theorem add_one_le_of_lt {a b : InternalNatural V} (hab : a < b) : a + 1 ≤ b := by
  change ordinalAdd a.val 1 ⊆ b.val
  rw [ordinalAdd_one_natural a.property]
  intro z hz
  rcases mem_succ_iff.mp hz with rfl | hz
  · exact hab
  · exact IsOrdinal.toIsTransitive.mem_trans hz hab

theorem double_add_bit_lt {a b i : InternalNatural V} (hab : a < b) (hi : i < 2) :
    a + a + i < b + b := by
  calc
    a + a + i < a + a + 2 := add_lt_add_right hi _
    _ = (a + 1) + (a + 1) := by ring
    _ ≤ b + b := add_le_add (add_one_le_of_lt hab) (add_one_le_of_lt hab)

end InternalNatural

theorem binaryNumerator_bound (c : V) {n : V} (hn : n ∈ (ω : V))
    (hc : ∀ i ∈ n, c ‘ i ∈ (2 : V)) :
    binaryNumerator c n ∈ (ω : V) ∧ binaryNumerator c n ∈ naturalPow (2 : V) n := by
  apply naturalNumber_induction
    (fun n ↦ (∀ i ∈ n, c ‘ i ∈ (2 : V)) →
      binaryNumerator c n ∈ (ω : V) ∧ binaryNumerator c n ∈ naturalPow (2 : V) n)
    (by definability) ?_ ?_ n hn hc
  · intro _
    simp
  · intro n hn ih hc
    obtain ⟨ha, hlt⟩ := ih (fun i hi ↦ hc i (mem_succ_iff.mpr (Or.inr hi)))
    have hbit := hc n (mem_succ_self n)
    have hbitω : c ‘ n ∈ (ω : V) := IsTransitive.ω.transitive _ (by simp) _ hbit
    have hp := naturalPow_natural (show (2 : V) ∈ ω by simp) hn
    rw [binaryNumerator_succ _ hn, naturalPow_succ _ hn, naturalMul_two hp]
    refine ⟨ordinalAdd_natural (ordinalAdd_natural ha ha) hbitω, ?_⟩
    exact InternalNatural.double_add_bit_lt
      (a := (⟨binaryNumerator c n, ha⟩ : InternalNatural V))
      (b := (⟨naturalPow (2 : V) n, hp⟩ : InternalNatural V))
      (i := (⟨c ‘ n, hbitω⟩ : InternalNatural V)) hlt hbit

theorem binaryNumerator_bound_of_cantor {c n : V} (hc : c ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    binaryNumerator c n ∈ (ω : V) ∧ binaryNumerator c n ∈ naturalPow (2 : V) n :=
  binaryNumerator_bound c hn (fun _ hi ↦ function_value_mem hc (IsTransitive.ω.transitive _ hn _ hi))

theorem binaryNumerator_eq_of_agree (c d : V) {n : V} (hn : n ∈ (ω : V))
    (h : ∀ i ∈ n, c ‘ i = d ‘ i) : binaryNumerator c n = binaryNumerator d n := by
  apply naturalNumber_induction
    (fun n ↦ (∀ i ∈ n, c ‘ i = d ‘ i) → binaryNumerator c n = binaryNumerator d n)
    (by definability) ?_ ?_ n hn h
  · intro _
    simp
  · intro n hn ih h
    rw [binaryNumerator_succ _ hn, binaryNumerator_succ _ hn,
      ih (fun i hi ↦ h i (mem_succ_iff.mpr (Or.inr hi))), h n (mem_succ_self n)]

theorem binaryNumerator_restrict {c n : V} (hc : c ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    binaryNumerator (c ↾ n) n = binaryNumerator c n := by
  let := IsFunction.of_mem hc
  apply binaryNumerator_eq_of_agree _ _ hn
  intro i hi
  apply value_restrict _ hi
  rw [domain_eq_of_mem_function hc]
  exact IsTransitive.ω.transitive _ hn _ hi

end ZFVP
