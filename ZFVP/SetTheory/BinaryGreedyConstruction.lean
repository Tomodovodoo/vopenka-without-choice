import ZFVP.SetTheory.BinaryExpansionReals

/-! A uniformly definable greedy binary sequence for an internal real cut. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def binaryGreedyMidFormula : SetTheorySemisentence 2 :=
  f“q p. q = !rationalAddFormula (!kpair.π₂.dfn p) (!dyadicUnitFormula (!succ.dfn (!kpair.π₁.dfn p)))”

def binaryGreedyDigitFormula : SetTheorySemisentence 3 :=
  f“d x p. ∀ z, z ∈ d ↔ z ∈ !succ.dfn (!isEmpty) ∧
    !rationalCutFormula (!binaryGreedyMidFormula p) ⊆ x”

def binaryGreedyNextFormula : SetTheorySemisentence 3 :=
  f“q x p. q = !kpair.dfn (!succ.dfn (!kpair.π₁.dfn p))
    (!rationalAddFormula (!kpair.π₂.dfn p)
      (!rationalMulFormula (!rationalNaturalFormula (!binaryGreedyDigitFormula x p))
        (!dyadicUnitFormula (!succ.dfn (!kpair.π₁.dfn p)))))”

def binaryGreedyRecStepFormula : SetTheorySemisentence 3 :=
  f“z x g. (!domain.dfn g = !isEmpty ∧ z = !kpair.dfn (!isEmpty) (!rationalZeroFormula)) ∨
    (!domain.dfn g ≠ !isEmpty ∧ z = !binaryGreedyNextFormula x
      (!value.dfn g (!sUnion.dfn (!domain.dfn g))))”

def binaryGreedyStateFormula : SetTheorySemisentence 3 :=
  parameterRecursionFormula binaryGreedyRecStepFormula

def binaryGreedyValueFormula : SetTheorySemisentence 3 :=
  f“q x n. q = !kpair.π₂.dfn (!binaryGreedyStateFormula x n)”

def binaryGreedyDigitAtFormula : SetTheorySemisentence 3 :=
  f“d x n. d = !binaryGreedyDigitFormula x (!binaryGreedyStateFormula x n)”

def binaryGreedyFormula : SetTheorySemisentence 2 :=
  f“c x. ∀ p, p ∈ c ↔ ∃ n ∈ !isω, p = !kpair.dfn n (!binaryGreedyDigitAtFormula x n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryGreedyMid (p : V) : V :=
  rationalAdd (kpair.π₂ p) (dyadicUnit (succ (kpair.π₁ p)))

instance binaryGreedyMidFormula_defined : ℒₛₑₜ-function₁[V] binaryGreedyMid via binaryGreedyMidFormula :=
  ⟨fun v ↦ by simp [binaryGreedyMidFormula, binaryGreedyMid]⟩

instance binaryGreedyMid_definable : ℒₛₑₜ-function₁[V] binaryGreedyMid :=
  binaryGreedyMidFormula_defined.to_definable

noncomputable def binaryGreedyDigit (x p : V) : V :=
  {z ∈ (1 : V) ; rationalCut (binaryGreedyMid p) ⊆ x}

instance binaryGreedyDigitFormula_defined :
    ℒₛₑₜ-function₂[V] binaryGreedyDigit via binaryGreedyDigitFormula :=
  ⟨fun v ↦ by
    have h1 : (1 : V) = succ ∅ := rfl
    change binaryGreedyDigitFormula.Evalb v ↔ v 0 = binaryGreedyDigit (v 1) (v 2)
    rw [mem_ext_iff]
    simp [binaryGreedyDigitFormula, binaryGreedyDigit, h1]⟩

instance binaryGreedyDigit_definable : ℒₛₑₜ-function₂[V] binaryGreedyDigit :=
  binaryGreedyDigitFormula_defined.to_definable

theorem binaryGreedyDigit_eq_one {x p : V} (h : rationalCut (binaryGreedyMid p) ⊆ x) :
    binaryGreedyDigit x p = 1 := by
  apply mem_ext
  intro z
  simp [binaryGreedyDigit, h]

theorem binaryGreedyDigit_eq_zero {x p : V} (h : ¬rationalCut (binaryGreedyMid p) ⊆ x) :
    binaryGreedyDigit x p = 0 := by
  apply mem_ext
  intro z
  simp [binaryGreedyDigit, h, zero_def]

theorem binaryGreedyDigit_mem_two (x p : V) : binaryGreedyDigit x p ∈ (2 : V) := by
  by_cases h : rationalCut (binaryGreedyMid p) ⊆ x
  · rw [binaryGreedyDigit_eq_one h]
    simp
  · rw [binaryGreedyDigit_eq_zero h]
    simp

noncomputable def binaryGreedyNext (x p : V) : V :=
  ⟨succ (kpair.π₁ p), rationalAdd (kpair.π₂ p)
    (rationalMul (rationalNatural (binaryGreedyDigit x p)) (dyadicUnit (succ (kpair.π₁ p))))⟩ₖ

instance binaryGreedyNextFormula_defined :
    ℒₛₑₜ-function₂[V] binaryGreedyNext via binaryGreedyNextFormula :=
  ⟨fun v ↦ by simp [binaryGreedyNextFormula, binaryGreedyNext]⟩

instance binaryGreedyNext_definable : ℒₛₑₜ-function₂[V] binaryGreedyNext :=
  binaryGreedyNextFormula_defined.to_definable

noncomputable def binaryGreedyRecStep (x g : V) : V :=
  naturalIterationStep (binaryGreedyNext x) ⟨0, rationalZero V⟩ₖ g

instance binaryGreedyRecStepFormula_defined :
    ℒₛₑₜ-function₂[V] binaryGreedyRecStep via binaryGreedyRecStepFormula :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = 0
    · simp_all [binaryGreedyRecStepFormula, binaryGreedyRecStep, naturalIterationStep, zero_def]
    · simp_all [binaryGreedyRecStepFormula, binaryGreedyRecStep, naturalIterationStep,
        zero_def, -ne_empty_iff_isNonempty]⟩

instance binaryGreedyRecStep_definable : ℒₛₑₜ-function₂[V] binaryGreedyRecStep :=
  binaryGreedyRecStepFormula_defined.to_definable

noncomputable def binaryGreedyState (x n : V) : V :=
  naturalIteration (binaryGreedyNext x) (by definability) ⟨0, rationalZero V⟩ₖ n

instance binaryGreedyStateFormula_defined :
    ℒₛₑₜ-function₂[V] binaryGreedyState via binaryGreedyStateFormula :=
  parameterRecursionFormula_defined binaryGreedyRecStep binaryGreedyRecStepFormula

instance binaryGreedyState_definable : ℒₛₑₜ-function₂[V] binaryGreedyState :=
  binaryGreedyStateFormula_defined.to_definable

noncomputable def binaryGreedyValue (x n : V) : V := kpair.π₂ (binaryGreedyState x n)

instance binaryGreedyValueFormula_defined :
    ℒₛₑₜ-function₂[V] binaryGreedyValue via binaryGreedyValueFormula :=
  ⟨fun v ↦ by simp [binaryGreedyValueFormula, binaryGreedyValue]⟩

instance binaryGreedyValue_definable : ℒₛₑₜ-function₂[V] binaryGreedyValue :=
  binaryGreedyValueFormula_defined.to_definable

noncomputable def binaryGreedyDigitAt (x n : V) : V := binaryGreedyDigit x (binaryGreedyState x n)

instance binaryGreedyDigitAtFormula_defined :
    ℒₛₑₜ-function₂[V] binaryGreedyDigitAt via binaryGreedyDigitAtFormula :=
  ⟨fun v ↦ by simp [binaryGreedyDigitAtFormula, binaryGreedyDigitAt]⟩

instance binaryGreedyDigitAt_definable : ℒₛₑₜ-function₂[V] binaryGreedyDigitAt :=
  binaryGreedyDigitAtFormula_defined.to_definable

noncomputable def binaryGreedy (x : V) : V :=
  definableGraph (ω : V) (binaryGreedyDigitAt x) (by definability)

instance binaryGreedyFormula_defined : ℒₛₑₜ-function₁[V] binaryGreedy via binaryGreedyFormula :=
  ⟨fun v ↦ by
    change binaryGreedyFormula.Evalb v ↔ v 0 = binaryGreedy (v 1)
    rw [mem_ext_iff]
    simp [binaryGreedyFormula, binaryGreedy, mem_definableGraph_iff]⟩

instance binaryGreedy_definable : ℒₛₑₜ-function₁[V] binaryGreedy := binaryGreedyFormula_defined.to_definable

theorem binaryGreedy_mem (x : V) : binaryGreedy x ∈ cantorSpace V :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun n _ ↦ binaryGreedyDigit_mem_two x (binaryGreedyState x n))

theorem binaryGreedy_value (x : V) {n : V} (hn : n ∈ (ω : V)) :
    (binaryGreedy x) ‘ n = binaryGreedyDigitAt x n := value_definableGraph _ _ _ hn

@[simp] theorem binaryGreedyState_zero (x : V) : binaryGreedyState x 0 = ⟨0, rationalZero V⟩ₖ :=
  naturalIteration_zero _ _ _

theorem binaryGreedyState_succ (x : V) {n : V} (hn : n ∈ (ω : V)) :
    binaryGreedyState x (succ n) = binaryGreedyNext x (binaryGreedyState x n) :=
  naturalIteration_succ _ _ _ hn

theorem binaryGreedyState_index (x : V) {n : V} (hn : n ∈ (ω : V)) :
    kpair.π₁ (binaryGreedyState x n) = n := by
  apply naturalNumber_induction (fun n ↦ kpair.π₁ (binaryGreedyState x n) = n)
    (by definability) ?_ ?_ n hn
  · simp
  · intro n hn ih
    rw [binaryGreedyState_succ _ hn]
    simp only [binaryGreedyNext, kpair.π₁_kpair, ih]

@[simp] theorem binaryGreedyValue_zero (x : V) : binaryGreedyValue x 0 = rationalZero V := by
  simp [binaryGreedyValue]

theorem binaryGreedyValue_succ (x : V) {n : V} (hn : n ∈ (ω : V)) :
    binaryGreedyValue x (succ n) = rationalAdd (binaryGreedyValue x n)
      (rationalMul (rationalNatural (binaryGreedyDigitAt x n)) (dyadicUnit (succ n))) := by
  simp only [binaryGreedyValue, binaryGreedyState_succ _ hn, binaryGreedyNext,
    kpair.π₂_kpair, binaryGreedyState_index _ hn, binaryGreedyDigitAt]

theorem binaryValue_succ {c n : V} (hc : c ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    binaryValue c (succ n) = rationalAdd (binaryValue c n)
      (rationalMul (rationalNatural (c ‘ n)) (dyadicUnit (succ n))) := by
  have h := congrArg Subtype.val (InternalRational.binaryApprox_succ c hc (⟨n, hn⟩ : InternalNatural V))
  change binaryValue c (ordinalAdd n 1) = rationalAdd (binaryValue c n)
    (rationalMul (rationalNatural (c ‘ n)) (dyadicUnit (ordinalAdd n 1))) at h
  rwa [ordinalAdd_one_natural hn] at h

theorem binaryGreedyValue_eq_binaryValue (x : V) {n : V} (hn : n ∈ (ω : V)) :
    binaryGreedyValue x n = binaryValue (binaryGreedy x) n := by
  apply naturalNumber_induction (fun n ↦ binaryGreedyValue x n = binaryValue (binaryGreedy x) n)
    (by definability) ?_ ?_ n hn
  · rw [binaryGreedyValue_zero, binaryValue_zero]
  · intro n hn ih
    rw [binaryGreedyValue_succ _ hn, binaryValue_succ (binaryGreedy_mem x) hn,
      binaryGreedy_value _ hn, ih]

theorem binaryGreedyValue_mem (x : V) {n : V} (hn : n ∈ (ω : V)) :
    binaryGreedyValue x n ∈ internalRationals V := by
  rw [binaryGreedyValue_eq_binaryValue _ hn]
  exact binaryValue_mem (binaryGreedy_mem x) hn

end ZFVP
