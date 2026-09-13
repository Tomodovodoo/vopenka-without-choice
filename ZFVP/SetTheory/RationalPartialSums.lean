import ZFVP.SetTheory.InternalRationalField
import ZFVP.SetTheory.NaturalIteration
import ZFVP.SetTheory.UniformParameterizedRecursion

/-! Rational sequence sums through the model's whole omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rationalSumNextFormula : SetTheorySemisentence 3 :=
  f“q f p. q = !kpair.dfn (!succ.dfn (!kpair.π₁.dfn p))
    (!rationalAddFormula (!kpair.π₂.dfn p) (!value.dfn f (!kpair.π₁.dfn p)))”

def rationalSumRecStepFormula : SetTheorySemisentence 3 :=
  f“z f g. (!domain.dfn g = !isEmpty ∧ z = !kpair.dfn (!isEmpty) (!rationalZeroFormula)) ∨
    (!domain.dfn g ≠ !isEmpty ∧ z = !rationalSumNextFormula f
      (!value.dfn g (!sUnion.dfn (!domain.dfn g))))”

def rationalSumStateFormula : SetTheorySemisentence 3 :=
  parameterRecursionFormula rationalSumRecStepFormula

def rationalPartialSumFormula : SetTheorySemisentence 3 :=
  f“q f n. q = !kpair.π₂.dfn (!rationalSumStateFormula f n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rationalSumNext (f p : V) : V :=
  ⟨succ (kpair.π₁ p), rationalAdd (kpair.π₂ p) (f ‘ (kpair.π₁ p))⟩ₖ

instance rationalSumNextFormula_defined :
    ℒₛₑₜ-function₂[V] rationalSumNext via rationalSumNextFormula :=
  ⟨fun v ↦ by simp [rationalSumNextFormula, rationalSumNext]⟩

instance rationalSumNext_definable : ℒₛₑₜ-function₂[V] rationalSumNext :=
  rationalSumNextFormula_defined.to_definable

noncomputable def rationalSumRecStep (f g : V) : V :=
  naturalIterationStep (rationalSumNext f) ⟨0, rationalZero V⟩ₖ g

instance rationalSumRecStepFormula_defined :
    ℒₛₑₜ-function₂[V] rationalSumRecStep via rationalSumRecStepFormula :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = 0
    · simp_all [rationalSumRecStepFormula, rationalSumRecStep, naturalIterationStep, zero_def]
    · simp_all [rationalSumRecStepFormula, rationalSumRecStep, naturalIterationStep,
        zero_def, -ne_empty_iff_isNonempty]⟩

instance rationalSumRecStep_definable : ℒₛₑₜ-function₂[V] rationalSumRecStep :=
  rationalSumRecStepFormula_defined.to_definable

noncomputable def rationalSumState (f n : V) : V :=
  naturalIteration (rationalSumNext f) (by definability) ⟨0, rationalZero V⟩ₖ n

instance rationalSumStateFormula_defined :
    ℒₛₑₜ-function₂[V] rationalSumState via rationalSumStateFormula :=
  parameterRecursionFormula_defined rationalSumRecStep rationalSumRecStepFormula

instance rationalSumState_definable : ℒₛₑₜ-function₂[V] rationalSumState :=
  rationalSumStateFormula_defined.to_definable

noncomputable def rationalPartialSum (f n : V) : V := kpair.π₂ (rationalSumState f n)

instance rationalPartialSumFormula_defined :
    ℒₛₑₜ-function₂[V] rationalPartialSum via rationalPartialSumFormula :=
  ⟨fun v ↦ by simp [rationalPartialSumFormula, rationalPartialSum]⟩

instance rationalPartialSum_definable : ℒₛₑₜ-function₂[V] rationalPartialSum :=
  rationalPartialSumFormula_defined.to_definable

@[simp] theorem rationalSumState_zero (f : V) : rationalSumState f 0 = ⟨0, rationalZero V⟩ₖ :=
  naturalIteration_zero _ _ _

theorem rationalSumState_succ (f : V) {n : V} (hn : n ∈ (ω : V)) :
    rationalSumState f (succ n) = rationalSumNext f (rationalSumState f n) :=
  naturalIteration_succ _ _ _ hn

theorem rationalSumState_index (f : V) {n : V} (hn : n ∈ (ω : V)) :
    kpair.π₁ (rationalSumState f n) = n := by
  apply naturalNumber_induction (fun n ↦ kpair.π₁ (rationalSumState f n) = n) (by definability) ?_ ?_ n hn
  · simp
  · intro n hn ih
    simp only [rationalSumState_succ _ hn, rationalSumNext, kpair.π₁_kpair, ih]

@[simp] theorem rationalPartialSum_zero (f : V) : rationalPartialSum f 0 = rationalZero V := by
  simp [rationalPartialSum]

theorem rationalPartialSum_succ (f : V) {n : V} (hn : n ∈ (ω : V)) :
    rationalPartialSum f (succ n) = rationalAdd (rationalPartialSum f n) (f ‘ n) := by
  simp only [rationalPartialSum, rationalSumState_succ _ hn, rationalSumNext,
    kpair.π₂_kpair, rationalSumState_index _ hn]

theorem rationalPartialSum_mem {f : V} (hf : ∀ n ∈ (ω : V), f ‘ n ∈ internalRationals V) :
    ∀ n ∈ (ω : V), rationalPartialSum f n ∈ internalRationals V := by
  apply naturalNumber_induction (fun n ↦ rationalPartialSum f n ∈ internalRationals V) (by definability)
  · simpa only [rationalPartialSum_zero] using rationalZero_mem (V := V)
  · intro n hn ih
    rw [rationalPartialSum_succ _ hn]
    exact rationalAdd_mem ih (hf n hn)

theorem rationalPartialSum_congr {f g : V}
    (hfg : ∀ n ∈ (ω : V), f ‘ n = g ‘ n) :
    ∀ n ∈ (ω : V), rationalPartialSum f n = rationalPartialSum g n := by
  apply naturalNumber_induction (fun n ↦ rationalPartialSum f n = rationalPartialSum g n) (by definability)
  · simp only [rationalPartialSum_zero]
  · intro n hn ih
    rw [rationalPartialSum_succ _ hn, rationalPartialSum_succ _ hn, ih, hfg n hn]

theorem rationalPartialSum_nonnegative {f : V}
    (hf : ∀ n ∈ (ω : V), f ‘ n ∈ internalRationals V)
    (hpos : ∀ n ∈ (ω : V), ¬ InternalRationalLT (f ‘ n) (rationalZero V)) :
    ∀ n ∈ (ω : V), ¬ InternalRationalLT (rationalPartialSum f n) (rationalZero V) := by
  apply naturalNumber_induction
    (fun n ↦ ¬ InternalRationalLT (rationalPartialSum f n) (rationalZero V)) (by definability)
  · rw [rationalPartialSum_zero]
    exact internalRationalLT_irrefl rationalZero_mem
  · intro n hn ih
    rw [rationalPartialSum_succ _ hn]
    exact (add_nonneg (show (0 : InternalRational V) ≤ ⟨rationalPartialSum f n, rationalPartialSum_mem hf n hn⟩ from ih)
      (show (0 : InternalRational V) ≤ ⟨f ‘ n, hf n hn⟩ from hpos n hn))

theorem rationalPartialSum_add {f g h : V}
    (hf : ∀ n ∈ (ω : V), f ‘ n ∈ internalRationals V)
    (hg : ∀ n ∈ (ω : V), g ‘ n ∈ internalRationals V)
    (hh : ∀ n ∈ (ω : V), h ‘ n = rationalAdd (f ‘ n) (g ‘ n)) :
    ∀ n ∈ (ω : V), rationalPartialSum h n =
      rationalAdd (rationalPartialSum f n) (rationalPartialSum g n) := by
  apply naturalNumber_induction
    (fun n ↦ rationalPartialSum h n = rationalAdd (rationalPartialSum f n) (rationalPartialSum g n))
    (by definability)
  · simp only [rationalPartialSum_zero, rationalAdd_zero rationalZero_mem]
  · intro n hn ih
    rw [rationalPartialSum_succ _ hn, rationalPartialSum_succ _ hn, rationalPartialSum_succ _ hn,
      ih, hh n hn]
    let a : InternalRational V := ⟨rationalPartialSum f n, rationalPartialSum_mem hf n hn⟩
    let b : InternalRational V := ⟨rationalPartialSum g n, rationalPartialSum_mem hg n hn⟩
    let c : InternalRational V := ⟨f ‘ n, hf n hn⟩
    let d : InternalRational V := ⟨g ‘ n, hg n hn⟩
    exact congrArg Subtype.val (show (a + b) + (c + d) = (a + c) + (b + d) from by ring)

end ZFVP
