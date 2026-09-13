import ZFVP.SetTheory.ExtendedRealAddition
import ZFVP.SetTheory.RealNullPadding
import ZFVP.SetTheory.NaturalIteration
import ZFVP.SetTheory.UniformParameterizedRecursion

/-! Extended nonnegative cut sums through the model's whole omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def extendedSumNextFormula : SetTheorySemisentence 3 :=
  f“q f p. q = !kpair.dfn (!succ.dfn (!kpair.π₁.dfn p))
    (!extendedRealAddFormula (!kpair.π₂.dfn p) (!value.dfn f (!kpair.π₁.dfn p)))”

def extendedSumRecStepFormula : SetTheorySemisentence 3 :=
  f“z f g. (!domain.dfn g = !isEmpty ∧ z = !kpair.dfn (!isEmpty) ((!rationalCutFormula (!rationalZeroFormula)))) ∨
    (!domain.dfn g ≠ !isEmpty ∧ z = !extendedSumNextFormula f
      (!value.dfn g (!sUnion.dfn (!domain.dfn g))))”

def extendedSumStateFormula : SetTheorySemisentence 3 :=
  parameterRecursionFormula extendedSumRecStepFormula

def extendedPartialSumFormula : SetTheorySemisentence 3 :=
  f“q f n. q = !kpair.π₂.dfn (!extendedSumStateFormula f n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def extendedSumNext (f p : V) : V :=
  ⟨succ (kpair.π₁ p), extendedRealAdd (kpair.π₂ p) (f ‘ (kpair.π₁ p))⟩ₖ

instance extendedSumNextFormula_defined :
    ℒₛₑₜ-function₂[V] extendedSumNext via extendedSumNextFormula :=
  ⟨fun v ↦ by simp [extendedSumNextFormula, extendedSumNext]⟩

instance extendedSumNext_definable : ℒₛₑₜ-function₂[V] extendedSumNext :=
  extendedSumNextFormula_defined.to_definable

noncomputable def extendedSumRecStep (f g : V) : V :=
  naturalIterationStep (extendedSumNext f) ⟨0, rationalCut (rationalZero V)⟩ₖ g

instance extendedSumRecStepFormula_defined :
    ℒₛₑₜ-function₂[V] extendedSumRecStep via extendedSumRecStepFormula :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = 0
    · simp_all [extendedSumRecStepFormula, extendedSumRecStep, naturalIterationStep, zero_def]
    · simp_all [extendedSumRecStepFormula, extendedSumRecStep, naturalIterationStep,
        zero_def, -ne_empty_iff_isNonempty]⟩

instance extendedSumRecStep_definable : ℒₛₑₜ-function₂[V] extendedSumRecStep :=
  extendedSumRecStepFormula_defined.to_definable

noncomputable def extendedSumState (f n : V) : V :=
  naturalIteration (extendedSumNext f) (by definability) ⟨0, rationalCut (rationalZero V)⟩ₖ n

instance extendedSumStateFormula_defined :
    ℒₛₑₜ-function₂[V] extendedSumState via extendedSumStateFormula :=
  parameterRecursionFormula_defined extendedSumRecStep extendedSumRecStepFormula

instance extendedSumState_definable : ℒₛₑₜ-function₂[V] extendedSumState :=
  extendedSumStateFormula_defined.to_definable

noncomputable def extendedPartialSum (f n : V) : V := kpair.π₂ (extendedSumState f n)

instance extendedPartialSumFormula_defined :
    ℒₛₑₜ-function₂[V] extendedPartialSum via extendedPartialSumFormula :=
  ⟨fun v ↦ by simp [extendedPartialSumFormula, extendedPartialSum]⟩

instance extendedPartialSum_definable : ℒₛₑₜ-function₂[V] extendedPartialSum :=
  extendedPartialSumFormula_defined.to_definable

@[simp] theorem extendedSumState_zero (f : V) : extendedSumState f 0 = ⟨0, rationalCut (rationalZero V)⟩ₖ :=
  naturalIteration_zero _ _ _

theorem extendedSumState_succ (f : V) {n : V} (hn : n ∈ (ω : V)) :
    extendedSumState f (succ n) = extendedSumNext f (extendedSumState f n) :=
  naturalIteration_succ _ _ _ hn

theorem extendedSumState_index (f : V) {n : V} (hn : n ∈ (ω : V)) :
    kpair.π₁ (extendedSumState f n) = n := by
  apply naturalNumber_induction (fun n ↦ kpair.π₁ (extendedSumState f n) = n) (by definability) ?_ ?_ n hn
  · simp
  · intro n hn ih
    simp only [extendedSumState_succ _ hn, extendedSumNext, kpair.π₁_kpair, ih]

@[simp] theorem extendedPartialSum_zero (f : V) : extendedPartialSum f 0 = rationalCut (rationalZero V) := by
  simp [extendedPartialSum]

theorem extendedPartialSum_succ (f : V) {n : V} (hn : n ∈ (ω : V)) :
    extendedPartialSum f (succ n) = extendedRealAdd (extendedPartialSum f n) (f ‘ n) := by
  simp only [extendedPartialSum, extendedSumState_succ _ hn, extendedSumNext,
    kpair.π₂_kpair, extendedSumState_index _ hn]


theorem extendedZero_extended : IsExtendedNonnegativeReal (rationalCut (rationalZero V)) := by
  rw [← realOuterMeasure_empty]
  exact realOuterMeasure_extended _

theorem extendedPartialSum_extended {f : V}
    (hf : ∀ n ∈ (ω : V), IsExtendedNonnegativeReal (f ‘ n)) :
    ∀ n ∈ (ω : V), IsExtendedNonnegativeReal (extendedPartialSum f n) := by
  apply naturalNumber_induction (fun n ↦ IsExtendedNonnegativeReal (extendedPartialSum f n)) (by definability)
  · simpa only [extendedPartialSum_zero] using (extendedZero_extended (V := V))
  · intro n hn ih
    rw [extendedPartialSum_succ _ hn]
    exact extendedRealAdd_extended ih (hf n hn)

theorem extendedPartialSum_step_mono {f n : V}
    (hf : ∀ i ∈ (ω : V), IsExtendedNonnegativeReal (f ‘ i)) (hn : n ∈ (ω : V)) :
    extendedPartialSum f n ⊆ extendedPartialSum f (succ n) := by
  rw [extendedPartialSum_succ _ hn]
  exact extendedRealAdd_le_left (extendedPartialSum_extended hf n hn) (hf n hn)

noncomputable def extendedSeries (f : V) : V :=
  {q ∈ internalRationals V ; ∃ n ∈ (ω : V), q ∈ extendedPartialSum f n}

theorem mem_extendedSeries_iff (f q : V) : q ∈ extendedSeries f ↔
    q ∈ internalRationals V ∧ ∃ n ∈ (ω : V), q ∈ extendedPartialSum f n := by
  simp [extendedSeries]

instance extendedSeries_definable : ℒₛₑₜ-function₁[V] extendedSeries := by
  have h : ℒₛₑₜ-relation[V] (fun S f ↦ ∀ q, q ∈ S ↔ q ∈ internalRationals V ∧
    ∃ n ∈ (ω : V), q ∈ extendedPartialSum f n) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_extendedSeries_iff]

theorem extendedPartialSum_subset_series {f n : V}
    (hf : ∀ i ∈ (ω : V), IsExtendedNonnegativeReal (f ‘ i)) (hn : n ∈ (ω : V)) :
    extendedPartialSum f n ⊆ extendedSeries f := by
  intro q hq
  exact (mem_extendedSeries_iff _ _).mpr ⟨(extendedPartialSum_extended hf n hn).1 q hq, n, hn, hq⟩

theorem extendedSeries_extended {f : V}
    (hf : ∀ i ∈ (ω : V), IsExtendedNonnegativeReal (f ‘ i)) :
    IsExtendedNonnegativeReal (extendedSeries f) := by
  refine ⟨fun q hq ↦ ((mem_extendedSeries_iff _ _).mp hq).1, ?_, ?_, ?_⟩
  · intro q hq
    exact (mem_extendedSeries_iff _ _).mpr
      ⟨(extendedZero_extended (V := V)).1 q hq, 0, by simp, by simpa using hq⟩
  · intro q hq p hp hpq
    obtain ⟨_, n, hn, hqn⟩ := (mem_extendedSeries_iff _ _).mp hq
    exact (mem_extendedSeries_iff _ _).mpr
      ⟨hp, n, hn, (extendedPartialSum_extended hf n hn).2.2.1 q hqn p hp hpq⟩
  · intro q hq
    obtain ⟨_, n, hn, hqn⟩ := (mem_extendedSeries_iff _ _).mp hq
    obtain ⟨r, hr, hqr⟩ := (extendedPartialSum_extended hf n hn).2.2.2 q hqn
    exact ⟨r, extendedPartialSum_subset_series hf hn r hr, hqr⟩

/-- Addition commutes with the supremum of internal partial sums, also at infinity. -/
theorem extendedSeries_add_le {f c U : V}
    (hbound : ∀ n ∈ (ω : V), extendedRealAdd (extendedPartialSum f n) c ⊆ U) :
    extendedRealAdd (extendedSeries f) c ⊆ U := by
  intro q hq
  obtain ⟨hqQ, p, hp, r, hr, he⟩ := (mem_extendedRealAdd_iff _ _ _).mp hq
  obtain ⟨_, n, hn, hpn⟩ := (mem_extendedSeries_iff _ _).mp hp
  exact hbound n hn q ((mem_extendedRealAdd_iff _ _ _).mpr ⟨hqQ, p, hpn, r, hr, he⟩)

theorem extendedSeries_term_subset {f i : V}
    (hf : ∀ n ∈ (ω : V), IsExtendedNonnegativeReal (f ‘ n)) (hi : i ∈ (ω : V)) :
    f ‘ i ⊆ extendedSeries f := by
  apply subset_trans (extendedRealAdd_le_right (extendedPartialSum_extended hf i hi) (hf i hi))
  rw [← extendedPartialSum_succ _ hi]
  exact extendedPartialSum_subset_series hf (ω_succ_closed hi)

theorem rationalPartialSum_cut_subset_extended {a f : V}
    (ha : ∀ i ∈ (ω : V), a ‘ i ∈ internalRationals V)
    (hf : ∀ i ∈ (ω : V), IsExtendedNonnegativeReal (f ‘ i))
    (haf : ∀ i ∈ (ω : V), a ‘ i ∈ f ‘ i) :
    ∀ n ∈ (ω : V), rationalCut (rationalPartialSum a n) ⊆ extendedPartialSum f n := by
  apply naturalNumber_induction
    (fun n ↦ rationalCut (rationalPartialSum a n) ⊆ extendedPartialSum f n) (by definability)
  · simp only [rationalPartialSum_zero, extendedPartialSum_zero]
    exact fun _ h ↦ h
  · intro n hn ih
    rw [rationalPartialSum_succ _ hn, extendedPartialSum_succ _ hn]
    have hcut : rationalCut (a ‘ n) ⊆ f ‘ n := by
      intro q hq
      obtain ⟨hqQ, hqa⟩ := (mem_rationalCut_iff _ _).mp hq
      exact (hf n hn).2.2.1 _ (haf n hn) q hqQ hqa
    have h := extendedRealAdd_mono ih hcut
    rw [extendedRealAdd_rationalCuts ⟨_, rationalPartialSum_mem ha n hn⟩ ⟨_, ha n hn⟩] at h
    exact h

end ZFVP
