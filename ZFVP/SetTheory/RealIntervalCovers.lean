import ZFVP.SetTheory.RationalPartialSumOrder
import ZFVP.SetTheory.RealRegularitySentences

/-! Genuine rational interval covers and their internally finite length sums. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def realIntervalLengthFormula : SetTheorySemisentence 2 :=
  f“q p. q = !rationalAddFormula (!kpair.π₂.dfn p) (!rationalNegFormula (!kpair.π₁.dfn p))”

def realCoverLengthsFormula : SetTheorySemisentence 2 :=
  f“f d. ∀ p, p ∈ f ↔ ∃ n ∈ !isω, p = !kpair.dfn n (!realIntervalLengthFormula (!value.dfn d n))”

def realCoverCostFormula : SetTheorySemisentence 3 :=
  f“q d n. q = !rationalPartialSumFormula (!realCoverLengthsFormula d) n”

def isRealIntervalCoverFormula : SetTheorySemisentence 2 :=
  f“d A. d ∈ !function.dfn (!realBasicCodesFormula) (!isω) ∧
    ∀ x ∈ A, ∃ n ∈ !isω, x ∈ !realIntervalFormula
      (!kpair.π₁.dfn (!value.dfn d n)) (!kpair.π₂.dfn (!value.dfn d n))”

def isRealNullFormula : SetTheorySemisentence 1 :=
  f“A. ∀ m ∈ !isω, ∃ d, !isRealIntervalCoverFormula d A ∧
    ∀ n ∈ !isω, ¬!internalRationalLTFormula (!dyadicUnitFormula m) (!realCoverCostFormula d n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realIntervalLength (p : V) : V :=
  rationalAdd (kpair.π₂ p) (rationalNeg (kpair.π₁ p))

instance realIntervalLengthFormula_defined :
    ℒₛₑₜ-function₁[V] realIntervalLength via realIntervalLengthFormula :=
  ⟨fun v ↦ by simp [realIntervalLengthFormula, realIntervalLength]⟩

instance realIntervalLength_definable : ℒₛₑₜ-function₁[V] realIntervalLength :=
  realIntervalLengthFormula_defined.to_definable

noncomputable def realCoverLengths (d : V) : V :=
  definableGraph (ω : V) (fun n ↦ realIntervalLength (d ‘ n)) (by definability)

instance realCoverLengthsFormula_defined :
    ℒₛₑₜ-function₁[V] realCoverLengths via realCoverLengthsFormula :=
  ⟨fun v ↦ by
    change realCoverLengthsFormula.Evalb v ↔ v 0 = realCoverLengths (v 1)
    rw [mem_ext_iff]
    simp [realCoverLengthsFormula, realCoverLengths, mem_definableGraph_iff]⟩

instance realCoverLengths_definable : ℒₛₑₜ-function₁[V] realCoverLengths :=
  realCoverLengthsFormula_defined.to_definable

noncomputable def realCoverCost (d n : V) : V := rationalPartialSum (realCoverLengths d) n

instance realCoverCostFormula_defined : ℒₛₑₜ-function₂[V] realCoverCost via realCoverCostFormula :=
  ⟨fun v ↦ by simp [realCoverCostFormula, realCoverCost]⟩

instance realCoverCost_definable : ℒₛₑₜ-function₂[V] realCoverCost := realCoverCostFormula_defined.to_definable

def IsRealIntervalCover (d A : V) : Prop := d ∈ (realBasicCodes V) ^ (ω : V) ∧
  ∀ x ∈ A, ∃ n ∈ (ω : V), x ∈ realInterval (kpair.π₁ (d ‘ n)) (kpair.π₂ (d ‘ n))

instance isRealIntervalCoverFormula_defined :
    ℒₛₑₜ-relation[V] IsRealIntervalCover via isRealIntervalCoverFormula :=
  ⟨fun v ↦ by simp [isRealIntervalCoverFormula, IsRealIntervalCover]⟩

instance isRealIntervalCover_definable : ℒₛₑₜ-relation[V] IsRealIntervalCover :=
  isRealIntervalCoverFormula_defined.to_definable

def IsRealNull (A : V) : Prop := ∀ m ∈ (ω : V), ∃ d, IsRealIntervalCover d A ∧
  ∀ n ∈ (ω : V), ¬ InternalRationalLT (dyadicUnit m) (realCoverCost d n)

instance isRealNullFormula_defined : ℒₛₑₜ-predicate[V] IsRealNull via isRealNullFormula :=
  ⟨fun v ↦ by simp [isRealNullFormula, IsRealNull]⟩

instance isRealNull_definable : ℒₛₑₜ-predicate[V] IsRealNull := isRealNullFormula_defined.to_definable

theorem realIntervalLength_mem {p : V} (hp : p ∈ realBasicCodes V) :
    realIntervalLength p ∈ internalRationals V := by
  obtain ⟨hpp, _⟩ := (mem_realBasicCodes_iff _).mp hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hpp
  simpa only [realIntervalLength, kpair.π₁_kpair, kpair.π₂_kpair] using
    rationalAdd_mem hb (rationalNeg_mem ha)

theorem realIntervalLength_pos {p : V} (hp : p ∈ realBasicCodes V) :
    InternalRationalLT (rationalZero V) (realIntervalLength p) := by
  obtain ⟨hpp, hab⟩ := (mem_realBasicCodes_iff _).mp hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hpp
  have h : (⟨a, ha⟩ : InternalRational V) < ⟨b, hb⟩ := by simpa using hab
  simp only [realIntervalLength, kpair.π₁_kpair, kpair.π₂_kpair]
  exact (sub_pos.mpr h : (0 : InternalRational V) < (⟨b, hb⟩ : InternalRational V) - ⟨a, ha⟩)

theorem realCoverCost_mem {d : V} (hd : d ∈ (realBasicCodes V) ^ (ω : V)) :
    ∀ n ∈ (ω : V), realCoverCost d n ∈ internalRationals V := by
  apply rationalPartialSum_mem
  intro n hn
  rw [realCoverLengths, value_definableGraph _ _ _ hn]
  exact realIntervalLength_mem (function_value_mem hd hn)

@[simp] theorem realCoverCost_zero (d : V) : realCoverCost d 0 = rationalZero V :=
  rationalPartialSum_zero _

theorem realCoverCost_succ (d : V) {n : V} (hn : n ∈ (ω : V)) :
    realCoverCost d (succ n) = rationalAdd (realCoverCost d n) (realIntervalLength (d ‘ n)) := by
  rw [realCoverCost, rationalPartialSum_succ _ hn, realCoverLengths, value_definableGraph _ _ _ hn]
  rfl

theorem realIntervalCover_subset_reals {d A : V} (hd : IsRealIntervalCover d A) :
    A ⊆ dedekindReals V := by
  intro x hx
  obtain ⟨n, _, hxn⟩ := hd.2 x hx
  exact realInterval_subset_reals _ _ x hxn

theorem realNull_subset_reals {A : V} (hA : IsRealNull A) : A ⊆ dedekindReals V := by
  obtain ⟨d, hd, _⟩ := hA 0 (by simp)
  exact realIntervalCover_subset_reals hd

theorem realNull_subset {A B : V} (hB : IsRealNull B) (hAB : A ⊆ B) : IsRealNull A := by
  intro m hm
  obtain ⟨d, hd, hcost⟩ := hB m hm
  exact ⟨d, ⟨hd.1, fun x hx ↦ hd.2 x (hAB x hx)⟩, hcost⟩

theorem realCoverLengths_mem {d : V} (hd : d ∈ (realBasicCodes V) ^ (ω : V))
    {n : V} (hn : n ∈ (ω : V)) : (realCoverLengths d) ‘ n ∈ internalRationals V := by
  rw [realCoverLengths, value_definableGraph _ _ _ hn]
  exact realIntervalLength_mem (function_value_mem hd hn)

theorem realCoverLengths_nonnegative {d : V} (hd : d ∈ (realBasicCodes V) ^ (ω : V))
    {n : V} (hn : n ∈ (ω : V)) : ¬ InternalRationalLT ((realCoverLengths d) ‘ n) (rationalZero V) := by
  rw [realCoverLengths, value_definableGraph _ _ _ hn]
  intro h
  exact internalRationalLT_irrefl rationalZero_mem (internalRationalLT_trans rationalZero_mem
    (realIntervalLength_mem (function_value_mem hd hn)) rationalZero_mem
    (realIntervalLength_pos (function_value_mem hd hn)) h)

theorem realCoverCost_nonnegative {d : V} (hd : d ∈ (realBasicCodes V) ^ (ω : V))
    {n : V} (hn : n ∈ (ω : V)) : ¬ InternalRationalLT (realCoverCost d n) (rationalZero V) :=
  rationalPartialSum_nonnegative (fun _ hk ↦ realCoverLengths_mem hd hk)
    (fun _ hk ↦ realCoverLengths_nonnegative hd hk) n hn

theorem realCoverCost_monotone {d n m : V} (hd : d ∈ (realBasicCodes V) ^ (ω : V))
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hnm : n ⊆ m) :
    ¬ InternalRationalLT (realCoverCost d m) (realCoverCost d n) :=
  rationalPartialSum_monotone (fun _ hk ↦ realCoverLengths_mem hd hk)
    (fun _ hk ↦ realCoverLengths_nonnegative hd hk) hn hm hnm

end ZFVP
