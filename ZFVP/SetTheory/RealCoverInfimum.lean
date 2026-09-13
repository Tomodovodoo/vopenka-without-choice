import ZFVP.SetTheory.RealNullPadding

/-! Cover costs are suprema of internal partial sums; outer measure is their infimum. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def realCoverSumFormula : SetTheorySemisentence 2 :=
  f“u d. ∀ q, q ∈ u ↔ q ∈ !internalRationalsFormula ∧
    ∃ n ∈ !isω, !internalRationalLTFormula q (!realCoverCostFormula d n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realCoverSum (d : V) : V :=
  {q ∈ internalRationals V ; ∃ n ∈ (ω : V), InternalRationalLT q (realCoverCost d n)}

theorem mem_realCoverSum_iff (d q : V) : q ∈ realCoverSum d ↔
    q ∈ internalRationals V ∧ ∃ n ∈ (ω : V), InternalRationalLT q (realCoverCost d n) := by
  simp [realCoverSum]

instance realCoverSumFormula_defined : ℒₛₑₜ-function₁[V] realCoverSum via realCoverSumFormula :=
  ⟨fun v ↦ by simp [realCoverSumFormula, mem_ext_iff (y := realCoverSum _), mem_realCoverSum_iff]⟩

instance realCoverSum_definable : ℒₛₑₜ-function₁[V] realCoverSum := realCoverSumFormula_defined.to_definable

theorem realCoverSum_extended {d : V} (hd : d ∈ (realBasicCodes V) ^ (ω : V)) :
    IsExtendedNonnegativeReal (realCoverSum d) := by
  refine ⟨fun q hq ↦ ((mem_realCoverSum_iff _ _).mp hq).1, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨hqQ, hq0⟩ := (mem_rationalCut_iff _ _).mp hq
    exact (mem_realCoverSum_iff _ _).mpr ⟨hqQ, 0, by simp, by simpa only [realCoverCost_zero] using hq0⟩
  · intro q hq p hp hpq
    obtain ⟨hqQ, n, hn, hqn⟩ := (mem_realCoverSum_iff _ _).mp hq
    exact (mem_realCoverSum_iff _ _).mpr ⟨hp, n, hn,
      internalRationalLT_trans hp hqQ (realCoverCost_mem hd n hn) hpq hqn⟩
  · intro q hq
    obtain ⟨hqQ, n, hn, hqn⟩ := (mem_realCoverSum_iff _ _).mp hq
    obtain ⟨r, hr, hqr, hrn⟩ := internalRational_dense hqQ (realCoverCost_mem hd n hn) hqn
    exact ⟨r, (mem_realCoverSum_iff _ _).mpr ⟨hr, n, hn, hrn⟩, hqr⟩

theorem realCoverSum_supremum (d u : V) :
    realCoverSum d ⊆ u ↔ ∀ n ∈ (ω : V), rationalCut (realCoverCost d n) ⊆ u := by
  constructor
  · intro h n hn q hq
    obtain ⟨hqQ, hqn⟩ := (mem_rationalCut_iff _ _).mp hq
    exact h q ((mem_realCoverSum_iff _ _).mpr ⟨hqQ, n, hn, hqn⟩)
  · intro h q hq
    obtain ⟨hqQ, n, hn, hqn⟩ := (mem_realCoverSum_iff _ _).mp hq
    exact h n hn q ((mem_rationalCut_iff _ _).mpr ⟨hqQ, hqn⟩)

theorem realOuterMeasure_le_coverSum {d A : V} (hd : IsRealIntervalCover d A) :
    realOuterMeasure A ⊆ realCoverSum d := by
  intro q hq
  obtain ⟨hqQ, hq0 | ⟨r, hr, hqr, hbound⟩⟩ := (mem_realOuterMeasure_iff _ _).mp hq
  · exact (mem_realCoverSum_iff _ _).mpr ⟨hqQ, 0, by simp, by simpa only [realCoverCost_zero] using hq0⟩
  · obtain ⟨n, hn, hrn⟩ := hbound d hd
    exact (mem_realCoverSum_iff _ _).mpr ⟨hqQ, n, hn,
      internalRationalLT_trans hqQ hr (realCoverCost_mem hd.1 n hn) hqr hrn⟩

theorem realOuterMeasure_greatest_lower_bound {u A : V} (hu : IsExtendedNonnegativeReal u)
    (hbound : ∀ d, IsRealIntervalCover d A → u ⊆ realCoverSum d) : u ⊆ realOuterMeasure A := by
  intro q hq
  obtain ⟨r, hr, hqr⟩ := hu.2.2.2 q hq
  refine (mem_realOuterMeasure_iff _ _).mpr ⟨hu.1 q hq, Or.inr ⟨r, hu.1 r hr, hqr, ?_⟩⟩
  intro d hd
  exact ((mem_realCoverSum_iff _ _).mp (hbound d hd r hr)).2

theorem realOuterMeasure_infimum (A : V) :
    IsExtendedNonnegativeReal (realOuterMeasure A) ∧
    (∀ d, IsRealIntervalCover d A → realOuterMeasure A ⊆ realCoverSum d) ∧
    ∀ u, IsExtendedNonnegativeReal u → (∀ d, IsRealIntervalCover d A → u ⊆ realCoverSum d) →
      u ⊆ realOuterMeasure A :=
  ⟨realOuterMeasure_extended A, fun _ hd ↦ realOuterMeasure_le_coverSum hd,
    fun _ hu hb ↦ realOuterMeasure_greatest_lower_bound hu hb⟩

end ZFVP
