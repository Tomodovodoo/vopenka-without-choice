import ZFVP.SetTheory.RealCountableNullUnions
import ZFVP.SetTheory.ExtendedRealSeries
import ZFVP.SetTheory.RealRationalBrackets

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realMeasureSequence (A : V) : V :=
  definableGraph (ω : V) (fun i ↦ realOuterMeasure (A ‘ i)) (by definability)

instance realMeasureSequence_definable : ℒₛₑₜ-function₁[V] realMeasureSequence := by
  have h : ℒₛₑₜ-relation[V] (fun f A ↦ ∀ p, p ∈ f ↔ ∃ i ∈ (ω : V),
    p = ⟨i, realOuterMeasure (A ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [realMeasureSequence, mem_definableGraph_iff]

theorem realMeasureSequence_value (A : V) {i : V} (hi : i ∈ (ω : V)) :
    (realMeasureSequence A) ‘ i = realOuterMeasure (A ‘ i) := value_definableGraph _ _ _ hi

theorem realMeasureSequence_extended (A : V) :
    ∀ i ∈ (ω : V), IsExtendedNonnegativeReal ((realMeasureSequence A) ‘ i) := by
  intro i hi
  rw [realMeasureSequence_value _ hi]
  exact realOuterMeasure_extended _

theorem realMeasureSequence_finite_of_series_finite {A : V}
    (hS : IsDedekindCut (extendedSeries (realMeasureSequence A))) :
    ∀ i ∈ (ω : V), IsDedekindCut (realOuterMeasure (A ‘ i)) := by
  intro i hi
  rcases extendedNonnegativeReal_finite_or_infinite (realOuterMeasure_extended (A ‘ i)) with h | h
  · exact h
  · obtain ⟨q, hq, hqout⟩ := hS.2.2.1
    have hh := extendedSeries_term_subset (realMeasureSequence_extended A) hi
    rw [realMeasureSequence_value _ hi, h] at hh
    exact (hqout (hh q hq)).elim

/-- Rational brackets are selected from subsets of the single set of internal rationals. -/
theorem realMeasure_bracket_family (hCC : InternalCountableChoice V) {A e : V}
    (hA : ∀ i ∈ (ω : V), IsDedekindCut (realOuterMeasure (A ‘ i)))
    (he : ∀ i ∈ (ω : V), e ‘ i ∈ internalRationals V)
    (hep : ∀ i ∈ (ω : V), InternalRationalLT (rationalZero V) (e ‘ i)) :
    ∃ a ∈ (internalRationals V) ^ (ω : V), ∀ i ∈ (ω : V),
      a ‘ i ∈ realOuterMeasure (A ‘ i) ∧ rationalAdd (a ‘ i) (e ‘ i) ∉ realOuterMeasure (A ‘ i) := by
  let W : V → V := fun i ↦ {q ∈ internalRationals V ; q ∈ realOuterMeasure (A ‘ i) ∧
    rationalAdd q (e ‘ i) ∉ realOuterMeasure (A ‘ i)}
  have hW : ℒₛₑₜ-function₁[V] W := by
    have h : ℒₛₑₜ-relation[V] (fun S i ↦ ∀ q, q ∈ S ↔ q ∈ internalRationals V ∧
      q ∈ realOuterMeasure (A ‘ i) ∧ rationalAdd q (e ‘ i) ∉ realOuterMeasure (A ‘ i)) := by definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp [W]
  let C := definableGraph (ω : V) W hW
  have hn : ∀ i ∈ (ω : V), IsNonempty (C ‘ i) := by
    intro i hi
    obtain ⟨q, hq, hout⟩ := real_rational_bracket (hA i hi) ⟨_, he i hi⟩ (hep i hi)
    refine ⟨q, ?_⟩
    rw [value_definableGraph _ _ _ hi]
    exact mem_sep_iff.mpr ⟨(hA i hi).1 q hq, hq, hout⟩
  obtain ⟨g, _, hg⟩ := hCC C (definableGraph_isFunction _ _ _) (domain_definableGraph _ _ _) hn
  have hv : ∀ i ∈ (ω : V), g ‘ i ∈ internalRationals V ∧
      g ‘ i ∈ realOuterMeasure (A ‘ i) ∧ rationalAdd (g ‘ i) (e ‘ i) ∉ realOuterMeasure (A ‘ i) := by
    intro i hi
    have h := hg i hi
    rw [value_definableGraph _ _ _ hi] at h
    exact mem_sep_iff.mp h
  let a := definableGraph (ω : V) (fun i ↦ g ‘ i) (by definability)
  refine ⟨a, definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ (hv i hi).1), ?_⟩
  intro i hi
  rw [value_definableGraph _ _ _ hi]
  exact (hv i hi).2

end ZFVP
