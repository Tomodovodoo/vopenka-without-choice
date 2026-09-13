import ZFVP.SetTheory.RealMeasureBracketFamily
import Mathlib.Tactic.Linarith

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Countable subadditivity for the actual internal extended-real series.
The full rational cut represents infinity, so this statement includes infinite sums. -/
theorem realOuterMeasure_countable_subadditive (hCC : InternalCountableChoice V) (A : V) :
    realOuterMeasure (realSequenceUnion A) ⊆ extendedSeries (realMeasureSequence A) := by
  intro q hq
  have hS := extendedSeries_extended (realMeasureSequence_extended A)
  by_contra hqout
  obtain ⟨r, hr, hqr⟩ := (realOuterMeasure_extended (realSequenceUnion A)).2.2.2 q hq
  have hqQ := (realOuterMeasure_extended (realSequenceUnion A)).1 q hq
  have hrQ := (realOuterMeasure_extended (realSequenceUnion A)).1 r hr
  let x : InternalRational V := ⟨q, hqQ⟩
  let y : InternalRational V := ⟨r, hrQ⟩
  have hxy : x < y := hqr
  have hSf : IsDedekindCut (extendedSeries (realMeasureSequence A)) := by
    rcases extendedNonnegativeReal_finite_or_infinite hS with h | h
    · exact h
    · exact (hqout (h.symm ▸ hqQ)).elim
  obtain ⟨m, hm, hsmall⟩ := dyadicUnit_small ((y - x) / 2).property
    (show (0 : InternalRational V) < (y - x) / 2 from div_pos (sub_pos.mpr hxy) (by norm_num))
  let t : InternalRational V := ⟨dyadicUnit m, dyadicUnit_mem hm⟩
  let e := realCoverLengths (realNullPadding m)
  have hem : ∀ i ∈ (ω : V), e ‘ i ∈ internalRationals V :=
    fun i hi ↦ realCoverLengths_mem (realNullPadding_mem hm) hi
  have hep : ∀ i ∈ (ω : V), InternalRationalLT (rationalZero V) (e ‘ i) := by
    intro i hi
    change InternalRationalLT (rationalZero V) ((realCoverLengths (realNullPadding m)) ‘ i)
    rw [realCoverLengths, value_definableGraph _ _ _ hi]
    exact realIntervalLength_pos (function_value_mem (realNullPadding_mem hm) hi)
  obtain ⟨a, ha, hbr⟩ := realMeasure_bracket_family hCC
    (realMeasureSequence_finite_of_series_finite hSf) hem hep
  have ham : ∀ i ∈ (ω : V), a ‘ i ∈ internalRationals V := fun i hi ↦ function_value_mem ha hi
  let b := definableGraph (ω : V)
    (fun i ↦ rationalAdd (rationalAdd (a ‘ i) (e ‘ i)) (e ‘ i)) (by definability)
  have hb : b ∈ (internalRationals V) ^ (ω : V) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦
      rationalAdd_mem (rationalAdd_mem (ham i hi) (hem i hi)) (hem i hi))
  have hbv : ∀ i ∈ (ω : V), b ‘ i = rationalAdd (rationalAdd (a ‘ i) (e ‘ i)) (e ‘ i) :=
    fun i hi ↦ value_definableGraph _ _ _ hi
  have hsum : ∀ n ∈ (ω : V), rationalPartialSum b n =
      rationalAdd (rationalAdd (rationalPartialSum a n) (rationalPartialSum e n)) (rationalPartialSum e n) := by
    apply naturalNumber_induction (fun n ↦ rationalPartialSum b n =
      rationalAdd (rationalAdd (rationalPartialSum a n) (rationalPartialSum e n)) (rationalPartialSum e n)) (by definability)
    · simp only [rationalPartialSum_zero, rationalAdd_zero rationalZero_mem]
    · intro n hn ih
      rw [rationalPartialSum_succ _ hn, rationalPartialSum_succ _ hn,
        rationalPartialSum_succ _ hn, ih, hbv n hn]
      let aa : InternalRational V := ⟨_, rationalPartialSum_mem ham n hn⟩
      let ee : InternalRational V := ⟨_, rationalPartialSum_mem hem n hn⟩
      let an : InternalRational V := ⟨_, ham n hn⟩
      let en : InternalRational V := ⟨_, hem n hn⟩
      exact congrArg Subtype.val (show (aa + ee + ee) + (an + en + en) =
        (aa + an) + (ee + en) + (ee + en) from by ring)
  have habound : ∀ n ∈ (ω : V), ¬InternalRationalLT q (rationalPartialSum a n) := by
    intro n hn hlt
    apply hqout
    apply extendedPartialSum_subset_series (realMeasureSequence_extended A) hn q
    apply rationalPartialSum_cut_subset_extended ham (realMeasureSequence_extended A)
      (fun i hi ↦ by rw [realMeasureSequence_value _ hi]; exact (hbr i hi).1) n hn q
    exact (mem_rationalCut_iff _ _).mpr ⟨hqQ, hlt⟩
  have hbudget : ∀ n ∈ (ω : V), ¬InternalRationalLT (x + t + t).val (rationalPartialSum b n) := by
    intro n hn
    rw [hsum n hn]
    exact add_le_add (add_le_add
      (show (⟨_, rationalPartialSum_mem ham n hn⟩ : InternalRational V) ≤ x from habound n hn)
      (show (⟨_, rationalPartialSum_mem hem n hn⟩ : InternalRational V) ≤ t from realNullPadding_cost_bound hm hn))
      (show (⟨_, rationalPartialSum_mem hem n hn⟩ : InternalRational V) ≤ t from realNullPadding_cost_bound hm hn)
  obtain ⟨d, hd, hdb⟩ := realSequenceUnion_cover_budget hCC hb (x + t + t).property (by
    intro i hi
    let ai : InternalRational V := ⟨_, ham i hi⟩
    let ei : InternalRational V := ⟨_, hem i hi⟩
    obtain ⟨d, hd, hdc⟩ := realOuterMeasure_cover_approximation (ai + ei) (ai + ei + ei)
      (hbr i hi).2 (lt_add_of_pos_right _ (show 0 < ei from hep i hi))
    refine ⟨d, hd, fun n hn ↦ ?_⟩
    rw [hbv i hi]
    exact hdc n hn) hbudget
  have hnonneg : ¬InternalRationalLT (x + t + t).val (rationalZero V) := by
    simpa only [realCoverCost_zero] using hdb 0 (by simp)
  have hbound := realOuterMeasure_le_of_cover_bound hd (x + t + t).property hnonneg hdb
  have hyr : y < x + t + t := ((mem_rationalCut_iff _ _).mp (hbound r hr)).2
  have hsmall' : t < (y - x) / 2 := hsmall
  linarith

end ZFVP
