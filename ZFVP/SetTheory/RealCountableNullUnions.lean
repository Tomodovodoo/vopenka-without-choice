import ZFVP.SetTheory.RealCoverFlattenBudget
import ZFVP.SetTheory.RealCategoryUnions
import ZFVP.SetTheory.RealNullPadding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Countable choice is applied to subsets of the fixed set of genuine covers. -/
theorem realIntervalCover_choose_budget (hCC : InternalCountableChoice V) {A b : V}
    (hex : ∀ i ∈ (ω : V), ∃ d, IsRealIntervalCover d (A ‘ i) ∧
      ∀ n ∈ (ω : V), ¬InternalRationalLT (b ‘ i) (realCoverCost d n)) :
    ∃ cov ∈ ((realBasicCodes V) ^ (ω : V)) ^ (ω : V),
      ∀ i ∈ (ω : V), IsRealIntervalCover (cov ‘ i) (A ‘ i) ∧
        ∀ n ∈ (ω : V), ¬InternalRationalLT (b ‘ i) (realCoverCost (cov ‘ i) n) := by
  let W : V → V := fun i ↦ {d ∈ (realBasicCodes V) ^ (ω : V) ;
    IsRealIntervalCover d (A ‘ i) ∧ ∀ n ∈ (ω : V), ¬InternalRationalLT (b ‘ i) (realCoverCost d n)}
  have hW : ℒₛₑₜ-function₁[V] W := by
    have h : ℒₛₑₜ-relation[V] (fun X i ↦ ∀ d, d ∈ X ↔
      d ∈ (realBasicCodes V) ^ (ω : V) ∧ IsRealIntervalCover d (A ‘ i) ∧
      ∀ n ∈ (ω : V), ¬InternalRationalLT (b ‘ i) (realCoverCost d n)) := by definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp [W]
  let C := definableGraph (ω : V) W hW
  have hnC : ∀ i ∈ (ω : V), IsNonempty (C ‘ i) := by
    intro i hi
    obtain ⟨d, hd, hb⟩ := hex i hi
    refine ⟨d, ?_⟩
    rw [value_definableGraph _ _ _ hi]
    exact mem_sep_iff.mpr ⟨hd.1, hd, hb⟩
  obtain ⟨g, hg, hchoice⟩ := hCC C (definableGraph_isFunction _ _ _)
    (domain_definableGraph _ _ _) hnC
  have hchosen : ∀ i ∈ (ω : V), IsRealIntervalCover (g ‘ i) (A ‘ i) ∧
      ∀ n ∈ (ω : V), ¬InternalRationalLT (b ‘ i) (realCoverCost (g ‘ i) n) := by
    intro i hi
    have h := hchoice i hi
    rw [value_definableGraph _ _ _ hi] at h
    exact (mem_sep_iff.mp h).2
  let cov := definableGraph (ω : V) (fun i ↦ g ‘ i) (by definability)
  refine ⟨cov, definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun i hi ↦ (hchosen i hi).1.1), ?_⟩
  intro i hi
  rw [value_definableGraph _ _ _ hi]
  exact hchosen i hi

/-- Explicit rational row budgets give a genuine cover of the countable union. -/
theorem realSequenceUnion_cover_budget (hCC : InternalCountableChoice V) {A b B : V}
    (hb : b ∈ (internalRationals V) ^ (ω : V)) (hB : B ∈ internalRationals V)
    (hex : ∀ i ∈ (ω : V), ∃ d, IsRealIntervalCover d (A ‘ i) ∧
      ∀ n ∈ (ω : V), ¬InternalRationalLT (b ‘ i) (realCoverCost d n))
    (hbudget : ∀ n ∈ (ω : V), ¬InternalRationalLT B (rationalPartialSum b n)) :
    ∃ d, IsRealIntervalCover d (realSequenceUnion A) ∧
      ∀ n ∈ (ω : V), ¬InternalRationalLT B (realCoverCost d n) := by
  obtain ⟨cov, hcov, hc⟩ := realIntervalCover_choose_budget hCC hex
  obtain ⟨d, hd, hdb⟩ := realCoverFamily_flatten_budget hcov hb hB
    (fun i hi ↦ (hc i hi).2) hbudget
  refine ⟨d, ⟨hd.1, fun x hx ↦ hd.2 x ?_⟩, hdb⟩
  obtain ⟨hxr, i, hi, hxi⟩ := (mem_realSequenceUnion_iff _ _).mp hx
  obtain ⟨j, hj, hxj⟩ := (hc i hi).1.2 x hxi
  exact (mem_realCoverFamilyUnion_iff _ _).mpr
    ⟨(mem_dedekindReals_iff _).mpr hxr, i, hi, j, hj, hxj⟩

/-- Internally countable unions of genuine real null sets are null under countable choice. -/
theorem realSequenceUnion_null (hCC : InternalCountableChoice V) {A : V}
    (hA : ∀ i ∈ (ω : V), IsRealNull (A ‘ i)) : IsRealNull (realSequenceUnion A) := by
  intro m hm
  let b := realCoverLengths (realNullPadding m)
  have hb : b ∈ (internalRationals V) ^ (ω : V) := by
    apply definableGraph_mem_function_of_mapsTo
    intro i hi
    exact realIntervalLength_mem (function_value_mem (realNullPadding_mem hm) hi)
  apply realSequenceUnion_cover_budget hCC hb (dyadicUnit_mem hm)
  · intro i hi
    have hmi := ω_succ_closed (ordinalAdd_natural hm hi)
    obtain ⟨d, hd, hdb⟩ := hA i hi _ hmi
    refine ⟨d, hd, ?_⟩
    intro n hn
    change ¬InternalRationalLT ((realCoverLengths (realNullPadding m)) ‘ i) (realCoverCost d n)
    rw [realCoverLengths, value_definableGraph _ _ _ hi, realNullPadding_length hm hi]
    exact hdb n hn
  · intro n hn
    exact realNullPadding_cost_bound hm hn

end ZFVP

