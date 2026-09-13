import ZFVP.SetTheory.RealFiniteMeasurableUnions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realSequenceUnion_measurable_disjoint (hCC : InternalCountableChoice V) {A : V}
    (hA : ∀ i ∈ (ω : V), IsRealLebesgueMeasurable (A ‘ i))
    (hd : RealSequenceDisjoint A) : IsRealLebesgueMeasurable (realSequenceUnion A) := by
  apply realLebesgueMeasurable_of_split_ge
    (fun x hx ↦ (mem_dedekindReals_iff _).mpr ((mem_realSequenceUnion_iff _ _).mp hx).1)
  intro T hT
  have hsum := realOuterMeasure_countable_subadditive hCC (realSequenceInter A T)
  rw [realSequenceInter_union] at hsum
  apply subset_trans (extendedRealAdd_mono hsum (fun _ h ↦ h))
  apply extendedSeries_add_le
  intro n hn
  have hrem : T \ realSequenceUnion A ⊆ T \ realFiniteUnion A n := by
    intro x hx
    obtain ⟨hxT, hxA⟩ := mem_sdiff_iff.mp hx
    exact mem_sdiff_iff.mpr ⟨hxT, fun hxF ↦ hxA (realFiniteUnion_subset_sequence hn x hxF)⟩
  have h := extendedRealAdd_mono (u := extendedPartialSum (realMeasureSequence (realSequenceInter A T)) n)
    (s := extendedPartialSum (realMeasureSequence (realSequenceInter A T)) n)
    (fun _ h ↦ h) (realOuterMeasure_mono hrem)
  rw [realFiniteUnion_split hA hd hT n hn] at h
  exact h

noncomputable def realDisjointize (A : V) : V :=
  definableGraph (ω : V) (fun n ↦ A ‘ n \ realFiniteUnion A n) (by definability)

instance realDisjointize_definable : ℒₛₑₜ-function₁[V] realDisjointize := by
  have h : ℒₛₑₜ-relation[V] (fun D A ↦ ∀ p, p ∈ D ↔ ∃ n ∈ (ω : V),
    p = ⟨n, A ‘ n \ realFiniteUnion A n⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [realDisjointize, mem_definableGraph_iff]

theorem realDisjointize_value (A : V) {n : V} (hn : n ∈ (ω : V)) :
    (realDisjointize A) ‘ n = A ‘ n \ realFiniteUnion A n := value_definableGraph _ _ _ hn

theorem realDisjointize_disjoint {A : V}
    (hA : ∀ n ∈ (ω : V), A ‘ n ⊆ dedekindReals V) : RealSequenceDisjoint (realDisjointize A) := by
  intro i hi j hj hne x hxi hxj
  rw [realDisjointize_value _ hi] at hxi
  rw [realDisjointize_value _ hj] at hxj
  obtain ⟨hxi, hxiF⟩ := mem_sdiff_iff.mp hxi
  obtain ⟨hxj, hxjF⟩ := mem_sdiff_iff.mp hxj
  rcases lt_trichotomy (⟨i, hi⟩ : InternalNatural V) ⟨j, hj⟩ with hij | hij | hji
  · exact hxjF ((mem_realFiniteUnion_iff _ _ _).mpr ⟨hA i hi x hxi, i, hij, hxi⟩)
  · exact hne (congrArg Subtype.val hij)
  · exact hxiF ((mem_realFiniteUnion_iff _ _ _).mpr ⟨hA j hj x hxj, j, hji, hxj⟩)

theorem realDisjointize_finiteUnion {A : V}
    (hA : ∀ n ∈ (ω : V), A ‘ n ⊆ dedekindReals V) :
    ∀ n ∈ (ω : V), realFiniteUnion (realDisjointize A) n = realFiniteUnion A n := by
  apply naturalNumber_induction (fun n ↦ realFiniteUnion (realDisjointize A) n = realFiniteUnion A n) (by definability)
  · simp only [realFiniteUnion_zero]
  · intro n hn ih
    have hD : (realDisjointize A) ‘ n ⊆ dedekindReals V := by
      rw [realDisjointize_value _ hn]
      exact fun x hx ↦ hA n hn x (mem_sdiff_iff.mp hx).1
    rw [realFiniteUnion_succ hD, realFiniteUnion_succ (hA n hn), ih, realDisjointize_value _ hn]
    apply mem_ext
    intro x
    simp only [mem_union_iff, mem_sdiff_iff]
    tauto

theorem realDisjointize_union {A : V}
    (hA : ∀ n ∈ (ω : V), A ‘ n ⊆ dedekindReals V) :
    realSequenceUnion (realDisjointize A) = realSequenceUnion A := by
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨hxR, i, hi, hxi⟩ := (mem_realSequenceUnion_iff _ _).mp hx
    rw [realDisjointize_value _ hi] at hxi
    exact (mem_realSequenceUnion_iff _ _).mpr ⟨hxR, i, hi, (mem_sdiff_iff.mp hxi).1⟩
  · intro hx
    obtain ⟨hxR, i, hi, hxi⟩ := (mem_realSequenceUnion_iff _ _).mp hx
    have hxF : x ∈ realFiniteUnion A (succ i) := (mem_realFiniteUnion_iff _ _ _).mpr
      ⟨(mem_dedekindReals_iff _).mpr hxR, i, mem_succ_iff.mpr (Or.inl rfl), hxi⟩
    rw [← realDisjointize_finiteUnion hA (succ i) (ω_succ_closed hi)] at hxF
    exact realFiniteUnion_subset_sequence (ω_succ_closed hi) x hxF

/-- The Carathéodory measurable sets are closed under internally countable unions. -/
theorem realSequenceUnion_measurable (hCC : InternalCountableChoice V) {A : V}
    (hA : ∀ n ∈ (ω : V), IsRealLebesgueMeasurable (A ‘ n)) :
    IsRealLebesgueMeasurable (realSequenceUnion A) := by
  have h := realSequenceUnion_measurable_disjoint hCC (A := realDisjointize A) (by
    intro n hn
    rw [realDisjointize_value _ hn]
    exact realLebesgueMeasurable_sdiff (hA n hn) (realFiniteUnion_measurable hA n hn))
    (realDisjointize_disjoint (fun n hn ↦ (hA n hn).1))
  rwa [realDisjointize_union (fun n hn ↦ (hA n hn).1)] at h

/-- Countable additivity for pairwise disjoint measurable sets, including infinite measure. -/
theorem realOuterMeasure_countable_additive (hCC : InternalCountableChoice V) {A : V}
    (hA : ∀ i ∈ (ω : V), IsRealLebesgueMeasurable (A ‘ i))
    (hd : RealSequenceDisjoint A) :
    realOuterMeasure (realSequenceUnion A) = extendedSeries (realMeasureSequence A) := by
  apply subset_antisymm (realOuterMeasure_countable_subadditive hCC A)
  have hE : realSequenceUnion A ⊆ dedekindReals V :=
    fun x hx ↦ (mem_dedekindReals_iff _).mpr ((mem_realSequenceUnion_iff _ _).mp hx).1
  have hinter : ∀ i ∈ (ω : V), realSequenceUnion A ∩ A ‘ i = A ‘ i := by
    intro i hi
    apply mem_ext
    intro x
    rw [mem_inter_iff]
    constructor
    · exact And.right
    · intro hx
      exact ⟨(mem_realSequenceUnion_iff _ _).mpr
        ⟨(mem_dedekindReals_iff _).mp ((hA i hi).1 x hx), i, hi, hx⟩, hx⟩
  have hsum : ∀ n ∈ (ω : V),
      extendedPartialSum (realMeasureSequence (realSequenceInter A (realSequenceUnion A))) n =
      extendedPartialSum (realMeasureSequence A) n := by
    apply naturalNumber_induction (fun n ↦
      extendedPartialSum (realMeasureSequence (realSequenceInter A (realSequenceUnion A))) n =
      extendedPartialSum (realMeasureSequence A) n) (by definability)
    · simp only [extendedPartialSum_zero]
    · intro n hn ih
      rw [extendedPartialSum_succ _ hn, extendedPartialSum_succ _ hn, ih,
        realMeasureSequence_value _ hn, realSequenceInter_value _ _ hn, hinter n hn,
        realMeasureSequence_value _ hn]
  intro q hq
  obtain ⟨_, n, hn, hqn⟩ := (mem_extendedSeries_iff _ _).mp hq
  have hh := realFiniteUnion_split hA hd hE n hn
  rw [hsum n hn] at hh
  have hle := extendedRealAdd_le_left
    (extendedPartialSum_extended (realMeasureSequence_extended A) n hn)
    (realOuterMeasure_extended (realSequenceUnion A \ realFiniteUnion A n))
  rw [hh] at hle
  exact hle q hqn

end ZFVP
