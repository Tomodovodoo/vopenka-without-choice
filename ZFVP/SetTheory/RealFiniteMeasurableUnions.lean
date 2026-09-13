import ZFVP.SetTheory.RealCountableSubadditivity
import ZFVP.SetTheory.RealMeasurableAlgebra

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realFiniteUnion (A n : V) : V :=
  {x ∈ dedekindReals V ; ∃ i ∈ n, x ∈ A ‘ i}

theorem mem_realFiniteUnion_iff (A n x : V) : x ∈ realFiniteUnion A n ↔
    x ∈ dedekindReals V ∧ ∃ i ∈ n, x ∈ A ‘ i := by simp [realFiniteUnion]

instance realFiniteUnion_definable : ℒₛₑₜ-function₂[V] realFiniteUnion := by
  have h : ℒₛₑₜ-relation₃[V] (fun F A n ↦ ∀ x, x ∈ F ↔ x ∈ dedekindReals V ∧
    ∃ i ∈ n, x ∈ A ‘ i) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_realFiniteUnion_iff]

@[simp] theorem realFiniteUnion_zero (A : V) : realFiniteUnion A 0 = ∅ := by
  apply mem_ext
  intro x
  simp [mem_realFiniteUnion_iff, zero_def]

theorem realFiniteUnion_succ {A n : V} (hA : A ‘ n ⊆ dedekindReals V) :
    realFiniteUnion A (succ n) = realFiniteUnion A n ∪ A ‘ n := by
  apply mem_ext
  intro x
  simp only [mem_realFiniteUnion_iff, mem_union_iff, mem_succ_iff]
  constructor
  · rintro ⟨hxR, i, hi, hxi⟩
    rcases hi with hi | hi
    · subst i; exact Or.inr hxi
    · exact Or.inl ⟨hxR, i, hi, hxi⟩
  · rintro (⟨hxR, i, hi, hxi⟩ | hx)
    · exact ⟨hxR, i, Or.inr hi, hxi⟩
    · exact ⟨hA x hx, n, Or.inl rfl, hx⟩

theorem realFiniteUnion_subset_sequence {A n : V} (hn : n ∈ (ω : V)) :
    realFiniteUnion A n ⊆ realSequenceUnion A := by
  intro x hx
  obtain ⟨hxR, i, hi, hxi⟩ := (mem_realFiniteUnion_iff _ _ _).mp hx
  exact (mem_realSequenceUnion_iff _ _).mpr
    ⟨(mem_dedekindReals_iff _).mp hxR, i, IsTransitive.ω.transitive n hn i hi, hxi⟩

theorem realFiniteUnion_measurable {A : V}
    (hA : ∀ i ∈ (ω : V), IsRealLebesgueMeasurable (A ‘ i)) :
    ∀ n ∈ (ω : V), IsRealLebesgueMeasurable (realFiniteUnion A n) := by
  apply naturalNumber_induction (fun n ↦ IsRealLebesgueMeasurable (realFiniteUnion A n)) (by definability)
  · rw [realFiniteUnion_zero]
    exact realNull_lebesgueMeasurable realNull_empty
  · intro n hn ih
    rw [realFiniteUnion_succ (hA n hn).1]
    exact realLebesgueMeasurable_union ih (hA n hn)

noncomputable def realSequenceInter (A T : V) : V :=
  definableGraph (ω : V) (fun i ↦ T ∩ A ‘ i) (by definability)

instance realSequenceInter_definable : ℒₛₑₜ-function₂[V] realSequenceInter := by
  have h : ℒₛₑₜ-relation₃[V] (fun f A T ↦ ∀ p, p ∈ f ↔ ∃ i ∈ (ω : V), p = ⟨i, T ∩ A ‘ i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [realSequenceInter, mem_definableGraph_iff]

theorem realSequenceInter_value (A T : V) {i : V} (hi : i ∈ (ω : V)) :
    (realSequenceInter A T) ‘ i = T ∩ A ‘ i := value_definableGraph _ _ _ hi

theorem realSequenceInter_union (A T : V) :
    realSequenceUnion (realSequenceInter A T) = T ∩ realSequenceUnion A := by
  apply mem_ext
  intro x
  simp only [mem_realSequenceUnion_iff, mem_inter_iff]
  constructor
  · rintro ⟨hxR, i, hi, hxi⟩
    rw [realSequenceInter_value _ _ hi] at hxi
    obtain ⟨hxT, hxi⟩ := mem_inter_iff.mp hxi
    exact ⟨hxT, hxR, i, hi, hxi⟩
  · rintro ⟨hxT, hxR, i, hi, hxi⟩
    refine ⟨hxR, i, hi, ?_⟩
    rw [realSequenceInter_value _ _ hi]
    exact mem_inter_iff.mpr ⟨hxT, hxi⟩

def RealSequenceDisjoint (A : V) : Prop :=
  ∀ i ∈ (ω : V), ∀ j ∈ (ω : V), i ≠ j → ∀ x, x ∈ A ‘ i → x ∉ A ‘ j

instance realSequenceDisjoint_definable : ℒₛₑₜ-predicate[V] RealSequenceDisjoint := by
  unfold RealSequenceDisjoint
  definability

/-- Finite disjoint splitting uses induction over the model's entire omega. -/
theorem realFiniteUnion_split {A T : V}
    (hA : ∀ i ∈ (ω : V), IsRealLebesgueMeasurable (A ‘ i))
    (hd : RealSequenceDisjoint A) (hT : T ⊆ dedekindReals V) :
    ∀ n ∈ (ω : V), extendedRealAdd
      (extendedPartialSum (realMeasureSequence (realSequenceInter A T)) n)
      (realOuterMeasure (T \ realFiniteUnion A n)) = realOuterMeasure T := by
  apply naturalNumber_induction (fun n ↦ extendedRealAdd
      (extendedPartialSum (realMeasureSequence (realSequenceInter A T)) n)
      (realOuterMeasure (T \ realFiniteUnion A n)) = realOuterMeasure T) (by definability)
  · rw [extendedPartialSum_zero, realFiniteUnion_zero]
    have he : T \ (∅ : V) = T := by apply mem_ext; intro x; simp
    rw [he, extendedRealAdd_zero_left (realOuterMeasure_extended T)]
  · intro n hn ih
    have hrem : T \ realFiniteUnion A n ⊆ dedekindReals V :=
      fun x hx ↦ hT x (mem_sdiff_iff.mp hx).1
    have hleft : (T \ realFiniteUnion A n) ∩ A ‘ n = T ∩ A ‘ n := by
      apply mem_ext
      intro x
      simp only [mem_inter_iff, mem_sdiff_iff]
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · rintro ⟨hxT, hxn⟩
        refine ⟨⟨hxT, ?_⟩, hxn⟩
        intro hxF
        obtain ⟨_, i, hi, hxi⟩ := (mem_realFiniteUnion_iff _ _ _).mp hxF
        have hiw := IsTransitive.ω.transitive n hn i hi
        have hne : i ≠ n := by intro he; subst i; exact mem_irrefl n hi
        exact hd i hiw n hn hne x hxi hxn
    have hright : (T \ realFiniteUnion A n) \ A ‘ n = T \ realFiniteUnion A (succ n) := by
      rw [realFiniteUnion_succ (hA n hn).1]
      apply mem_ext
      intro x
      simp only [mem_sdiff_iff, mem_union_iff]
      tauto
    have hsplit := (hA n hn).2 (T \ realFiniteUnion A n) hrem
    rw [hleft, hright] at hsplit
    rw [extendedPartialSum_succ _ hn, realMeasureSequence_value _ hn, realSequenceInter_value _ _ hn,
      extendedRealAdd_assoc (extendedPartialSum_extended (realMeasureSequence_extended _) n hn).1
        (realOuterMeasure_extended _).1 (realOuterMeasure_extended _).1,
      ← hsplit]
    exact ih

end ZFVP
