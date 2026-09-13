import ZFVP.SetTheory.RealIntervalCovers

/-! The extended nonnegative outer measure defined by genuine rational interval covers.
The full rational cut represents infinity. The existential rational margin in the
infimum formula ensures that the lower cut has no greatest element. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def realOuterMeasureFormula : SetTheorySemisentence 2 :=
  f“u A. ∀ q, q ∈ u ↔ q ∈ !internalRationalsFormula ∧
    (!internalRationalLTFormula q (!rationalZeroFormula) ∨
      ∃ r ∈ !internalRationalsFormula, !internalRationalLTFormula q r ∧
        ∀ d, !isRealIntervalCoverFormula d A →
          ∃ n ∈ !isω, !internalRationalLTFormula r (!realCoverCostFormula d n))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsExtendedNonnegativeReal (u : V) : Prop :=
  u ⊆ internalRationals V ∧ rationalCut (rationalZero V) ⊆ u ∧
    (∀ q ∈ u, ∀ p ∈ internalRationals V, InternalRationalLT p q → p ∈ u) ∧
    ∀ q ∈ u, ∃ r ∈ u, InternalRationalLT q r

instance isExtendedNonnegativeReal_definable : ℒₛₑₜ-predicate[V] IsExtendedNonnegativeReal := by
  unfold IsExtendedNonnegativeReal
  definability

noncomputable def realOuterMeasure (A : V) : V :=
  {q ∈ internalRationals V ; InternalRationalLT q (rationalZero V) ∨
    ∃ r ∈ internalRationals V, InternalRationalLT q r ∧
      ∀ d, IsRealIntervalCover d A → ∃ n ∈ (ω : V), InternalRationalLT r (realCoverCost d n)}

theorem mem_realOuterMeasure_iff (A q : V) : q ∈ realOuterMeasure A ↔
    q ∈ internalRationals V ∧ (InternalRationalLT q (rationalZero V) ∨
      ∃ r ∈ internalRationals V, InternalRationalLT q r ∧
        ∀ d, IsRealIntervalCover d A → ∃ n ∈ (ω : V), InternalRationalLT r (realCoverCost d n)) := by
  simp [realOuterMeasure]

instance realOuterMeasureFormula_defined :
    ℒₛₑₜ-function₁[V] realOuterMeasure via realOuterMeasureFormula :=
  ⟨fun v ↦ by simp [realOuterMeasureFormula, mem_ext_iff (y := realOuterMeasure _),
    mem_realOuterMeasure_iff]⟩

instance realOuterMeasure_definable : ℒₛₑₜ-function₁[V] realOuterMeasure :=
  realOuterMeasureFormula_defined.to_definable

theorem realOuterMeasure_extended (A : V) : IsExtendedNonnegativeReal (realOuterMeasure A) := by
  refine ⟨fun q hq ↦ ((mem_realOuterMeasure_iff _ _).mp hq).1, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨hqQ, hq0⟩ := (mem_rationalCut_iff _ _).mp hq
    exact (mem_realOuterMeasure_iff _ _).mpr ⟨hqQ, Or.inl hq0⟩
  · intro q hq p hp hpq
    obtain ⟨hqQ, hq0 | ⟨r, hr, hqr, hbound⟩⟩ := (mem_realOuterMeasure_iff _ _).mp hq
    · exact (mem_realOuterMeasure_iff _ _).mpr
        ⟨hp, Or.inl (internalRationalLT_trans hp hqQ rationalZero_mem hpq hq0)⟩
    · exact (mem_realOuterMeasure_iff _ _).mpr
        ⟨hp, Or.inr ⟨r, hr, internalRationalLT_trans hp hqQ hr hpq hqr, hbound⟩⟩
  · intro q hq
    obtain ⟨hqQ, hq0 | ⟨r, hr, hqr, hbound⟩⟩ := (mem_realOuterMeasure_iff _ _).mp hq
    · obtain ⟨p, hp, hqp, hp0⟩ := internalRational_dense hqQ rationalZero_mem hq0
      exact ⟨p, (mem_realOuterMeasure_iff _ _).mpr ⟨hp, Or.inl hp0⟩, hqp⟩
    · obtain ⟨p, hp, hqp, hpr⟩ := internalRational_dense hqQ hr hqr
      exact ⟨p, (mem_realOuterMeasure_iff _ _).mpr ⟨hp, Or.inr ⟨r, hr, hpr, hbound⟩⟩, hqp⟩

theorem extendedNonnegativeReal_finite_or_infinite {u : V} (hu : IsExtendedNonnegativeReal u) :
    IsDedekindCut u ∨ u = internalRationals V := by
  by_cases h : u = internalRationals V
  · exact Or.inr h
  · apply Or.inl
    have hex : ∃ q ∈ internalRationals V, q ∉ u := by
      by_contra hn
      apply h
      apply subset_antisymm hu.1
      intro q hq
      by_contra hqu
      exact hn ⟨q, hq, hqu⟩
    obtain ⟨q, hq⟩ := (rationalCut_isCut (rationalZero_mem (V := V))).2.1
    exact ⟨hu.1, ⟨q, hu.2.1 q hq⟩, hex, hu.2.2.1, hu.2.2.2⟩

theorem realOuterMeasure_mono {A B : V} (hAB : A ⊆ B) : realOuterMeasure A ⊆ realOuterMeasure B := by
  intro q hq
  obtain ⟨hqQ, hq0 | ⟨r, hr, hqr, hbound⟩⟩ := (mem_realOuterMeasure_iff _ _).mp hq
  · exact (mem_realOuterMeasure_iff _ _).mpr ⟨hqQ, Or.inl hq0⟩
  · refine (mem_realOuterMeasure_iff _ _).mpr ⟨hqQ, Or.inr ⟨r, hr, hqr, ?_⟩⟩
    intro d hd
    exact hbound d ⟨hd.1, fun x hx ↦ hd.2 x (hAB x hx)⟩

theorem realOuterMeasure_le_of_cover_bound {A d b : V}
    (hd : IsRealIntervalCover d A) (hb : b ∈ internalRationals V)
    (hb0 : ¬ InternalRationalLT b (rationalZero V))
    (hcost : ∀ n ∈ (ω : V), ¬ InternalRationalLT b (realCoverCost d n)) :
    realOuterMeasure A ⊆ rationalCut b := by
  intro q hq
  obtain ⟨hqQ, hq0 | ⟨r, hr, hqr, hbound⟩⟩ := (mem_realOuterMeasure_iff _ _).mp hq
  · apply (mem_rationalCut_iff _ _).mpr
    exact ⟨hqQ, show (⟨q, hqQ⟩ : InternalRational V) < ⟨b, hb⟩ from
      lt_of_lt_of_le hq0 (show (0 : InternalRational V) ≤ ⟨b, hb⟩ from hb0)⟩
  · obtain ⟨n, hn, hrn⟩ := hbound d hd
    have hsn := realCoverCost_mem hd.1 n hn
    have hqb : (⟨q, hqQ⟩ : InternalRational V) < ⟨b, hb⟩ :=
      lt_of_lt_of_le (show (⟨q, hqQ⟩ : InternalRational V) < ⟨realCoverCost d n, hsn⟩ from
        internalRationalLT_trans hqQ hr hsn hqr hrn) (hcost n hn)
    exact (mem_rationalCut_iff _ _).mpr ⟨hqQ, hqb⟩

theorem realNull_outerMeasure_zero {A : V} (hA : IsRealNull A) :
    realOuterMeasure A = rationalCut (rationalZero V) := by
  apply subset_antisymm ?_ (realOuterMeasure_extended A).2.1
  intro q hq
  obtain ⟨hqQ, hq0 | ⟨r, hr, hqr, hbound⟩⟩ := (mem_realOuterMeasure_iff _ _).mp hq
  · exact (mem_rationalCut_iff _ _).mpr ⟨hqQ, hq0⟩
  · by_cases hq0 : InternalRationalLT q (rationalZero V)
    · exact (mem_rationalCut_iff _ _).mpr ⟨hqQ, hq0⟩
    have hr0 : InternalRationalLT (rationalZero V) r :=
      lt_of_le_of_lt (show (0 : InternalRational V) ≤ ⟨q, hqQ⟩ from hq0)
        (show (⟨q, hqQ⟩ : InternalRational V) < ⟨r, hr⟩ from hqr)
    obtain ⟨m, hm, hmr⟩ := dyadicUnit_small hr hr0
    obtain ⟨d, hd, hcost⟩ := hA m hm
    obtain ⟨n, hn, hrn⟩ := hbound d hd
    exact (hcost n hn (internalRationalLT_trans (dyadicUnit_mem hm) hr
      (realCoverCost_mem hd.1 n hn) hmr hrn)).elim

theorem realNull_of_outerMeasure_zero {A : V}
    (hA : realOuterMeasure A = rationalCut (rationalZero V)) : IsRealNull A := by
  intro m hm
  obtain ⟨k, hk, hkm⟩ := dyadicUnit_small (dyadicUnit_mem hm) (dyadicUnit_positive hm)
  have hknot : dyadicUnit k ∉ realOuterMeasure A := by
    rw [hA]
    intro h
    have hk0 := ((mem_rationalCut_iff _ _).mp h).2
    exact internalRationalLT_irrefl rationalZero_mem
      (internalRationalLT_trans rationalZero_mem (dyadicUnit_mem hk) rationalZero_mem
        (dyadicUnit_positive hk) hk0)
  by_contra hmissing
  apply hknot
  refine (mem_realOuterMeasure_iff _ _).mpr ⟨dyadicUnit_mem hk,
    Or.inr ⟨dyadicUnit m, dyadicUnit_mem hm, hkm, ?_⟩⟩
  intro d hd
  by_contra hn
  exact hmissing ⟨d, hd, fun n hnω hcost ↦ hn ⟨n, hnω, hcost⟩⟩

theorem realNull_iff_outerMeasure_zero (A : V) :
    IsRealNull A ↔ realOuterMeasure A = rationalCut (rationalZero V) :=
  ⟨realNull_outerMeasure_zero, realNull_of_outerMeasure_zero⟩

end ZFVP
