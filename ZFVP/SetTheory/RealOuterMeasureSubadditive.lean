import ZFVP.SetTheory.RealRationalBrackets
import Mathlib.Tactic.Linarith

/-! Finite subadditivity of the actual interval-cover outer measure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realOuterMeasure_union_le_finite {A B : V}
    (hA : IsDedekindCut (realOuterMeasure A)) (hB : IsDedekindCut (realOuterMeasure B)) :
    realOuterMeasure (A ∪ B) ⊆ extendedRealAdd (realOuterMeasure A) (realOuterMeasure B) := by
  intro q hq
  have hU := realOuterMeasure_extended (A ∪ B)
  have hsum := extendedRealAdd_extended (realOuterMeasure_extended A) (realOuterMeasure_extended B)
  obtain ⟨r, hr, hqr⟩ := hU.2.2.2 q hq
  let c : InternalRational V := ⟨q, hU.1 q hq⟩
  let t : InternalRational V := ⟨r, hU.1 r hr⟩
  let e := (t - c) / 8
  have he : 0 < e := div_pos (sub_pos.mpr (show c < t from hqr)) (by norm_num)
  obtain ⟨a, ha, haout⟩ := real_rational_bracket hA e he
  obtain ⟨b, hb, hbout⟩ := real_rational_bracket hB e he
  let s : InternalRational V := ⟨a, hA.1 a ha⟩
  let v : InternalRational V := ⟨b, hB.1 b hb⟩
  obtain ⟨d, hd, hdc⟩ := realOuterMeasure_cover_approximation (s + e) (s + e + e) haout
    (lt_add_of_pos_right _ he)
  obtain ⟨f, hf, hfc⟩ := realOuterMeasure_cover_approximation (v + e) (v + e + e) hbout
    (lt_add_of_pos_right _ he)
  have hcost := sequenceInterleave_coverCost_bound hd.1 hf.1 (s + e + e) (v + e + e) hdc hfc
  have hbudget0 : ¬ InternalRationalLT ((s + e + e) + (v + e + e)).val (rationalZero V) := by
    simpa only [realCoverCost_zero] using hcost 0 (by simp)
  have hbound := realOuterMeasure_le_of_cover_bound (sequenceInterleave_intervalCover hd hf)
    ((s + e + e) + (v + e + e)).property hbudget0 hcost
  have hrbudget : t < (s + e + e) + (v + e + e) := ((mem_rationalCut_iff _ _).mp (hbound r hr)).2
  by_contra hnot
  have habc : s + v ≤ c := by
    by_contra h
    have hlt : c < s + v := lt_of_not_ge h
    apply hnot
    apply hsum.2.2.1 (s + v).val
      ((mem_extendedRealAdd_iff _ _ _).mpr ⟨(s + v).property, a, ha, b, hb, rfl⟩) q c.property hlt
  have hgap : 8 * e = t - c := by dsimp [e]; ring
  have hcontra : ¬ t < (s + e + e) + (v + e + e) := by
    linarith
  exact hcontra hrbudget

theorem realOuterMeasure_union_le (A B : V) :
    realOuterMeasure (A ∪ B) ⊆ extendedRealAdd (realOuterMeasure A) (realOuterMeasure B) := by
  rcases extendedNonnegativeReal_finite_or_infinite (realOuterMeasure_extended A) with hA | hA
  · rcases extendedNonnegativeReal_finite_or_infinite (realOuterMeasure_extended B) with hB | hB
    · exact realOuterMeasure_union_le_finite hA hB
    · rw [hB, extendedRealAdd_infinity (realOuterMeasure_extended A)]
      exact (realOuterMeasure_extended (A ∪ B)).1
  · rw [extendedRealAdd_comm (realOuterMeasure_extended A).1 (realOuterMeasure_extended B).1,
      hA, extendedRealAdd_infinity (realOuterMeasure_extended B)]
    exact (realOuterMeasure_extended (A ∪ B)).1

end ZFVP
