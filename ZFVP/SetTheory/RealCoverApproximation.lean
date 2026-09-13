import ZFVP.SetTheory.RealCoverExistence
import ZFVP.SetTheory.ExtendedRealAddition

/-! Rational approximation of the actual interval-cover infimum. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realOuterMeasure_cover_approximation {A : V} (a b : InternalRational V)
    (ha : a.val ∉ realOuterMeasure A) (hab : a < b) :
    ∃ d, IsRealIntervalCover d A ∧
      ∀ n ∈ (ω : V), ¬ InternalRationalLT b.val (realCoverCost d n) := by
  by_contra h
  apply ha
  refine (mem_realOuterMeasure_iff _ _).mpr ⟨a.property, Or.inr ⟨b.val, b.property, hab, ?_⟩⟩
  intro d hd
  by_contra hn
  exact h ⟨d, hd, fun n hnω hcost ↦ hn ⟨n, hnω, hcost⟩⟩

theorem realOuterMeasure_cover_approximation_of_bound {A : V} (a b : InternalRational V)
    (ha : realOuterMeasure A ⊆ rationalCut a.val) (hab : a < b) :
    ∃ d, IsRealIntervalCover d A ∧
      ∀ n ∈ (ω : V), ¬ InternalRationalLT b.val (realCoverCost d n) := by
  apply realOuterMeasure_cover_approximation a b ?_ hab
  intro h
  exact lt_irrefl a (show a < a from ((mem_rationalCut_iff _ _).mp (ha _ h)).2)

theorem realOuterMeasure_finite_iff_bounded_cover {A : V} :
    realOuterMeasure A ≠ internalRationals V ↔
      ∃ d b, IsRealIntervalCover d A ∧ b ∈ internalRationals V ∧
        ¬ InternalRationalLT b (rationalZero V) ∧
        ∀ n ∈ (ω : V), ¬ InternalRationalLT b (realCoverCost d n) := by
  constructor
  · intro h
    have hex : ∃ a ∈ internalRationals V, a ∉ realOuterMeasure A := by
      by_contra hn
      apply h
      apply subset_antisymm (realOuterMeasure_extended A).1
      intro a ha
      by_contra hnot
      exact hn ⟨a, ha, hnot⟩
    obtain ⟨a, ha, hnot⟩ := hex
    let q : InternalRational V := ⟨a, ha⟩
    obtain ⟨d, hd, hb⟩ := realOuterMeasure_cover_approximation q (q + 1) hnot (by simp)
    refine ⟨d, (q + 1).val, hd, (q + 1).property, ?_, hb⟩
    simpa only [realCoverCost_zero] using hb 0 (by simp)
  · rintro ⟨d, b, hd, hb, hb0, hcost⟩ heq
    have hle := realOuterMeasure_le_of_cover_bound hd hb hb0 hcost
    rw [heq] at hle
    exact internalRationalLT_irrefl hb ((mem_rationalCut_iff _ _).mp (hle b hb)).2

end ZFVP
