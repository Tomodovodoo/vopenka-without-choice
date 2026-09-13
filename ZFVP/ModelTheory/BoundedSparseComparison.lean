import ZFVP.ModelTheory.SparseCarrierOrderRecursion
import ZFVP.SetTheory.BoundedForcingSubset
import ZFVP.SetTheory.BoundedRestriction
import ZFVP.SetTheory.BoundedValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSparseComparisonFormula : SetTheorySemisentence 8 :=
  “W T C O E b p q. ∃ B ∈ W, ∃ R ∈ W, ∃ H ∈ W,
    !boundedValueFormula B C b ∧ !boundedValueFormula R O b ∧ !boundedValueFormula H E b ∧
    ∃ r ∈ T, ∃ σ ∈ T, ∃ τ ∈ T,
      !boundedRestrictFormula r p b ∧ !boundedValueFormula σ q b ∧ !boundedValueFormula τ p b ∧
      r ∈ B ∧ !boundedEqualityLeftFormula T B R H σ τ r”

theorem boundedSparseComparisonFormula_bounded : IsBoundedSetFormula boundedSparseComparisonFormula := by
  repeat' first
    | exact boundedValueFormula_bounded.subst _
    | exact boundedRestrictFormula_bounded.subst _
    | exact boundedEqualityLeftFormula_bounded.subst _
    | exact IsBoundedSetFormula.rel _ _
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedSparseComparisonFormula {W T C O E b p q : V} [IsTransitive T]
    (hC : C ‘ b ∈ W) (hO : O ‘ b ∈ W) (hE : E ‘ b ∈ W)
    (hr : p ↾ b ∈ T) (hσ : q ‘ b ∈ T) (hτ : p ‘ b ∈ T)
    (hR : IsForcingPreorder (C ‘ b) (O ‘ b))
    (hnσ : IsForcingName (C ‘ b) (q ‘ b)) (hnτ : IsForcingName (C ‘ b) (p ‘ b))
    (hH : IsAtomicTruthTable (C ‘ b) (O ‘ b) T (E ‘ b)) :
    boundedSparseComparisonFormula.Evalb ![W, T, C, O, E, b, p, q] ↔
      SparseSubsetComparison (C ‘ b) (O ‘ b) (p ↾ b) (q ‘ b) (p ‘ b) := by
  have he : boundedSparseComparisonFormula.Evalb ![W, T, C, O, E, b, p, q] ↔
      p ↾ b ∈ C ‘ b ∧ boundedEqualityLeftFormula.Evalb
        ![T, C ‘ b, O ‘ b, E ‘ b, q ‘ b, p ‘ b, p ↾ b] := by
    simp [boundedSparseComparisonFormula, hC, hO, hE, hr, hσ, hτ,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [he, sparseSubsetComparison_iff hR hnσ hnτ]
  exact (forcingSubsetConditions_bounded_iff hR hnσ hH hσ hτ).symm

end ZFVP
