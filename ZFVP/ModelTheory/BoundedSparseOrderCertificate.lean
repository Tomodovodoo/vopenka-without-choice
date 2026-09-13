import ZFVP.ModelTheory.BoundedSparseCarrierCut
import ZFVP.ModelTheory.BoundedSparseComparison
import ZFVP.SetTheory.NameHierarchyTableFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSparseOrderRowFormula : SetTheorySemisentence 7 :=
  “W T S C O E b. ∃ B ∈ W, ∃ R ∈ W, ∃ H ∈ W,
    !boundedValueFormula B C b ∧ !boundedValueFormula R O b ∧ !boundedValueFormula H E b ∧
    !boundedSparseCarrierCutFormula B S b ∧ !boundedAtomicTruthTableFormula T B R H ∧
    !boundedSubsetProductFormula R B B ∧
    ∀ p ∈ B, ∀ q ∈ B, !boundedPairMemberFormula R p q ↔
      ∀ c ∈ b, !boundedSparseComparisonFormula W T C O E c p q”

def boundedSparseOrderCertificateFormula : SetTheorySemisentence 7 :=
  “W T S a C O E. ∀ b ∈ a, !boundedSparseOrderRowFormula W T S C O E b”

theorem boundedSparseOrderRowFormula_bounded : IsBoundedSetFormula boundedSparseOrderRowFormula := by
  repeat' first
    | exact boundedValueFormula_bounded.subst _
    | exact boundedSparseCarrierCutFormula_bounded.subst _
    | exact boundedAtomicTruthTableFormula_bounded.subst _
    | exact boundedSubsetProductFormula_bounded.subst _
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | exact boundedSparseComparisonFormula_bounded.subst _
    | exact (boundedSparseComparisonFormula_bounded.subst _).neg
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

theorem boundedSparseOrderCertificateFormula_bounded :
    IsBoundedSetFormula boundedSparseOrderCertificateFormula :=
  .all (.bvar 3) (boundedSparseOrderRowFormula_bounded.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def SparseOrderCertificateRow (W T S C O E b : V) : Prop :=
  C ‘ b ∈ W ∧ O ‘ b ∈ W ∧ E ‘ b ∈ W ∧ C ‘ b = sparseCarrierCut S b ∧
    IsAtomicTruthTable (C ‘ b) (O ‘ b) T (E ‘ b) ∧ O ‘ b ⊆ (C ‘ b) ×ˢ (C ‘ b) ∧
    ∀ p ∈ C ‘ b, ∀ q ∈ C ‘ b, ⟨p, q⟩ₖ ∈ O ‘ b ↔
      ∀ c ∈ b, boundedSparseComparisonFormula.Evalb ![W, T, C, O, E, c, p, q]

theorem eval_boundedSparseOrderRowFormula {W T S C O E b : V} [IsTransitive T] :
    boundedSparseOrderRowFormula.Evalb ![W, T, S, C, O, E, b] ↔
      SparseOrderCertificateRow W T S C O E b := by
  simp [boundedSparseOrderRowFormula, SparseOrderCertificateRow,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_boundedAtomicTruthTableFormula, eval_boundedSubsetProductFormula]

theorem eval_boundedSparseOrderCertificateFormula {W T S a C O E : V} [IsTransitive T] :
    boundedSparseOrderCertificateFormula.Evalb ![W, T, S, a, C, O, E] ↔
      ∀ b ∈ a, SparseOrderCertificateRow W T S C O E b := by
  simp [boundedSparseOrderCertificateFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_boundedSparseOrderRowFormula]

end ZFVP
