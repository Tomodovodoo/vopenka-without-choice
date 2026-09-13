import ZFVP.ModelTheory.NormalizedReverseOrderComparison
import ZFVP.ModelTheory.SparseNormalizedTwoStep

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparseNormalizedTwoStep_append_reverse_order {a P R one δ Q p q τ σ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hQ : IsForcingName P Q)
    (hsp : ∀ r ∈ P, IsSparseFunctionOn a r) (hp : p ∈ P) (hq : q ∈ P)
    (hτ : τ ∈ normalizedNamePool P R one δ Q) (hσ : σ ∈ normalizedNamePool P R one δ Q) :
    ⟨sparseAppend a p τ, sparseAppend a q σ⟩ₖ ∈
      sparseNormalizedTwoStepOrder a P R one δ Q (reverseInclusionOrderName P R Q) ↔
      ⟨p, q⟩ₖ ∈ R ∧ p ∈ forcingFormula P R isSubsetOf (standardTuple ![σ, τ]) := by
  rw [sparseNormalizedTwoStepOrder, mem_forcingPullbackOrder_iff]
  have hp' := sparseAppend_mem_pairCarrier hsp hp hτ
  have hq' := sparseAppend_mem_pairCarrier hsp hq hσ
  change _ ∈ sparseNormalizedTwoStep a P R one δ Q at hp' hq'
  simp only [hp', hq', true_and]
  rw [sparsePairDecode_append hsp hp hτ, sparsePairDecode_append hsp hq hσ]
  exact normalizedNameTwoStep_reverse_order_comparison hR ht hQ hp hq hτ hσ

theorem sparseNormalizedTwoStep_reverse_order_on_base {a P R one δ Q p q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hQ : IsForcingName P Q)
    (hsp : ∀ r ∈ P, IsSparseFunctionOn a r)
    (h0 : (∅ : V) ∈ normalizedNamePool P R one δ Q) (hp : p ∈ P) (hq : q ∈ P) :
    ⟨p, q⟩ₖ ∈ sparseNormalizedTwoStepOrder a P R one δ Q (reverseInclusionOrderName P R Q) ↔
      ⟨p, q⟩ₖ ∈ R := by
  have hh := sparseNormalizedTwoStep_append_reverse_order hR ht hQ hsp hp hq h0 h0
  rw [sparseAppend_empty, sparseAppend_empty] at hh
  have hs : p ∈ forcingFormula P R isSubsetOf (standardTuple ![(∅ : V), ∅]) := by
    let t : ForcingName P := ⟨∅, empty_forcingName P⟩
    let φ : SetTheorySemisentence 2 := .rel Language.Set.Rel.eq ![.bvar 0, .bvar 1]
    apply forcingFormula_entailment φ isSubsetOf (by
      intro W _ _ _ v hv
      have he : v 0 = v 1 := by simpa [φ, Structure.rel] using hv
      simp [he]) hR ht hp ![t, t]
    simpa only [φ, forcingFormula_rel, forcingAtomic, forcingTermValue, value_standardTuple,
      Matrix.cons_val_zero, Matrix.cons_val_one, atomicEquality_refl hR] using hp
  simpa only [hs, and_true] using hh

end ZFVP
