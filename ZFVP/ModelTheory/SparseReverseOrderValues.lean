import ZFVP.ModelTheory.SparseReverseOrderComparison

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparseNormalizedTwoStep_reverse_order_values {a P R one δ Q p q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hQ : IsForcingName P Q)
    (hsp : ∀ r ∈ P, IsSparseFunctionOn a r)
    (hp : p ∈ sparseNormalizedTwoStep a P R one δ Q)
    (hq : q ∈ sparseNormalizedTwoStep a P R one δ Q) :
    ⟨p, q⟩ₖ ∈ sparseNormalizedTwoStepOrder a P R one δ Q (reverseInclusionOrderName P R Q) ↔
      ⟨p ↾ a, q ↾ a⟩ₖ ∈ R ∧
      p ↾ a ∈ forcingFormula P R isSubsetOf (standardTuple ![q ‘ a, p ‘ a]) := by
  have hp' := mem_sparsePairCarrier_iff.mp hp
  have hq' := mem_sparsePairCarrier_iff.mp hq
  have he := sparseNormalizedTwoStep_append_reverse_order hR ht hQ hsp hp'.2.1 hq'.2.1 hp'.2.2 hq'.2.2
  rwa [sparseAppend_reconstruct hp'.1, sparseAppend_reconstruct hq'.1] at he

end ZFVP
