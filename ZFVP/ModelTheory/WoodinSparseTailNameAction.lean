import ZFVP.ModelTheory.WoodinTailTwoStepAction
import ZFVP.ModelTheory.SparseNormalizedTwoStep

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparseTailNameMap (a P R top δ Q f : V) : V :=
  let W := normalizedNamePool P R top δ Q
  compose (sparsePairDecode a P W)
    (compose (normalizedTailTwoStepMap P R top δ Q f) (sparsePairEncode a P W))

theorem sparseTailNameMap_automorphism {a P R top δ Q S f : V}
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)
    (hi : IsForcingAutomorphism (normalizedNameTwoStep P R top δ Q)
      (nameTwoStepOrderOn P R S (normalizedNameTwoStep P R top δ Q))
      (normalizedTailTwoStepMap P R top δ Q f)) :
    IsForcingAutomorphism (sparseNormalizedTwoStep a P R top δ Q)
      (sparseNormalizedTwoStepOrder a P R top δ Q S) (sparseTailNameMap a P R top δ Q f) := by
  have hd := sparsePairDecode_isomorphism («W» := normalizedNamePool P R top δ Q)
    (R := nameTwoStepOrderOn P R S (normalizedNameTwoStep P R top δ Q)) hsp
  have he := sparsePairEncode_isomorphism («W» := normalizedNamePool P R top δ Q)
    (R := nameTwoStepOrderOn P R S (normalizedNameTwoStep P R top δ Q)) hsp
  have hii : IsForcingIsomorphism (normalizedNameTwoStep P R top δ Q)
      (nameTwoStepOrderOn P R S (normalizedNameTwoStep P R top δ Q))
      (normalizedNameTwoStep P R top δ Q)
      (nameTwoStepOrderOn P R S (normalizedNameTwoStep P R top δ Q))
      (normalizedTailTwoStepMap P R top δ Q f) := hi
  exact hd.comp (hii.comp he)

theorem sparseTailNameMap_value {a P R top δ Q f q : V}
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)
    (hm : normalizedTailTwoStepMap P R top δ Q f ∈
      (normalizedNameTwoStep P R top δ Q) ^ (normalizedNameTwoStep P R top δ Q))
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ Q) :
    (sparseTailNameMap a P R top δ Q f) ‘ q =
      sparseAppend a (q ↾ a) (normalizedTailFunctionValueName P R top f (q ‘ a)) := by
  have hd := sparsePairDecode_isomorphism («W» := normalizedNamePool P R top δ Q) (R := (∅ : V)) hsp
  have he := sparsePairEncode_isomorphism («W» := normalizedNamePool P R top δ Q) (R := (∅ : V)) hsp
  unfold sparseTailNameMap
  dsimp only
  rw [value_compose_of_mem_function hd.1 (compose_function hm he.1) hq,
    value_compose_of_mem_function hm he.1 (function_value_mem hd.1 hq),
    sparsePairEncode_value_of_mem hsp (function_value_mem hm (function_value_mem hd.1 hq)),
    normalizedTailTwoStepMap_value (function_value_mem hd.1 hq), sparsePairDecode_value hq]
  simp only [normalizedTailTwoStepValue, kpair.π₁_kpair, kpair.π₂_kpair]

theorem sparseTailNameMap_restrict {a P R top δ Q f q : V}
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)
    (hm : normalizedTailTwoStepMap P R top δ Q f ∈
      (normalizedNameTwoStep P R top δ Q) ^ (normalizedNameTwoStep P R top δ Q))
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ Q) :
    ((sparseTailNameMap a P R top δ Q f) ‘ q) ↾ a = q ↾ a := by
  have hs := hsp _ (mem_sparsePairCarrier_iff.mp hq).2.1
  let := hs.1
  rw [sparseTailNameMap_value hsp hm hq]
  exact sparseAppend_restrict hs.2.1

theorem sparseTailNameMap_restrict_earlier {a b P R top δ Q f q : V}
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)
    (hm : normalizedTailTwoStepMap P R top δ Q f ∈
      (normalizedNameTwoStep P R top δ Q) ^ (normalizedNameTwoStep P R top δ Q))
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ Q) (hb : b ⊆ a) :
    ((sparseTailNameMap a P R top δ Q f) ‘ q) ↾ b = q ↾ b := by
  rw [← restrict_restrict_of_subset hb, sparseTailNameMap_restrict hsp hm hq,
    restrict_restrict_of_subset hb]

theorem sparseTailNameMap_empty_tail {a P R top δ Q q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (f : ForcingName P)
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (h0 : top ∈ tailFunctionValueForcing P R f.val ∅ ∅)
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)
    (hm : normalizedTailTwoStepMap P R top δ Q f.val ∈
      (normalizedNameTwoStep P R top δ Q) ^ (normalizedNameTwoStep P R top δ Q))
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ Q) (hqa : q ‘ a = ∅) :
    (sparseTailNameMap a P R top δ Q f.val) ‘ q = q := by
  rw [sparseTailNameMap_value hsp hm hq, hqa,
    normalizedTailFunctionValueName_empty hR ht f hf h0, sparseAppend_empty]
  have h := sparseAppend_reconstruct (mem_sparsePairCarrier_iff.mp hq).1
  rwa [hqa, sparseAppend_empty] at h

theorem sparseTailNameMap_function {a P R top δ Q f : V}
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)
    (hm : normalizedTailTwoStepMap P R top δ Q f ∈
      (normalizedNameTwoStep P R top δ Q) ^ (normalizedNameTwoStep P R top δ Q)) :
    sparseTailNameMap a P R top δ Q f ∈
      (sparseNormalizedTwoStep a P R top δ Q) ^ (sparseNormalizedTwoStep a P R top δ Q) := by
  have hd := sparsePairDecode_isomorphism («W» := normalizedNamePool P R top δ Q) (R := (∅ : V)) hsp
  have he := sparsePairEncode_isomorphism («W» := normalizedNamePool P R top δ Q) (R := (∅ : V)) hsp
  exact compose_function hd.1 (compose_function hm he.1)

theorem sparseTailNameMap_inverse_value {a P R top δ q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)
    (hmf : normalizedTailTwoStepMap P R top δ Q.val f.val ∈
      (normalizedNameTwoStep P R top δ Q.val) ^ (normalizedNameTwoStep P R top δ Q.val))
    (hmg : normalizedTailTwoStepMap P R top δ Q.val g.val ∈
      (normalizedNameTwoStep P R top δ Q.val) ^ (normalizedNameTwoStep P R top δ Q.val))
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ Q.val) :
    (sparseTailNameMap a P R top δ Q.val g.val) ‘
      ((sparseTailNameMap a P R top δ Q.val f.val) ‘ q) = q := by
  have hq' := mem_sparsePairCarrier_iff.mp hq
  have hs := hsp _ hq'.2.1
  let := hs.1
  have hτ := mem_sep_iff.mp hq'.2.2
  have himage := function_value_mem (sparseTailNameMap_function hsp hmf) hq
  rw [sparseTailNameMap_value hsp hmg himage, sparseTailNameMap_restrict hsp hmf hq,
    sparseTailNameMap_value hsp hmf hq, sparseAppend_value_new hs.2.1,
    normalizedTailFunctionValueName_inverse hR ht Q S f g ⟨q ‘ a, hτ.2.1⟩
      hi hf hg hτ.2.2.2 hτ.2.2.1]
  exact sparseAppend_reconstruct hq'.1

theorem normalizedTailFunctionValueName_eq_empty_iff {P R top δ τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hf0 : top ∈ tailFunctionValueForcing P R f.val ∅ ∅)
    (hg0 : top ∈ tailFunctionValueForcing P R g.val ∅ ∅)
    (hτ : τ ∈ normalizedNamePool P R top δ Q.val) :
    normalizedTailFunctionValueName P R top f.val τ = ∅ ↔ τ = ∅ := by
  have hτ' := mem_sep_iff.mp hτ
  constructor
  · intro he
    have hn := normalizedTailFunctionValueName_inverse hR ht Q S f g ⟨τ, hτ'.2.1⟩
      hi hf hg hτ'.2.2.2 hτ'.2.2.1
    rw [he, normalizedTailFunctionValueName_empty hR ht g hg hg0] at hn
    exact hn.symm
  · intro he
    rw [he, normalizedTailFunctionValueName_empty hR ht f hf hf0]

theorem sparseTailNameMap_domain {a P R top δ q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hf0 : top ∈ tailFunctionValueForcing P R f.val ∅ ∅)
    (hg0 : top ∈ tailFunctionValueForcing P R g.val ∅ ∅)
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)
    (hm : normalizedTailTwoStepMap P R top δ Q.val f.val ∈
      (normalizedNameTwoStep P R top δ Q.val) ^ (normalizedNameTwoStep P R top δ Q.val))
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ Q.val) :
    domain ((sparseTailNameMap a P R top δ Q.val f.val) ‘ q) = domain q := by
  have hq' := mem_sparsePairCarrier_iff.mp hq
  have hz := normalizedTailFunctionValueName_eq_empty_iff hR ht Q S f g hi hf hg hf0 hg0 hq'.2.2
  rw [sparseTailNameMap_value hsp hm hq, sparseAppend_domain, hz]
  simpa only [sparseAppend_domain] using congrArg domain (sparseAppend_reconstruct hq'.1)

end ZFVP



