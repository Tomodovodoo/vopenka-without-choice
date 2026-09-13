import ZFVP.ModelTheory.WoodinCanonicalTailCommonBound
import ZFVP.ModelTheory.WoodinSparseTailCommonExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem canonicalTailCommonName_empty {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (f : ForcingName P)
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (h0 : top ∈ tailFunctionValueForcing P R f.val ∅ ∅) :
    canonicalTailCommonName P R top f.val ∅ ∅ = ∅ := by
  rw [canonicalTailCommonName, normalizedTailFunctionValueName_empty hR ht f hf h0,
    normalizedBinaryNameUnion, union_empty, forcingLeastRankName_empty hR ht.1]

theorem canonicalTailCommonName_support {a P R top p q r : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (f : ForcingName P)
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (h0 : top ∈ tailFunctionValueForcing P R f.val ∅ ∅) :
    domain (sparseAppend a r (canonicalTailCommonName P R top f.val (p ‘ a) (q ‘ a))) ⊆
      (domain r ∪ domain p) ∪ domain q := by
  classical
  rw [sparseAppend_domain]
  split_ifs with he
  · intro z hz
    exact mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl hz)))
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · by_cases hp : z ∈ domain p
      · exact mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hp)))
      · by_cases hq : z ∈ domain q
        · exact mem_union_iff.mpr (Or.inr hq)
        · apply False.elim
          apply he
          rw [value_eq_empty_of_not_mem_domain hp, value_eq_empty_of_not_mem_domain hq]
          exact canonicalTailCommonName_empty hR ht f hf h0
    · exact mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl hz)))
theorem canonicalSparse_commonExtension_of_member_rank {a P R top δ p q r : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (Q S k d f g : ForcingName P)
    (hp : p ∈ sparseNormalizedTwoStep a P R top δ Q.val)
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ Q.val)
    (hr : r ∈ P) (hrp : ⟨r,p ↾ a⟩ₖ ∈ R) (hrq : ⟨r,q ↾ a⟩ₖ ∈ R)
    (hpre : top ∈ forcingFormula P R collapseDisplacementPreInputFormula
      (standardTuple ![Q.val,S.val,k.val,d.val,p ‘ a,q ‘ a]))
    (hout : top ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple ![Q.val,S.val,k.val,d.val,p ‘ a,q ‘ a,f.val,g.val]))
    (hQr : ∀ τ : ForcingName P, top ∈ atomicMembership P R τ.val Q.val →
      top ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val,checkName top δ]))
    (hsp : ∀ z ∈ P, IsSparseFunctionOn a z) :
    let C := sparseNormalizedTwoStep a P R top δ Q.val
    let T := sparseNormalizedTwoStepOrder a P R top δ Q.val S.val
    let F := sparseTailNameMap a P R top δ Q.val f.val
    let ν := canonicalTailCommonName P R top f.val (p ‘ a) (q ‘ a)
    let w := sparseAppend a r ν
    w ∈ C ∧ ⟨w,F ‘ p⟩ₖ ∈ T ∧ ⟨w,q⟩ₖ ∈ T ∧ w ↾ a = r ∧ w ‘ a = ν ∧
      domain w ⊆ (domain r ∪ domain p) ∪ domain q := by
  have hp' := (mem_sparseNormalizedTwoStep_iff.mp hp).2.2
  have hq' := (mem_sparseNormalizedTwoStep_iff.mp hq).2.2
  let x : ForcingName P := ⟨p ‘ a, (mem_sep_iff.mp hp').2.1⟩
  let y : ForcingName P := ⟨q ‘ a, (mem_sep_iff.mp hq').2.1⟩
  have hi := canonicalTailOutput_inverse hR ht ht.1 ![Q,S,k,d,x,y,f,g] hout
  have hj := canonicalTailOutput_inverse_reverse hR ht ht.1 ![Q,S,k,d,x,y,f,g] hout
  have hf := canonicalTailOutput_function hR ht ht.1 ![Q,S,k,d,x,y,f,g] hout
  have hg := canonicalTailOutput_function_reverse hR ht ht.1 ![Q,S,k,d,x,y,f,g] hout
  have hn := normalizedTailTwoStepMap_automorphism_of_member_rank hR ht hδ hP Q S f g hi hj hf hg hQr
  have hF := sparseTailNameMap_automorphism hsp hn
  have hFp := function_value_mem hF.1 hp
  have hres := sparseTailNameMap_restrict hsp hn.1 hp
  have hs := hsp _ (mem_sparseNormalizedTwoStep_iff.mp hp).2.1
  let := hs.1
  have htail : ((sparseTailNameMap a P R top δ Q.val f.val) ‘ p) ‘ a =
      normalizedTailFunctionValueName P R top f.val (p ‘ a) := by
    rw [sparseTailNameMap_value hsp hn.1 hp]
    exact sparseAppend_value_new hs.2.1
  have hb := canonicalTailCommonName_spec_of_member_rank hR ht hδ hP Q S k d x y f g hpre hout hp' hq' hQr
  have hc := sparseTail_commonExtension hR ht hsp hr hb.1 hFp hq
    (hres.symm ▸ hrp) hrq (htail.symm ▸ hb.2.1) hb.2.2
  have hsupp := canonicalTailCommonName_support (a := a) (p := p) (q := q) (r := r) hR ht f hf
    (canonicalTailOutput_empty hR ht ht.1 ![Q,S,k,d,x,y,f,g] hout)
  exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2,hsupp⟩

theorem sparseCanonicalPrefixDisplacement_commonExtension {a P R top κ δ p q r : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : top ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName top κ]))
    (hp : p ∈ sparseNormalizedTwoStep a P R top δ (saturatedWoodinPrefixPosetName P R top κ δ))
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ (saturatedWoodinPrefixPosetName P R top κ δ))
    (hr : r ∈ P) (hrp : ⟨r,p ↾ a⟩ₖ ∈ R) (hrq : ⟨r,q ↾ a⟩ₖ ∈ R)
    (hsp : ∀ z ∈ P, IsSparseFunctionOn a z) :
    let Q := saturatedWoodinPrefixPosetName P R top κ δ
    let S := saturatedWoodinPrefixOrderName P R top κ δ
    let f := woodinCollapseDisplacementName P R (checkName top κ) (checkName top δ) (p ‘ a) (q ‘ a)
    let F := sparseCanonicalPrefixDisplacement a P R top κ δ (p ‘ a) (q ‘ a)
    let ν := canonicalTailCommonName P R top f (p ‘ a) (q ‘ a)
    let w := sparseAppend a r ν
    let T := sparseNormalizedTwoStepOrder a P R top δ Q S
    w ∈ sparseNormalizedTwoStep a P R top δ Q ∧ ⟨w,F ‘ p⟩ₖ ∈ T ∧ ⟨w,q⟩ₖ ∈ T ∧
      w ↾ a = r ∧ w ‘ a = ν ∧ domain w ⊆ (domain r ∪ domain p) ∪ domain q := by
  let Q : ForcingName P := ⟨_, saturatedWoodinPrefixPosetName_isName P R top κ δ⟩
  let S : ForcingName P := ⟨_, saturatedWoodinPrefixOrderName_isName P R top κ δ⟩
  let k : ForcingName P := ⟨_, checkName_isName ht.1 κ⟩
  let d : ForcingName P := ⟨_, checkName_isName ht.1 δ⟩
  have hp' := (mem_sparseNormalizedTwoStep_iff.mp hp).2.2
  have hq' := (mem_sparseNormalizedTwoStep_iff.mp hq).2.2
  let x : ForcingName P := ⟨p ‘ a, (mem_sep_iff.mp hp').2.1⟩
  let y : ForcingName P := ⟨q ‘ a, (mem_sep_iff.mp hq').2.1⟩
  let f : ForcingName P := ⟨_, woodinCollapseDisplacementName_isName P R k.val d.val x.val y.val⟩
  let g : ForcingName P := ⟨_, collapseConverseName_isName P R f.val⟩
  have hpQ := (mem_sep_iff.mp hp').2.2.2
  have hqQ := (mem_sep_iff.mp hq').2.2.2
  have hpre := collapseDisplacement_forces_preInput hR ht ht.1 Q S k d x y hκ
    (forces_checked_ordinal hR ht hδ.1 ht.1)
    (saturatedWoodinPrefixPosetName_forces hR ht hδ hP hκδ ht.1)
    (reverseInclusionOrderName_forces hR ht ht.1 Q) hpQ hqQ
  have hout := saturatedPrefix_displacementName_forces_output hR ht hδ hP hκδ hκ x y hpQ hqQ
  exact canonicalSparse_commonExtension_of_member_rank hR ht hδ hP Q S k d f g hp hq hr hrp hrq hpre hout
    (fun τ hτ ↦ saturatedWoodinPrefix_member_forces_rank hR ht hδ hP hκδ τ hτ) hsp
theorem sparseCanonicalHartogsDisplacement_commonExtension {a P R top γ δ p q r : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγδ : γ ∈ δ)
    (hγ : top ∈ forcingFormula P R regularCardinalFormula (standardTuple ![hartogsNumberName P R (checkName top γ)]))
    (hp : p ∈ sparseNormalizedTwoStep a P R top δ (saturatedHartogsPosetName P R top γ δ))
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ (saturatedHartogsPosetName P R top γ δ))
    (hr : r ∈ P) (hrp : ⟨r,p ↾ a⟩ₖ ∈ R) (hrq : ⟨r,q ↾ a⟩ₖ ∈ R)
    (hsp : ∀ z ∈ P, IsSparseFunctionOn a z) :
    let Q := saturatedHartogsPosetName P R top γ δ
    let S := saturatedHartogsOrderName P R top γ δ
    let f := woodinCollapseDisplacementName P R (hartogsNumberName P R (checkName top γ)) (checkName top δ) (p ‘ a) (q ‘ a)
    let F := sparseCanonicalHartogsDisplacement a P R top γ δ (p ‘ a) (q ‘ a)
    let ν := canonicalTailCommonName P R top f (p ‘ a) (q ‘ a)
    let w := sparseAppend a r ν
    let T := sparseNormalizedTwoStepOrder a P R top δ Q S
    w ∈ sparseNormalizedTwoStep a P R top δ Q ∧ ⟨w,F ‘ p⟩ₖ ∈ T ∧ ⟨w,q⟩ₖ ∈ T ∧
      w ↾ a = r ∧ w ‘ a = ν ∧ domain w ⊆ (domain r ∪ domain p) ∪ domain q := by
  let Q : ForcingName P := ⟨_, saturatedHartogsPosetName_isName P R top γ δ⟩
  let S : ForcingName P := ⟨_, reverseInclusionOrderName_isName P R Q.val⟩
  let k : ForcingName P := ⟨_, hartogsNumberName_isName P R (checkName top γ)⟩
  let d : ForcingName P := ⟨_, checkName_isName ht.1 δ⟩
  have hp' := (mem_sparseNormalizedTwoStep_iff.mp hp).2.2
  have hq' := (mem_sparseNormalizedTwoStep_iff.mp hq).2.2
  let x : ForcingName P := ⟨p ‘ a, (mem_sep_iff.mp hp').2.1⟩
  let y : ForcingName P := ⟨q ‘ a, (mem_sep_iff.mp hq').2.1⟩
  let f : ForcingName P := ⟨_, woodinCollapseDisplacementName_isName P R k.val d.val x.val y.val⟩
  let g : ForcingName P := ⟨_, collapseConverseName_isName P R f.val⟩
  have hpQ := (mem_sep_iff.mp hp').2.2.2
  have hqQ := (mem_sep_iff.mp hq').2.2.2
  have hpre := collapseDisplacement_forces_preInput hR ht ht.1 Q S k d x y hγ
    (forces_checked_ordinal hR ht hδ.1 ht.1)
    (saturatedHartogsPosetName_forces hR ht hδ hP hγδ ht.1)
    (reverseInclusionOrderName_forces hR ht ht.1 Q) hpQ hqQ
  have hout := saturatedHartogs_displacementName_forces_output hR ht hδ hP hγδ hγ x y hpQ hqQ
  exact canonicalSparse_commonExtension_of_member_rank hR ht hδ hP Q S k d f g hp hq hr hrp hrq hpre hout
    (fun τ hτ ↦ saturatedHartogs_member_forces_rank hR ht hδ hP hγδ τ hτ) hsp
end ZFVP
