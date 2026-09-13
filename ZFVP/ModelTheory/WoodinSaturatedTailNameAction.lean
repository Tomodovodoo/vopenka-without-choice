import ZFVP.ModelTheory.WoodinSparseTailNameAction
import ZFVP.ModelTheory.SaturatedPrefixMemberRank
import ZFVP.ModelTheory.SaturatedHartogsMemberRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem tailFunctionValueName_forces_rank_of_member_rank {P R top δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hQr : ∀ τ : ForcingName P, top ∈ atomicMembership P R τ.val Q.val →
      top ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName top δ]))
    {τ : V} (hτ : τ ∈ normalizedNamePool P R top δ Q.val) :
    top ∈ forcingFormula P R nameInHierarchyFormula
      (standardTuple ![tailFunctionValueName P R f.val τ, checkName top δ]) := by
  have hτ' := mem_sep_iff.mp hτ
  exact hQr ⟨_, tailFunctionValueName_isName _ _ _ _⟩
    (tailFunctionValueForcing_member hR ht Q S f g ⟨τ, hτ'.2.1⟩
      ⟨_, tailFunctionValueName_isName _ _ _ _⟩ hi hτ'.2.2.2
      (tailFunctionValueName_forces hR ht ht.1 f ⟨τ, hτ'.2.1⟩ hf))

theorem normalizedTailTwoStepMap_automorphism_of_member_rank {P R top δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hj : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, g.val, f.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hQr : ∀ τ : ForcingName P, top ∈ atomicMembership P R τ.val Q.val →
      top ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName top δ])) :
    let C := normalizedNameTwoStep P R top δ Q.val
    IsForcingAutomorphism C (nameTwoStepOrderOn P R S.val C)
      (normalizedTailTwoStepMap P R top δ Q.val f.val) :=
  normalizedTailTwoStepMap_automorphism hR ht hδ hP Q S f g hi hj hf hg
    (fun _ hτ ↦ tailFunctionValueName_forces_rank_of_member_rank hR ht Q S f g hi hf hQr hτ)
    (fun _ hτ ↦ tailFunctionValueName_forces_rank_of_member_rank hR ht Q S g f hj hg hQr hτ)

theorem sparseTailNameMap_automorphism_of_member_rank {a P R top δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hj : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, g.val, f.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hQr : ∀ τ : ForcingName P, top ∈ atomicMembership P R τ.val Q.val →
      top ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName top δ]))
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p) :
    IsForcingAutomorphism (sparseNormalizedTwoStep a P R top δ Q.val)
      (sparseNormalizedTwoStepOrder a P R top δ Q.val S.val)
      (sparseTailNameMap a P R top δ Q.val f.val) :=
  sparseTailNameMap_automorphism hsp
    (normalizedTailTwoStepMap_automorphism_of_member_rank hR ht hδ hP Q S f g hi hj hf hg hQr)

theorem sparseSaturatedPrefixTailNameMap_automorphism {a P R top κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ)
    (S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![saturatedWoodinPrefixPosetName P R top κ δ, S.val, f.val, g.val]))
    (hj : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![saturatedWoodinPrefixPosetName P R top κ δ, S.val, g.val, f.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p) :
    let Q := saturatedWoodinPrefixPosetName P R top κ δ
    IsForcingAutomorphism (sparseNormalizedTwoStep a P R top δ Q)
      (sparseNormalizedTwoStepOrder a P R top δ Q S.val) (sparseTailNameMap a P R top δ Q f.val) := by
  let Q : ForcingName P := ⟨saturatedWoodinPrefixPosetName P R top κ δ,
    saturatedWoodinPrefixPosetName_isName P R top κ δ⟩
  exact sparseTailNameMap_automorphism_of_member_rank hR ht hδ hP Q S f g hi hj hf hg
    (fun τ hτ ↦ saturatedWoodinPrefix_member_forces_rank hR ht hδ hP hκ τ hτ) hsp

theorem sparseSaturatedHartogsTailNameMap_automorphism {a P R top γ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ)
    (S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![saturatedHartogsPosetName P R top γ δ, S.val, f.val, g.val]))
    (hj : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![saturatedHartogsPosetName P R top γ δ, S.val, g.val, f.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p) :
    let Q := saturatedHartogsPosetName P R top γ δ
    IsForcingAutomorphism (sparseNormalizedTwoStep a P R top δ Q)
      (sparseNormalizedTwoStepOrder a P R top δ Q S.val) (sparseTailNameMap a P R top δ Q f.val) := by
  let Q : ForcingName P := ⟨saturatedHartogsPosetName P R top γ δ,
    saturatedHartogsPosetName_isName P R top γ δ⟩
  exact sparseTailNameMap_automorphism_of_member_rank hR ht hδ hP Q S f g hi hj hf hg
    (fun τ hτ ↦ saturatedHartogs_member_forces_rank hR ht hδ hP hγ τ hτ) hsp

end ZFVP
