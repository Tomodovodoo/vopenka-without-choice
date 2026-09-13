import ZFVP.ModelTheory.WoodinTailNameInverseForcing
import ZFVP.SetTheory.DefinableGraph
import ZFVP.ModelTheory.NamedFunctionValues

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance normalizedTailFunctionValueName_definable (P R top f : V) :
    ℒₛₑₜ-function₁[V] (normalizedTailFunctionValueName P R top f) := by
  unfold normalizedTailFunctionValueName
  apply Language.DefinableFunction₁.comp
  infer_instance

noncomputable def normalizedTailPoolMap (P R top δ Q f : V) : V :=
  definableGraph (normalizedNamePool P R top δ Q)
    (normalizedTailFunctionValueName P R top f) (by infer_instance)

theorem normalizedTailPoolMap_value {P R top δ Q f τ : V}
    (hτ : τ ∈ normalizedNamePool P R top δ Q) :
    (normalizedTailPoolMap P R top δ Q f) ‘ τ = normalizedTailFunctionValueName P R top f τ :=
  value_definableGraph _ _ _ hτ

theorem normalizedTailFunctionValueName_mem_pool {P R top δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    {τ : V} (hτ : τ ∈ normalizedNamePool P R top δ Q.val)
    (hb : top ∈ forcingFormula P R nameInHierarchyFormula
      (standardTuple ![tailFunctionValueName P R f.val τ, checkName top δ])) :
    normalizedTailFunctionValueName P R top f.val τ ∈ normalizedNamePool P R top δ Q.val := by
  have hτ' := mem_sep_iff.mp hτ
  apply mem_sep_iff.mpr
  refine ⟨normalizedTailFunctionValueName_mem_hierarchy hR ht hδ hP hb,
    normalizedTailFunctionValueName_isName hR ht.1,
    normalizedTailFunctionValueName_normalized hR ht.1, ?_⟩
  exact tailFunctionValueForcing_member hR ht Q S f g ⟨τ, hτ'.2.1⟩
    ⟨_, normalizedTailFunctionValueName_isName hR ht.1⟩ hi hτ'.2.2.2
    (normalizedTailFunctionValueName_forces hR ht f ⟨τ, hτ'.2.1⟩ hf)

theorem normalizedTailPoolMap_bijection {P R top δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hj : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, g.val, f.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hbf : ∀ τ ∈ normalizedNamePool P R top δ Q.val,
      top ∈ forcingFormula P R nameInHierarchyFormula
        (standardTuple ![tailFunctionValueName P R f.val τ, checkName top δ]))
    (hbg : ∀ τ ∈ normalizedNamePool P R top δ Q.val,
      top ∈ forcingFormula P R nameInHierarchyFormula
        (standardTuple ![tailFunctionValueName P R g.val τ, checkName top δ])) :
    let W := normalizedNamePool P R top δ Q.val
    let F := normalizedTailPoolMap P R top δ Q.val f.val
    F ∈ W ^ W ∧ Injective F ∧ range F = W := by
  dsimp only
  have hmem {τ : V} (hτ : τ ∈ normalizedNamePool P R top δ Q.val) :=
    normalizedTailFunctionValueName_mem_pool hR ht hδ hP Q S f g hi hf hτ (hbf τ hτ)
  have hback {τ : V} (hτ : τ ∈ normalizedNamePool P R top δ Q.val) :=
    normalizedTailFunctionValueName_mem_pool hR ht hδ hP Q S g f hj hg hτ (hbg τ hτ)
  have hm : normalizedTailPoolMap P R top δ Q.val f.val ∈
      (normalizedNamePool P R top δ Q.val) ^ (normalizedNamePool P R top δ Q.val) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hτ ↦ hmem hτ)
  refine ⟨hm, ?_, ?_⟩
  · intro a b z ha hb
    obtain ⟨ha', hza⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp ha
    obtain ⟨hb', hzb⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hb
    have ha'' := mem_sep_iff.mp ha'
    have hb'' := mem_sep_iff.mp hb'
    have he := congrArg (normalizedTailFunctionValueName P R top g.val) (hza.symm.trans hzb)
    rw [normalizedTailFunctionValueName_inverse hR ht Q S f g ⟨a, ha''.2.1⟩
      hi hf hg ha''.2.2.2 ha''.2.2.1,
      normalizedTailFunctionValueName_inverse hR ht Q S f g ⟨b, hb''.2.1⟩
      hi hf hg hb''.2.2.2 hb''.2.2.1] at he
    exact he
  · apply subset_antisymm (range_subset_of_mem_function hm)
    intro τ hτ
    have hτ' := mem_sep_iff.mp hτ
    have ha := hback hτ
    have hv := value_mem_range hm ha
    rw [normalizedTailPoolMap_value ha,
      normalizedTailFunctionValueName_inverse hR ht Q S g f ⟨τ, hτ'.2.1⟩
        hj hg hf hτ'.2.2.2 hτ'.2.2.1] at hv
    exact hv

theorem normalizedTailFunctionValueName_empty {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (f : ForcingName P)
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (h0 : top ∈ tailFunctionValueForcing P R f.val ∅ ∅) :
    normalizedTailFunctionValueName P R top f.val ∅ = ∅ := by
  have ha := normalizedTailFunctionValueName_forces hR ht f ⟨∅, empty_forcingName P⟩ hf
  have ha' : ForcesNamedFunctionValue P R top f.val top ∅
      (normalizedTailFunctionValueName P R top f.val ∅) := by
    simpa [ForcesNamedFunctionValue, tailFunctionValueForcing, checkName_empty] using ha
  have h0' : ForcesNamedFunctionValue P R top f.val top ∅ ∅ := by
    simpa [ForcesNamedFunctionValue, tailFunctionValueForcing, checkName_empty] using h0
  have hn := normalizedTailFunctionValueName_isName (f := f.val) (τ := (∅ : V)) hR ht.1
  have he := forcesNamedFunctionValue_unique hR ht f.property hn (empty_forcingName P) ha' h0'
  have h := forcingLeastRankName_empty_of_forced hR ht.1 hn he
  rw [normalizedTailFunctionValueName_normalized hR ht.1] at h
  exact h

end ZFVP


