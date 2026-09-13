import ZFVP.ModelTheory.WoodinTailNameOrderAction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def normalizedTailTwoStepValue (P R top f z : V) : V :=
  ⟨kpair.π₁ z, normalizedTailFunctionValueName P R top f (kpair.π₂ z)⟩ₖ

instance normalizedTailTwoStepValue_definable (P R top f : V) :
    ℒₛₑₜ-function₁[V] (normalizedTailTwoStepValue P R top f) := by
  unfold normalizedTailTwoStepValue
  apply Language.DefinableFunction₂.comp
  · definability
  · apply Language.DefinableFunction₁.comp
    definability

noncomputable def normalizedTailTwoStepMap (P R top δ Q f : V) : V :=
  definableGraph (normalizedNameTwoStep P R top δ Q)
    (normalizedTailTwoStepValue P R top f) (by infer_instance)

theorem normalizedTailTwoStepMap_value {P R top δ Q f z : V}
    (hz : z ∈ normalizedNameTwoStep P R top δ Q) :
    (normalizedTailTwoStepMap P R top δ Q f) ‘ z = normalizedTailTwoStepValue P R top f z :=
  value_definableGraph _ _ _ hz

theorem normalizedTailTwoStepValue_inverse {P R top δ z : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hg : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![g.val]))
    (hz : z ∈ normalizedNameTwoStep P R top δ Q.val) :
    normalizedTailTwoStepValue P R top g.val (normalizedTailTwoStepValue P R top f.val z) = z := by
  obtain ⟨p, _, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  have hτ' := mem_sep_iff.mp hτ
  simp only [normalizedTailTwoStepValue, kpair.π₁_kpair, kpair.π₂_kpair]
  rw [normalizedTailFunctionValueName_inverse hR ht Q S f g ⟨τ, hτ'.2.1⟩
    hi hf hg hτ'.2.2.2 hτ'.2.2.1]

theorem normalizedTailTwoStepValue_mem {P R top δ z : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (Q S f g : ForcingName P)
    (hi : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (hb : ∀ τ ∈ normalizedNamePool P R top δ Q.val,
      top ∈ forcingFormula P R nameInHierarchyFormula
        (standardTuple ![tailFunctionValueName P R f.val τ, checkName top δ]))
    (hz : z ∈ normalizedNameTwoStep P R top δ Q.val) :
    normalizedTailTwoStepValue P R top f.val z ∈ normalizedNameTwoStep P R top δ Q.val := by
  obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  simp only [normalizedTailTwoStepValue, kpair.π₁_kpair, kpair.π₂_kpair,
    normalizedNameTwoStep, kpair_mem_iff]
  exact ⟨hp, normalizedTailFunctionValueName_mem_pool hR ht hδ hP Q S f g hi hf hτ (hb τ hτ)⟩

theorem normalizedTailTwoStepMap_automorphism {P R top δ : V}
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
    let C := normalizedNameTwoStep P R top δ Q.val
    IsForcingAutomorphism C (nameTwoStepOrderOn P R S.val C)
      (normalizedTailTwoStepMap P R top δ Q.val f.val) := by
  dsimp only
  have hmem {z : V} (hz : z ∈ normalizedNameTwoStep P R top δ Q.val) :=
    normalizedTailTwoStepValue_mem hR ht hδ hP Q S f g hi hf hbf hz
  have hback {z : V} (hz : z ∈ normalizedNameTwoStep P R top δ Q.val) :=
    normalizedTailTwoStepValue_mem hR ht hδ hP Q S g f hj hg hbg hz
  have hm : normalizedTailTwoStepMap P R top δ Q.val f.val ∈
      (normalizedNameTwoStep P R top δ Q.val) ^ (normalizedNameTwoStep P R top δ Q.val) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hz ↦ hmem hz)
  refine ⟨hm, ?_, ?_, ?_⟩
  · intro a b z ha hb
    obtain ⟨ha', hza⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp ha
    obtain ⟨hb', hzb⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hb
    have he := congrArg (normalizedTailTwoStepValue P R top g.val) (hza.symm.trans hzb)
    rw [normalizedTailTwoStepValue_inverse hR ht Q S f g hi hf hg ha',
      normalizedTailTwoStepValue_inverse hR ht Q S f g hi hf hg hb'] at he
    exact he
  · apply subset_antisymm (range_subset_of_mem_function hm)
    intro z hz
    have ha := hback hz
    have hv := value_mem_range hm ha
    rw [normalizedTailTwoStepMap_value ha,
      normalizedTailTwoStepValue_inverse hR ht Q S g f hj hg hf hz] at hv
    exact hv
  · intro a ha b hb
    have ha' := hmem ha
    have hb' := hmem hb
    rw [normalizedTailTwoStepMap_value ha, normalizedTailTwoStepMap_value hb]
    obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp ha
    obtain ⟨q, hq, σ, hσ, rfl⟩ := mem_prod_iff.mp hb
    have hτ' := mem_sep_iff.mp hτ
    have hσ' := mem_sep_iff.mp hσ
    have ho := tailFunctionValueForcing_order hR ht hp Q S f g ⟨τ, hτ'.2.1⟩ ⟨σ, hσ'.2.1⟩
      ⟨_, normalizedTailFunctionValueName_isName hR ht.1⟩
      ⟨_, normalizedTailFunctionValueName_isName hR ht.1⟩ hi hτ'.2.2.2 hσ'.2.2.2
      (normalizedTailFunctionValueName_forces hR ht f ⟨τ, hτ'.2.1⟩ hf)
      (normalizedTailFunctionValueName_forces hR ht f ⟨σ, hσ'.2.1⟩ hf)
    simp only [normalizedTailTwoStepValue, kpair.π₁_kpair, kpair.π₂_kpair] at ha' hb' ⊢
    rw [pair_mem_nameTwoStepOrderOn, pair_mem_nameTwoStepOrderOn]
    simp only [show ⟨p, τ⟩ₖ ∈ normalizedNameTwoStep P R top δ Q.val from kpair_mem_iff.mpr ⟨hp, hτ⟩,
      show ⟨q, σ⟩ₖ ∈ normalizedNameTwoStep P R top δ Q.val from kpair_mem_iff.mpr ⟨hq, hσ⟩,
      ha', hb', true_and]
    exact and_congr Iff.rfl ho

theorem normalizedTailTwoStepMap_first {P R top δ Q f z : V}
    (hz : z ∈ normalizedNameTwoStep P R top δ Q) :
    kpair.π₁ ((normalizedTailTwoStepMap P R top δ Q f) ‘ z) = kpair.π₁ z := by
  rw [normalizedTailTwoStepMap_value hz]
  exact kpair.π₁_kpair _ _

theorem normalizedTailTwoStepMap_empty {P R top δ Q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (f : ForcingName P)
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val]))
    (h0 : top ∈ tailFunctionValueForcing P R f.val ∅ ∅) {p : V}
    (hp : ⟨p, ∅⟩ₖ ∈ normalizedNameTwoStep P R top δ Q) :
    (normalizedTailTwoStepMap P R top δ Q f.val) ‘ ⟨p, ∅⟩ₖ = ⟨p, ∅⟩ₖ := by
  rw [normalizedTailTwoStepMap_value hp]
  simp only [normalizedTailTwoStepValue, kpair.π₁_kpair, kpair.π₂_kpair]
  rw [normalizedTailFunctionValueName_empty hR ht f hf h0]

end ZFVP

