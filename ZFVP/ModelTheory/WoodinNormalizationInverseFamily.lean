import ZFVP.ModelTheory.WoodinNormalizationInverseCoherence
import ZFVP.ModelTheory.WoodinRawInverseSingular

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinNormalizationInverse_family {Ω θ s K m : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hs : IsWoodinIteration Ω θ s K)
    (h : IsForcingNormalizationFamily θ s m) (hθ : θ ∈ Ω) (h0 : ∅ ∈ θ)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula
        (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) :
    IsForcingNormalizationFamily (succ θ) (woodinInverseSourceCode θ s K)
      (woodinNormalizationInverse θ s K m) := by
  obtain ⟨hR, ht, hc, hP, hI⟩ := hs.normalizationInverse_inputs hΩ hθ h0 hlim hγ hDC
  obtain ⟨hr, ho, he⟩ := forcingNormalizationInverse_base hs.code h h0
  have hT := forcingOrderRestriction_preorder hR hr.inclusion
  have hone : forcingInverseCodeTop θ s ∈ forcingMapFixedPoints (forcingInverseCodePoset θ s)
      (forcingNormalizationInverseMap θ s m) := mem_sep_iff.mpr ⟨ht.1, ho⟩
  have hI' := hr.iterand_nameAction hR hT he hI
  have ht' := hr.top_of_mem ht hone
  have hTnew := normalizedNameTwoStep_preorder (δ := forcingInverseSourceCutoff θ s (woodinLimitCardinal K))
    hT ht' hI'.posetName hI'.orderName hI'.preorder
  have hrnew := woodinNormalizationInverseMap_retraction hr hR ht hc hP hI ho he
  have henew (z : V) := woodinNormalizationInverseMap_equivalent hr hR ht hc hP hI ho he (z := z)
  have htnew := woodinNormalizationInverseMap_top hr hR ht hc hP hI ho he
  simp only [woodinInverseSourceCode_poset, woodinInverseSourceCode_order, woodinInverseSourceCode_top]
    at hrnew henew htnew
  rw [woodinInverseSourceCode_twoStepColumn]
  unfold woodinNormalizationInverse forcingTwoStepColumnCode
  apply h.extend hrnew hTnew henew htnew
  · intro i hi z hz
    have hz' : z ∈ (forcingCodeP (woodinInverseSourceCode θ s K)) ‘ θ := by
      simpa only [woodinInverseSourceCode_poset] using hz
    have hh := woodinNormalizationInverse_projection_coherent hs.code h0 hr hR ht hc hP hI ho he hi hz'
    simpa only [woodinInverseSourceCode_twoStepColumn, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeπ_code, forcingMatrixNext_column hi] using hh
  · intro i hi p hp
    have hh := woodinNormalizationInverse_section_coherent hs.code h h0 hr hR ht hc hP hI ho he hi hp
    simpa only [woodinInverseSourceCode_twoStepColumn, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeE_code, forcingMatrixNext_column hi] using hh

/-- At an actual inverse branch, the construction supplies the raw forcing inputs. -/
theorem woodinNormalizationInverse_actual_family {Ω θ m : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) (h0 : ∅ ∈ θ)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (h : IsForcingNormalizationFamily θ (woodinIterationPrefix θ) m) :
    IsForcingNormalizationFamily (succ θ)
      (woodinInverseSourceCode θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ))
      (woodinNormalizationInverse θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) m) := by
  let := hΩ.inaccessible.1
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1)
  have hzero : θ ≠ ∅ := by
    intro he
    rw [he] at h0
    exact not_mem_empty h0
  have hf := woodinRawInverseSingular hΩ hθ hzero hlim hn
  have col := hs.code.system.inverseColumn h0 hs.code.subset_universe
  let τ : ForcingName (forcingInverseCodePoset θ (woodinIterationPrefix θ)) :=
    ⟨checkName (forcingInverseCodeTop θ (woodinIterationPrefix θ))
      (woodinLimitCardinal (woodinIterationCardinalPrefix θ)), checkName_isName col.tops.top.1 _⟩
  apply woodinNormalizationInverse_family hΩ hs h hθ h0 hlim
  · intro p hp
    apply forcingFormula_entailment singularLimitStageFormula
      (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_
      col.order.preorder col.tops.top hp ![τ] (hf p hp)
    intro W _ _ _ v hv
    have hh : IsLimitOfRegularCardinals (v 0) ∧ InternalDependentChoiceAt (v 0) :=
      (Defined.eval_iff _).mp hv
    change regularCardinalFormula.Evalb v ∨ limitOfRegularCardinalsFormula.Evalb v
    exact Or.inr ((Defined.eval_iff _).mpr hh.1)
  · intro p hp
    have hh := hf p hp
    rw [singularLimitStageFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.2

end ZFVP
