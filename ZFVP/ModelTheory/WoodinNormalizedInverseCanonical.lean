import ZFVP.ModelTheory.NormalizedHartogsRetraction
import ZFVP.ModelTheory.RetractionNamedCutoff
import ZFVP.ModelTheory.WoodinNormalizedCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ s K m : V} [IsOrdinal θ]
local notation "P" => forcingInverseCodePoset θ s
local notation "R" => forcingInverseCodeOrder θ s
local notation "o" => forcingInverseCodeTop θ s
local notation "γ" => woodinLimitCardinal K
local notation "c" => forcingInverseSourceCutoff θ s γ
local notation "r" => forcingNormalizationInverseMap θ s m
local notation "N" => forcingMapFixedPoints P r
local notation "T" => forcingOrderRestriction N R
local notation "d" => woodinNamedPrefixCutoff N T o γ (hartogsNumberName N T (checkName o γ))
local notation "C" => forcingNormalizedCode (succ θ) (woodinInverseSourceCode θ s K)
  (woodinNormalizationInverse θ s K m)

theorem woodinNormalizedInverse_carrier_order
    (hΩ : IsWoodinSupercompact Ω) (hs : IsWoodinIteration Ω θ s K)
    (hm : IsForcingNormalizationFamily θ s m) (hθ : θ ∈ Ω) (h0 : ∅ ∈ θ)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hγ : ∀ p ∈ P, p ∈ forcingFormula P R (regularCardinalFormula.or limitOfRegularCardinalsFormula)
      (standardTuple ![checkName o γ]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName o γ])) :
    (forcingCodeP C) ‘ θ = normalizedNameTwoStep N T o d (saturatedHartogsPosetName N T o γ d) ∧
      (forcingCodeR C) ‘ θ = nameTwoStepOrderOn N T (saturatedHartogsOrderName N T o γ d)
        (normalizedNameTwoStep N T o d (saturatedHartogsPosetName N T o γ d)) := by
  obtain ⟨hR, ht, hc, hP, hI⟩ := hs.normalizationInverse_inputs hΩ hθ h0 hlim hγ hDC
  obtain ⟨hr, ho, he⟩ := forcingNormalizationInverse_base hs.code hm h0
  have hT := forcingOrderRestriction_preorder hR hr.inclusion
  have hone : o ∈ N := mem_sep_iff.mpr ⟨ht.1, ho⟩
  have hγc := (hs.inverse_sourceCutoff hΩ hθ h0 hγ hDC).2.1
  have hd : c = d := by
    simpa only [forcingInverseSourceCutoff, forcingInverseHartogsName] using
      hr.hartogs_prefix_cutoff hR hT he ht hone γ
  rw [← hd]
  have hrnew := woodinNormalizationInverseMap_retraction hr hR ht hc hP hI ho he
  have hI' := hr.iterand_nameAction hR hT he hI
  have hpre := normalizedNameTwoStep_preorder (δ := c) hT (hr.top_of_mem ht hone)
    hI'.posetName hI'.orderName hI'.preorder
  rw [hr.normalized_hartogs_order hR hT he ht hone hc hP hγc,
    hr.normalized_hartogs_carrier hR hT he ht hone hc hP hγc] at hrnew hpre
  simp only [forcingNormalizedCode, forcingCodeP_code, forcingCodeR_code,
    forcingNormalizationOrders_value (mem_succ_self θ), forcingNormalizationCarriers_value (mem_succ_self θ),
    woodinNormalizationInverse_new]
  constructor
  · exact hrnew.fixedPoints_eq
  · rw [hrnew.fixedPoints_eq]
    exact hrnew.orderRestriction_eq hpre

theorem woodinNormalizationHistory_inverse
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinNormalizationHistory (succ θ) = woodinNormalizationInverse θ (woodinIterationPrefix θ)
      (woodinIterationCardinalPrefix θ) (woodinNormalizationHistory θ) := by
  rw [woodinNormalizationHistory_next, woodinNormalizationRec_rule]
  simp only [woodinNormalizationRule, ite_eq_right h0, ite_eq_right hlim, ite_eq_right hn,
    woodinNormalizationInverse]

theorem woodinNormalizedStage_inverse_carrier_order
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let s := woodinIterationPrefix θ
    let K := woodinIterationCardinalPrefix θ
    let m := woodinNormalizationHistory θ
    let base := forcingMapFixedPoints (forcingInverseCodePoset θ s) (forcingNormalizationInverseMap θ s m)
    let rel := forcingOrderRestriction base (forcingInverseCodeOrder θ s)
    let one := forcingInverseCodeTop θ s
    let card := woodinLimitCardinal K
    let cut := woodinNamedPrefixCutoff base rel one card (hartogsNumberName base rel (checkName one card))
    let iter := saturatedHartogsPosetName base rel one card cut
    let ord := saturatedHartogsOrderName base rel one card cut
    (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ = normalizedNameTwoStep base rel one cut iter ∧
      (forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ =
        nameTwoStepOrderOn base rel ord (normalizedNameTwoStep base rel one cut iter) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hsub i hi)).1)
  have hm := woodinNormalizationHistory_actual_prefix hΩ hAC hsub
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hlimit := ordinal_limit_of_not_successor hlim
  have hf := woodinRawInverseSingular hΩ hθ h0 hlimit hn
  have col := hs.code.system.inverseColumn hz hs.code.subset_universe
  let τ : ForcingName (forcingInverseCodePoset θ (woodinIterationPrefix θ)) :=
    ⟨checkName (forcingInverseCodeTop θ (woodinIterationPrefix θ))
      (woodinLimitCardinal (woodinIterationCardinalPrefix θ)), checkName_isName col.tops.top.1 _⟩
  have hγ : ∀ p ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      p ∈ forcingFormula (forcingInverseCodePoset θ (woodinIterationPrefix θ))
        (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
        (regularCardinalFormula.or limitOfRegularCardinalsFormula) (standardTuple ![τ.val]) := by
    intro p hp
    apply forcingFormula_entailment singularLimitStageFormula
      (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_
      col.order.preorder col.tops.top hp ![τ] (hf p hp)
    intro W _ _ _ v hv
    have hh : IsLimitOfRegularCardinals (v 0) ∧ InternalDependentChoiceAt (v 0) := (Defined.eval_iff _).mp hv
    change regularCardinalFormula.Evalb v ∨ limitOfRegularCardinalsFormula.Evalb v
    exact Or.inr ((Defined.eval_iff _).mpr hh.1)
  have hDC : ∀ p ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      p ∈ forcingFormula (forcingInverseCodePoset θ (woodinIterationPrefix θ))
        (forcingInverseCodeOrder θ (woodinIterationPrefix θ)) dependentChoiceAtFormula (standardTuple ![τ.val]) := by
    intro p hp
    have hh := hf p hp
    rw [singularLimitStageFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.2
  have hh := woodinNormalizedInverse_carrier_order hΩ hs hm hθ hz hlimit hγ hDC
  simpa only [woodinNormalizedStageCode, woodinIterationRec_inverse h0 hlim hn, kpair.π₁_kpair,
    woodinNormalizationHistory_inverse h0 hlim hn] using hh

end ZFVP
