import ZFVP.ModelTheory.ForcingNormalizationThreadClosure
import ZFVP.ModelTheory.WoodinNormalizationInverseFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s K m : V}
local notation "P" => forcingInverseCodePoset θ s
local notation "R" => forcingInverseCodeOrder θ s
local notation "o" => forcingInverseCodeTop θ s
local notation "γ" => woodinLimitCardinal K
local notation "c" => forcingInverseSourceCutoff θ s γ
local notation "Q" => saturatedHartogsPosetName P R o γ c
local notation "S" => saturatedHartogsOrderName P R o γ c
local notation "r" => forcingNormalizationInverseMap θ s m
local notation "N" => forcingMapFixedPoints P r
local notation "T" => forcingOrderRestriction N R

theorem woodinNormalizationInverse_liftClosed [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (h : IsForcingNormalizationFamily θ s m)
    (hL : IsForcingNormalizationLiftClosed θ s m) (h0 : ∅ ∈ θ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o)
    (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) (hI : IsForcingIterand P R Q S ∅) :
    IsForcingNormalizationLiftClosed (succ θ) (woodinInverseSourceCode θ s K)
      (woodinNormalizationInverse θ s K m) := by
  obtain ⟨hr, ho, he⟩ := forcingNormalizationInverse_base hs h h0
  have hrnew := woodinNormalizationInverseMap_retraction hr hR ht hc hP hI ho he
  have hshape : forcingMapFixedPoints (twoStepConditions P R Q ∅)
      (woodinNormalizationInverseMap θ s K m) = normalizedNameTwoStep N T o c (nameAction r Q) := by
    simpa only [woodinInverseSourceCode_poset] using hrnew.fixedPoints_eq
  rw [woodinInverseSourceCode_twoStepColumn]
  unfold woodinNormalizationInverse forcingTwoStepColumnCode
  apply hL.extend
  intro i hi a ha b hb hle
  rw [hshape] at ha ⊢
  have haP : a ∈ twoStepConditions P R Q ∅ := by
    simpa only [woodinInverseSourceCode_poset] using hrnew.inclusion a ha
  have hbP := h.inclusion i hi b hb
  have col := hs.system.inverseColumn h0 hs.subset_universe
  have hm : (forcingLimitProjectionColumn θ P) ‘ i ∈ ((forcingCodeP s) ‘ i) ^ P :=
    col.functions.projection i hi
  rw [forcingComposeProjectionColumn_twoStep_value hi hm hR ht hI haP] at hle
  rw [forcingTwoStepLiftColumn_value hi haP hbP]
  obtain ⟨f, hf, τ, hτ, rfl⟩ := mem_prod_iff.mp ha
  have hfP : f ∈ P := (mem_sep_iff.mp hf).1
  simp only [kpair.π₁_kpair, forcingLimitProjectionColumn_value hi,
    forcingThreadCoordinate_value hfP] at hle
  have hf' : f ∈ forcingMapFixedPoints
      (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
      (forcingThreadActionMap θ m
        (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))) := by
    simpa only [forcingNormalizationInverseMap, forcingInverseCode, forcingThreadCode_poset,
      forcingInverseCodePoset] using hf
  have hl : forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) f i b ∈ N := by
    simpa only [forcingNormalizationInverseMap, forcingInverseCode, forcingThreadCode_poset,
      forcingInverseCodePoset] using hL.inverse_splice h hs hf' hi hb hle
  simpa only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair, kpair.π₂_kpair,
    forcingLimitLiftColumn_value hi, forcingLimitLift_value hfP hbP, normalizedNameTwoStep]
    using (kpair_mem_iff.mpr ⟨hl, hτ⟩ :
      ⟨forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) f i b, τ⟩ₖ ∈
        N ×ˢ normalizedNamePool N T o c (nameAction r Q))

theorem woodinNormalizationInverse_actual_liftClosed {Ω θ m : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) (h0 : ∅ ∈ θ)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (h : IsForcingNormalizationFamily θ (woodinIterationPrefix θ) m)
    (hL : IsForcingNormalizationLiftClosed θ (woodinIterationPrefix θ) m) :
    IsForcingNormalizationLiftClosed (succ θ)
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
  have hinputs := hs.normalizationInverse_inputs hΩ hθ h0 hlim ?_ ?_
  · exact woodinNormalizationInverse_liftClosed hs.code h hL h0
      hinputs.1 hinputs.2.1 hinputs.2.2.1 hinputs.2.2.2.1 hinputs.2.2.2.2
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
