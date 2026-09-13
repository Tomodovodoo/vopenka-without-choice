import ZFVP.ModelTheory.WoodinRawHistorySelectedBound
import ZFVP.ModelTheory.WoodinEarlierRawPreservation
import ZFVP.ModelTheory.WoodinEarlierRawSmall
import ZFVP.ModelTheory.WoodinBoundSuccessorStep

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 1000000 in
theorem woodinQuotientBoundAt_inverse_normalized [Countable V] {δ θ i j p α : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (hi : i ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hclosure : HasWoodinQuotientClosure (succ j) (kpair.π₁ (woodinIterationRec j))
      (kpair.π₂ (woodinIterationRec j)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (hprev : ∀ k ∈ j, IsWoodinNormalizedQuotientBoundAt θ i p f.val α k) :
    IsWoodinNormalizedQuotientBoundAt θ i p f.val α j := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hj
  have hij : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hi
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have h0j : (∅ : V) ∈ j := (IsOrdinal.subset_iff.mp (empty_subset j)).resolve_left (fun he ↦ h0 he.symm)
  let s := woodinIterationPrefix j
  let K := woodinIterationCardinalPrefix j
  let γ := woodinLimitCardinal K
  let c := forcingInverseSourceCutoff j s γ
  let T := forcingInverseCodePoset j s
  let U := forcingInverseCodeOrder j s
  let o := forcingInverseCodeTop j s
  let η := K ‘ i
  let τ := forcingThreadCoordinate T i
  let E := forcingThreadSection j (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) i
  let π := (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ
  let Q : ForcingName T := ⟨woodinCollapseName T U (forcingInverseHartogsName j s γ)
    (forcingInverseRestorationName j s γ), woodinCollapseName_isName _ _ _ _⟩
  let Qs := forcingInverseCollapseName j s c (forcingInverseHartogsName j s γ)
    (forcingInverseRestorationName j s γ)
  let S := reverseInclusionOrderName T U Qs
  let q := woodinQuotientBoundHistory θ i p f.val j
  let μ : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    ⟨woodinBoundCoordinateName θ i f.val j, woodinBoundCoordinateName_isName _ _ _ _⟩
  have hssub := fun k hk ↦ hs k (hsub k hk)
  have h := woodinIterationPrefix_of_stages hssub
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have col := h.code.system.inverseColumn h0j h.code.subset_universe
  have hU : IsForcingPreorder T U := col.order.preorder
  have hot : IsForcingTop T U o := col.tops.top
  obtain ⟨hγc, hci, hT⟩ := woodinEarlierRaw_cutoff_data hs hj h0 hlim hinac
  let := hci.1
  let := h.limitCardinal_ordinal
  let : IsOrdinal η := (h.inaccessible i hi).1
  have hκforce := woodinEarlierRaw_hartogs_regular hs hj h0 hlim hinac hclosure
  have hiter := woodinInverse_iterand_of_stages hs hj h0 hlim hinac
  have hPi := woodinIterationPrefix_poset_value hssub hi (mem_succ_self i)
  have hRi := woodinIterationPrefix_order_value hssub hi (mem_succ_self i)
  have hoi := woodinIterationPrefix_top_value hssub hi (mem_succ_self i)
  have hbaseR := (hs i hiθ).code.system.order.preorder i (mem_succ_self i)
  have hbaseo := (hs i hiθ).code.system.tops.top i (mem_succ_self i)
  have hsplit := woodinInverseCoordinate_split hssub hi
  rw [hPi, hRi] at hsplit
  have hrec := woodinIterationRec_inverse h0 hlim hinac
  have hPnext : (forcingCodeP (woodinIterationPrefix θ)) ‘ j = twoStepConditions T U Qs ∅ := by
    rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
      forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingFamilyNext_new, T, U, Qs, c, γ, s, K, forcingInverseCodePoset, forcingInverseCodeOrder]
  have hRnext : (forcingCodeR (woodinIterationPrefix θ)) ‘ j = twoStepOrder T U Qs S ∅ := by
    rw [woodinIterationPrefix_order_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
      forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeR_code, forcingFamilyNext_new, T, U, Qs, S, c, γ, s, K, forcingInverseCodePoset, forcingInverseCodeOrder]
  have hπfull := hcθ.system.projection hiθ hj hij
  rw [woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i),
    woodinIterationPrefix_order_value hs hiθ (mem_succ_self i), hPnext, hRnext] at hπfull
  have hcomp : ∀ z ∈ twoStepConditions T U Qs ∅, τ ‘ (kpair.π₁ z) = π ‘ z := by
    intro z hz
    have hz' := hPnext.symm ▸ hz
    have hm := woodinInverse_first_mem hs hj h0 hlim hinac hz'
    rw [forcingThreadCoordinate_value hm]
    exact (woodinInverse_projection_value hs hj h0 hlim hinac hi hz').symm
  have hmem : ∀ k ∈ j, woodinQuotientBoundRec θ i p f.val k ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ k :=
    fun k hk ↦ (hprev k hk).1.1
  have hmemlocal : ∀ k ∈ j, woodinQuotientBoundRec θ i p f.val k ∈ (forcingCodeP s) ‘ k := by
    intro k hk
    rw [h.code.tableP.value_of_subset hcθ.tableP (woodinIterationPrefix_extends hsub).subP hk]
    exact hmem k hk
  have hqdata := woodinQuotientBoundHistory_inverse_condition (ξ := θ) hssub hi hmemlocal
  have hq : q ∈ T := hqdata.1
  have hqb : τ ‘ q = p := hqdata.2
  have hqp : ⟨q, E ‘ p⟩ₖ ∈ U := (hsplit.below q hq p hp).mpr (hqb.symm ▸ hbaseR.2.1 p hp)
  have hηi : η = (kpair.π₂ (woodinIterationRec i)) ‘ i := by
    have hh := woodinIterationHistory_of_stages hssub
    simpa only [η, K, woodinIterationCardinalPrefix, woodinIterationHistory_cardinal_value hi] using
      hh.cardinal_union_value hi (mem_succ_self i)
  have hαη : α ∈ η := hηi.symm ▸ hα
  have hαγ : α ∈ γ := h.cardinal_subset_limit hi α hαη
  have hcl := woodinEarlierRaw_quotient_closedBelow hs hj hi hlim hinac hclosure
  dsimp only at hcl
  rw [hPi, hRi, hoi] at hcl
  have hDCforce : ∀ r ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
      r ∈ forcingFormula ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) dependentChoiceBelowFormula
        (standardTuple ![checkName ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) η]) := by
    have hh := (h.stage i hi).2.2.2.2
    simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code, s, hPi, hRi, hoi, η] using hh
  have hdata (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) (hpG : p ∈ G) :
      let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
      IsForcingDescending (A.projectionQuotient (twoStepConditions T U Qs ∅) π)
        (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Qs ∅) π)
          (A.projectionQuotientOrder (twoStepConditions T U Qs ∅) (twoStepOrder T U Qs S ∅) π))
        (A.check α) (A.ofName μ) ∧
      (∀ a ∈ A.check α, ⟨A.check q, (compose (A.ofName μ) (A.check (twoStepProjection T U Qs ∅))) ‘ a⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) ∧
      InternalDependentChoiceAt (A.check α) ∧
      IsForcingClosedThrough (A.projectionQuotient T τ)
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) (A.check α) := by
    let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
    have hd := woodinQuotientSequence_semantics hs hiθ f hf G hG hpG
    have hfun := mem_function_of_mem_function_of_subset hd.1 sep_subset
    have hnext := A.woodinCoordinate_descending hs hiθ hj hij rfl rfl rfl f hd
    rw [hPnext, hRnext] at hnext
    have hDCs : ∀ β ∈ A.check η, InternalDependentChoiceAt β :=
      (Defined.eval_iff _).mp ((A.checked_unary_truth dependentChoiceBelowFormula η).mpr
        ⟨p, hpG, hDCforce p hp⟩)
    have hclosed := A.projectionQuotient_closedBelow_of_forced hsplit.projection hU hcl
    refine ⟨hnext, ?_, hDCs _ ((A.check_mem_iff _ _).mpr hαη), ?_⟩
    · intro a ha
      obtain ⟨d, hdD, had⟩ := (A.mem_check_iff _ _).mp (function_value_mem hfun ha)
      have hv := A.woodinCoordinate_value hs hj rfl rfl rfl f hfun ha hdD had
      have hdj := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hdD).2.1 j hj
      rw [hPnext] at hdj
      have hν := mem_function_of_mem_function_of_subset hnext.1 sep_subset
      have hρ := twoStepProjection_maps T U Qs ∅
      let := IsFunction.of_mem hρ
      rw [value_compose_of_mem_function hν ((A.check_function_iff _ _ _).mpr hρ) ha,
        hv, A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hdj), twoStepProjection_value hdj]
      have hπorig := (woodinInverseCoordinate_split hs hiθ).projection.maps
      rw [woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)] at hπorig
      have hdQ := function_value_mem hd.1 ha
      rw [had] at hdQ
      have hdG := ((A.check_mem_projectionQuotient_iff hπorig).mp hdQ).2
      rw [forcingThreadCoordinate_value hdD] at hdG
      have ht := woodinThread_inverse_coordinate hs hj h0 hlim hinac hdD
      exact A.woodinRawHistory_le_selected hs hsub hi rfl rfl rfl f hpG hdD hdG hfun ha had
        ht.1 (fun k hk ↦ (ht.2 k hk).symm) hmem (fun k hk ↦ (hprev k hk).2)
    · intro β hβ hβα
      exact hclosed β (ordinal_mem_of_subset_mem hβα ((A.check_mem_iff _ _).mpr hαη))
  have hcollapse (H : Set V) (hH : IsExternalForcingGeneric T U H) :
      let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
      ∃ κ : C.Model, IsRegularCardinal κ ∧ κ ⊆ C.check c ∧ C.check α ∈ κ ∧
        C.ofName ⟨Qs, hiter.posetName⟩ = woodinCollapse κ (C.check c) ∧
        C.ofName ⟨S, hiter.orderName⟩ = woodinCollapseOrder κ (C.check c) := by
    let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
    obtain ⟨r, hr⟩ := hH.1.2.1
    let ν : ForcingName T := ⟨checkName o γ, checkName_isName hot.1 _⟩
    have hv : C.ofName (C.hartogsName ν) = hartogsNumber (C.check γ) := C.hartogsName_value ν
    have hreg : IsRegularCardinal (hartogsNumber (C.check γ)) := by
      rw [← hv]
      exact (Defined.eval_iff _).mp ((C.formula_truth regularCardinalFormula ![C.hartogsName ν]).mpr
        ⟨r, hr, hκforce r (hH.1.1 r hr)⟩)
    refine ⟨hartogsNumber (C.check γ), hreg,
      IsOrdinal.toIsTransitive.transitive _ (C.hartogs_checked_mem hci hT hγc), ?_,
      C.saturatedHartogsCollapseName_value hci hT hγc,
      C.saturatedHartogsCollapseOrderName_value hci hT hγc⟩
    exact ordinal_cardLE_iff_mem_hartogsNumber.mp (cardLE_of_subset
      (IsOrdinal.toIsTransitive.transitive _ ((C.check_mem_iff _ _).mpr hαγ)))
  let ν := forcingLocalCanonicalName T U o c (E ‘ p)
    (forcingSelectedUnion T U o (twoStepNames Qs ∅) (twoStepTailSelector T U Qs ∅) (nameAction E μ.val))
  have hpair : ⟨q, ν⟩ₖ ∈ twoStepConditions T U Qs ∅ :=
    transported_local_union_pair_mem hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
      hπfull.maps hcomp hdata (fun H hH _ ↦ hcollapse H hH)
  have hqnext : woodinQuotientBoundRec θ i p f.val j = ⟨q, ν⟩ₖ := by
    rw [woodinQuotientBoundRec_inverse hi hlim hinac]
    unfold woodinBoundInverseTail woodinBoundTailName
    dsimp only
    simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
    rfl
  have hnorm : q ∈ atomicEquality T U ν
      (forcingSelectedUnion T U o (twoStepNames Qs ∅) (twoStepTailSelector T U Qs ∅) (nameAction E μ.val)) :=
    transported_local_union_normalization hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
      hπfull.maps hcomp hdata (fun H hH _ ↦ hcollapse H hH)
  refine ⟨?_, ?_⟩
  · apply (woodinQuotientBoundAt_iff_generics hs hiθ hj hij hp f).mpr
    refine ⟨?_, ?_⟩
    · rw [hqnext, hPnext]
      exact hpair
    · intro G hG hpG
      let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
      obtain ⟨hdesc, hbound, hDC, hclosed⟩ := hdata G hG hpG
      have hπpair : π ‘ ⟨q, ν⟩ₖ = p := by
        rw [← hcomp _ hpair, kpair.π₁_kpair, hqb]
      have hpQ : A.check ⟨q, ν⟩ₖ ∈ A.projectionQuotient (twoStepConditions T U Qs ∅) π :=
        (A.check_mem_projectionQuotient_iff hπfull.maps).mpr ⟨hpair, hπpair.symm ▸ hpG⟩
      dsimp only
      rw [hqnext, hPnext, hRnext]
      refine ⟨hpQ, ?_⟩
      apply A.local_union_quotient_separative_bound hsplit hU hot hiter hπfull.maps hcomp μ hdesc hbound
        hci hT (function_value_mem hsplit.maps hp) hqp hDC hclosed ?_ hpQ
      intro H hH hA
      obtain ⟨κ, hκ, hκc, hακ, hQ, hS⟩ := hcollapse H hH
      refine ⟨κ, hκ, hκc, ?_, hQ, hS⟩
      rwa [A.projectionInclusion_check _ hsplit hA α]
  · intro _
    constructor
    · intro hsucc
      exact (hlim hsucc).elim
    · intro _ _
      unfold woodinBoundInverseTail woodinBoundTailName woodinBoundInverseRawTail
      dsimp only
      simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
      exact hnorm

end ZFVP
