import ZFVP.ModelTheory.WoodinBoundInvariantSemantics
import ZFVP.ModelTheory.WoodinBoundCoherence
import ZFVP.ModelTheory.WoodinSuccessorCoordinates
import ZFVP.ModelTheory.TransportedLocalUnionPair
import ZFVP.ModelTheory.LocalUnionQuotientBound
import ZFVP.ModelTheory.WoodinBoundNormalization
import ZFVP.ModelTheory.TransportedLocalUnionNormalization

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 1000000 in
theorem woodinQuotientBoundAt_successor_normalized [Countable V] {δ θ i k p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hk : succ k ∈ θ) (hi : i ∈ succ k)
    (hclosure : HasWoodinQuotientClosure (succ k) (woodinIterationPrefix (succ k))
      (woodinIterationCardinalPrefix (succ k)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (hprev : ∀ l ∈ succ k, IsWoodinQuotientBoundAt θ i p f.val α l) :
    IsWoodinNormalizedQuotientBoundAt θ i p f.val α (succ k) := by
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem (mem_succ_self k)
  let := IsOrdinal.of_mem hi
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hk
  have hkθ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hik : i ⊆ k := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)
  have hssub := fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hk)
  have hhist := woodinIterationHistory_of_stages hssub
  have he := woodinIterationPrefix_successor hhist
  let s := woodinIterationPrefix (succ k)
  let K := woodinIterationCardinalPrefix (succ k)
  let T := (forcingCodeP s) ‘ k
  let U := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := K ‘ k
  let η := K ‘ i
  let c := woodinPrefixCutoff T U o κ
  let τ := (forcingCodeπ s) ‘ ⟨i, k⟩ₖ
  let E := (forcingCodeE s) ‘ ⟨i, k⟩ₖ
  let π := (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, succ k⟩ₖ
  let q := woodinQuotientBoundRec θ i p f.val k
  have h : IsWoodinIteration δ (succ k) s K := woodinIterationPrefix_of_stages hssub
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have hnewstage : IsWoodinIteration δ (succ (succ k)) (woodinIterationSuccessor k s K)
      (woodinIterationCardinalNext k s K) := by
    have hh := hs (succ k) hk
    rw [woodinIterationRec_successor_of_history hhist, kpair.π₁_kpair, kpair.π₂_kpair] at hh
    simpa only [s, K, he.1, he.2] using hh
  have hnew : (woodinIterationCardinalNext k s K) ‘ (succ k) = c := by
    simp only [c, T, U, o, κ, woodinIterationCardinalNext, forcingFamilyNext_new, woodinSuccessorStep,
      woodinSuccessorAt, woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code]
  have hci : IsChoicelessInaccessible c := hnew ▸ hnewstage.inaccessible (succ k) (mem_succ_self _)
  let := hci.1
  have hold : (woodinIterationCardinalNext k s K) ‘ k = K ‘ k := forcingFamilyNext_old (mem_succ_self k)
  have hκc : κ ∈ c := by
    simpa only [hnew, hold, κ] using hnewstage.increasing k
      (mem_succ_iff.mpr (Or.inr (mem_succ_self k))) (succ k) (mem_succ_self _) (mem_succ_self k)
  have hT : T ∈ hierarchy c := by
    have hh := h.small k (mem_succ_self k) c hci
    simp only [woodinIterationStage, woodinStageCardinal_code, woodinStagePoset_code] at hh
    exact hh hκc
  have hκforce : ∀ r ∈ T, r ∈ forcingFormula T U regularCardinalFormula (standardTuple ![checkName o κ]) := by
    simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code] using (h.stage k (mem_succ_self k)).2.2.2.1
  have hU := h.code.system.order.preorder k (mem_succ_self k)
  have hot := h.code.system.tops.top k (mem_succ_self k)
  have hκsub : κ ⊆ c := IsOrdinal.toIsTransitive.transitive _ hκc
  have hiter := saturatedWoodinPrefix_iterand hU hot hci hT hκsub hκforce
  let Qs := saturatedWoodinPrefixPosetName T U o κ c
  let S := saturatedWoodinPrefixOrderName T U o κ c
  let Q : ForcingName T := ⟨woodinPrefixPosetName T U o κ c, woodinCollapseName_isName _ _ _ _⟩
  let μ : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    ⟨woodinBoundCoordinateName θ i f.val (succ k), woodinBoundCoordinateName_isName _ _ _ _⟩
  have hPi := woodinIterationPrefix_poset_value hssub hi (mem_succ_self i)
  have hRi := woodinIterationPrefix_order_value hssub hi (mem_succ_self i)
  have hoi := woodinIterationPrefix_top_value hssub hi (mem_succ_self i)
  have hbaseR := (hs i hiθ).code.system.order.preorder i (mem_succ_self i)
  have hbaseo := (hs i hiθ).code.system.tops.top i (mem_succ_self i)
  have hsplit := h.code.system.splitProjection hi (mem_succ_self k) hik
  rw [hPi, hRi] at hsplit
  have hPk : (forcingCodeP (woodinIterationPrefix θ)) ‘ k = T := by
    simpa only [T, s, he.1] using woodinIterationPrefix_poset_value hs hkθ (mem_succ_self k)
  have hRk : (forcingCodeR (woodinIterationPrefix θ)) ‘ k = U := by
    simpa only [U, s, he.1] using woodinIterationPrefix_order_value hs hkθ (mem_succ_self k)
  have hτeq : (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, k⟩ₖ = τ := by
    simpa only [τ, s, he.1] using woodinIterationPrefix_projection_value hs hkθ hi (mem_succ_self k)
  have hPnext : (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k) = twoStepConditions T U Qs ∅ := by
    rw [woodinIterationPrefix_poset_value hs hk (mem_succ_self _),
      woodinIterationRec_successor_of_history hhist, kpair.π₁_kpair]
    simp only [woodinIterationSuccessor, forcingSuccessorCode_poset, Qs, c, T, U, o, κ, s, K, he.1, he.2]
  have hRnext : (forcingCodeR (woodinIterationPrefix θ)) ‘ (succ k) = twoStepOrder T U Qs S ∅ := by
    rw [woodinIterationPrefix_order_value hs hk (mem_succ_self _),
      woodinIterationRec_successor_of_history hhist, kpair.π₁_kpair]
    simp only [woodinIterationSuccessor, forcingSuccessorCode_order, Qs, S, c, T, U, o, κ, s, K, he.1, he.2]
  have hπfull := hcθ.system.projection hiθ hk (IsOrdinal.toIsTransitive.transitive _ hi)
  rw [woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i),
    woodinIterationPrefix_order_value hs hiθ (mem_succ_self i), hPnext, hRnext] at hπfull
  have hcomp : ∀ z ∈ twoStepConditions T U Qs ∅, τ ‘ (kpair.π₁ z) = π ‘ z := by
    intro z hz
    rw [← hτeq]
    exact woodinSuccessor_projection_comp hs hk hi (hPnext.symm ▸ hz)
  have hmemlocal : ∀ l ∈ succ k, woodinQuotientBoundRec θ i p f.val l ∈ (forcingCodeP s) ‘ l := by
    intro l hl
    rw [h.code.tableP.value_of_subset hcθ.tableP
      (woodinIterationPrefix_extends (IsOrdinal.toIsTransitive.transitive _ hk)).subP hl]
    exact (hprev l hl).1
  have hq : q ∈ T := hmemlocal k (mem_succ_self k)
  have hqb : τ ‘ q = p := by
    rw [woodinQuotientBoundRec_projects_of_membership hssub hi hmemlocal k (mem_succ_self k) i hi,
      woodinQuotientBoundRec_base]
  have hqp : ⟨q, E ‘ p⟩ₖ ∈ U := (hsplit.below q hq p hp).mpr (hqb.symm ▸ hbaseR.2.1 p hp)
  have hηi : η = (kpair.π₂ (woodinIterationRec i)) ‘ i := by
    simpa only [η, K, woodinIterationCardinalPrefix, woodinIterationHistory_cardinal_value hi] using
      hhist.cardinal_union_value hi (mem_succ_self i)
  have hαη : α ∈ η := hηi.symm ▸ hα
  let := (h.inaccessible k (mem_succ_self k)).1
  let : IsOrdinal η := (h.inaccessible i hi).1
  have hηκ : η ⊆ κ := by
    rcases mem_succ_iff.mp hi with rfl | hi'
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ (h.increasing i hi k (mem_succ_self k) hi')
  have hακ : α ∈ κ := hηκ α hαη
  have hcl := hclosure i hi k (mem_succ_self k) hik
  change ForcesProjectionQuotientClosedBelow ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
    ((forcingCodet s) ‘ i) T U τ η at hcl
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
    have hnext := A.woodinCoordinate_descending hs hiθ hk (IsOrdinal.toIsTransitive.transitive _ hi)
      rfl rfl rfl f hd
    rw [hPnext, hRnext] at hnext
    have hbprev := ((woodinQuotientBoundAt_iff_generics hs hiθ hkθ hik hp f).mp (hprev k (mem_succ_self k))).2 G hG hpG
    have hDCs : ∀ β ∈ A.check η, InternalDependentChoiceAt β :=
      (Defined.eval_iff _).mp ((A.checked_unary_truth dependentChoiceBelowFormula η).mpr
        ⟨p, hpG, hDCforce p hp⟩)
    have hclosed := A.projectionQuotient_closedBelow_of_forced hsplit.projection hU hcl
    refine ⟨hnext, ?_, hDCs _ ((A.check_mem_iff _ _).mpr hαη), ?_⟩
    · intro a ha
      obtain ⟨d, hdD, had⟩ := (A.mem_check_iff _ _).mp (function_value_mem hfun ha)
      have hv := A.woodinCoordinate_value hs hk rfl rfl rfl f hfun ha hdD had
      have hdk := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hdD).2.1 (succ k) hk
      rw [hPnext] at hdk
      have hν := mem_function_of_mem_function_of_subset hnext.1 sep_subset
      have hρ := twoStepProjection_maps T U Qs ∅
      let := IsFunction.of_mem hρ
      rw [value_compose_of_mem_function hν ((A.check_function_iff _ _ _).mpr hρ) ha,
        hv, A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hdk), twoStepProjection_value hdk,
        woodinInverseThread_successor_first hs hk hdD]
      have hbval := hbprev.2 a ha
      rw [A.woodinCoordinate_value hs hkθ rfl rfl rfl f hfun ha hdD had, hPk, hRk, hτeq] at hbval
      exact hbval
    · intro β hβ hβα
      exact hclosed β (ordinal_mem_of_subset_mem hβα ((A.check_mem_iff _ _).mpr hαη))
  have hcollapse (H : Set V) (hH : IsExternalForcingGeneric T U H) :
      let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
      ∃ γ : C.Model, IsRegularCardinal γ ∧ γ ⊆ C.check c ∧ C.check α ∈ γ ∧
        C.ofName ⟨Qs, hiter.posetName⟩ = woodinCollapse γ (C.check c) ∧
        C.ofName ⟨S, hiter.orderName⟩ = woodinCollapseOrder γ (C.check c) := by
    let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
    obtain ⟨r, hr⟩ := hH.1.2.1
    have hreg : IsRegularCardinal (C.check κ) :=
      (Defined.eval_iff _).mp ((C.checked_unary_truth regularCardinalFormula κ).mpr
        ⟨r, hr, hκforce r (hH.1.1 r hr)⟩)
    exact ⟨C.check κ, hreg, (C.checkEmbedding.subset_iff _ _).mpr hκsub,
      (C.check_mem_iff _ _).mpr hακ, C.saturatedWoodinPosetName_value hci hT hκsub,
      C.saturatedWoodinOrderName_value hci hT hκsub⟩
  let ν := forcingLocalCanonicalName T U o c (E ‘ p)
    (forcingSelectedUnion T U o (twoStepNames Qs ∅) (twoStepTailSelector T U Qs ∅) (nameAction E μ.val))
  have hpair : ⟨q, ν⟩ₖ ∈ twoStepConditions T U Qs ∅ :=
    transported_local_union_pair_mem hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
      hπfull.maps hcomp hdata (fun H hH _ ↦ hcollapse H hH)
  have hqnext : woodinQuotientBoundRec θ i p f.val (succ k) = ⟨q, ν⟩ₖ := by
    rw [woodinQuotientBoundRec_successor hi]
    unfold woodinBoundSuccessorTail woodinBoundTailName
    dsimp only
    simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
    rfl
  have hnorm : q ∈ atomicEquality T U ν
      (forcingSelectedUnion T U o (twoStepNames Qs ∅) (twoStepTailSelector T U Qs ∅) (nameAction E μ.val)) :=
    transported_local_union_normalization hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
      hπfull.maps hcomp hdata (fun H hH _ ↦ hcollapse H hH)
  refine ⟨?_, ?_⟩
  · apply (woodinQuotientBoundAt_iff_generics hs hiθ hk (IsOrdinal.toIsTransitive.transitive _ hi) hp f).mpr
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
      obtain ⟨γ, hγ, hγc, hαγ, hQ, hS⟩ := hcollapse H hH
      refine ⟨γ, hγ, hγc, ?_, hQ, hS⟩
      rwa [A.projectionInclusion_check _ hsplit hA α]
  
  · intro _
    constructor
    · intro _
      simp only [sUnion_succ_of_transitive]
      unfold woodinBoundSuccessorTail woodinBoundTailName woodinBoundSuccessorRawTail
      dsimp only
      simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
      exact hnorm
    · intro hnot
      exact False.elim (hnot (by rw [sUnion_succ_of_transitive]))

set_option maxHeartbeats 1000000 in
theorem woodinQuotientBoundAt_successor [Countable V] {δ θ i k p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hk : succ k ∈ θ) (hi : i ∈ succ k)
    (hclosure : HasWoodinQuotientClosure (succ k) (woodinIterationPrefix (succ k))
      (woodinIterationCardinalPrefix (succ k)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (hprev : ∀ l ∈ succ k, IsWoodinQuotientBoundAt θ i p f.val α l) :
    IsWoodinQuotientBoundAt θ i p f.val α (succ k) :=
  (woodinQuotientBoundAt_successor_normalized hs hk hi hclosure hα hp f hf hprev).1

end ZFVP
