import ZFVP.ModelTheory.WoodinBoundInvariantSemantics
import ZFVP.ModelTheory.WoodinBoundCoherence
import ZFVP.ModelTheory.WoodinCanonicalBoundInverseIterand
import ZFVP.ModelTheory.WoodinCanonicalBoundInverseClosure
import ZFVP.ModelTheory.WoodinCanonicalBoundInverseClosureDecided
import ZFVP.ModelTheory.WoodinQuotientClosureInverse
import ZFVP.ModelTheory.QuotientLiftCompatibility
import ZFVP.ModelTheory.SaturatedHartogsCollapse
import ZFVP.ModelTheory.TransportedLocalUnionPair
import ZFVP.ModelTheory.LocalUnionQuotientBound
import ZFVP.ModelTheory.WoodinBoundNormalization
import ZFVP.ModelTheory.TransportedLocalUnionNormalization

/-! The inverse-limit step of the canonical quotient-bound induction with a raw comparison
premise that carries the decision property.

`woodinQuotientBoundAt_inverse_normalized_of_raw` asks for the raw thread comparison with `d ‘ i` as the
base condition. That premise cannot be discharged: the raw comparison lemmas need a base condition
that decides the selected value of the canonical coordinate name, and `d ‘ i` does not. Here the
comparison premise takes an arbitrary condition `e` below `d ‘ i` together with the two decision
properties, and the proof gets `e` from the generic filter through
`woodinBound_decision_for_selected_thread`. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 1000000 in
theorem woodinQuotientBoundAt_inverse_normalized_decided [Countable V] {δ θ i j p α : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hj : j ∈ θ) (hij : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hclosure : ∀ k ∈ j, IterationQuotientClosedBelow
      (forcingInverseCode j (woodinIterationPrefix j)) k j ((woodinIterationCardinalPrefix j) ‘ k))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (hprev : ∀ k ∈ j, IsWoodinQuotientBoundAt θ i p f.val α k)
    (hraw : ∀ d ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      ∀ e ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
        ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
        (∀ m ∈ j, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
            ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G')
          (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
          (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
            ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G' →
          let A : ForcingContext V := ⟨_, _, _, G', hR, ho, hG'⟩
          let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val m,
            woodinBoundCoordinateName_isName θ i f.val m⟩
          ∃ X b : A.Model,
            A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ m) ^ X ∧
              b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ m)) →
        (∀ m ∈ j, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
            ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) G'), e ∈ G' →
          ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
              ((forcingCodeR (woodinIterationPrefix θ)) ‘ i))
            (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
              ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
              ((forcingCodet (woodinIterationPrefix θ)) ‘ i))
            (μ : ForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)),
            μ.val = woodinBoundCoordinateName θ i f.val m →
            let A : ForcingContext V := ⟨_, _, _, G', hRi, hti, hG'⟩
            ∃ X b : A.Model, A.ofName μ ∈
                A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ m) ^ X ∧
              b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ m)) →
        ∀ r ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
          ⟨r, woodinQuotientBoundHistory θ i p f.val j⟩ₖ ∈
            forcingInverseCodeOrder j (woodinIterationPrefix j) →
          ∀ b ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
            ⟨b, (forcingThreadCoordinate
              (forcingInverseCodePoset j (woodinIterationPrefix j)) i) ‘ r⟩ₖ ∈
              (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
            ⟨b, e⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
            ⟨(woodinInverseCodeLift j (woodinIterationPrefix j) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ ∈
              forcingInverseCodeOrder j (woodinIterationPrefix j)) :
    IsWoodinNormalizedQuotientBoundAt θ i p f.val α j := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hiθ : i ∈ θ := IsOrdinal.toIsTransitive.mem_trans hij hj
  have hijs : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hij
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hij
  have h0j : (∅ : V) ∈ j := empty_mem_of_ordinal_ne_empty h0
  have hsucclim : ∀ k ∈ j, succ k ∈ j := ordinal_limit_of_not_successor hlim
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hsj : ∀ l ∈ j, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)) := fun l hl ↦ hs l (hsub l hl)
  let s := woodinIterationPrefix j
  let K := woodinIterationCardinalPrefix j
  let γ := woodinLimitCardinal K
  let T := forcingInverseCodePoset j s
  let U := forcingInverseCodeOrder j s
  let o := forcingInverseCodeTop j s
  let c := forcingInverseSourceCutoff j s γ
  let τ := forcingThreadCoordinate T i
  let E := forcingThreadSection j (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) i
  let π := (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ
  let η := K ‘ i
  let q := woodinQuotientBoundHistory θ i p f.val j
  have h : IsWoodinIteration δ j s K := woodinIterationPrefix_of_stages hsj
  have hcj := h.code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  let := h.limitCardinal_ordinal
  have hnewstage : IsWoodinIteration δ (succ j) (woodinInverseSourceCode j s K)
      (woodinInverseCardinalNext j s K) := by
    have hh := hs j hj
    rw [woodinIterationRec_inverse h0 hlim hinac, kpair.π₁_kpair, kpair.π₂_kpair] at hh
    exact hh
  have hnew : (woodinInverseCardinalNext j s K) ‘ j = c := forcingFamilyNext_new _ _ _
  have hci : IsChoicelessInaccessible c := hnew ▸ hnewstage.inaccessible j (mem_succ_self j)
  let := hci.1
  have hKc : ∀ k ∈ j, K ‘ k ∈ c := by
    intro k hk
    have hh := hnewstage.increasing k (mem_succ_iff.mpr (Or.inr hk)) j (mem_succ_self j) hk
    rw [hnew] at hh
    rwa [show (woodinInverseCardinalNext j s K) ‘ k = K ‘ k from forcingFamilyNext_old hk] at hh
  have hγc : γ ∈ c := by
    have hγsub : γ ⊆ c := by
      intro x hx
      obtain ⟨k, hk, hxk⟩ := h.limitCardinal_cofinal hx
      exact IsOrdinal.toIsTransitive.mem_trans hxk (hKc k hk)
    rcases IsOrdinal.subset_iff.mp hγsub with he | he
    · exact absurd (show IsChoicelessInaccessible γ from he ▸ hci) hinac
    · exact he
  have hT : T ∈ hierarchy c := (h.inverse_small_above_limit hsucclim hci hγc).1
  have hcol := hcj.system.inverseColumn h0j hcj.subset_universe
  have hU : IsForcingPreorder T U := hcol.order.preorder
  have hot : IsForcingTop T U o := hcol.tops.top
  -- the forced regularity of the collapse cardinal name over the raw inverse limit
  have hforced := h.inverse_stage_forced_of_quotient_closure h0j hsucclim hinac hclosure
  let ν : ForcingName T := ⟨checkName o γ, checkName_isName hot.1 _⟩
  have hγforce : ∀ r ∈ T, r ∈ forcingFormula T U
      (regularCardinalFormula.or limitOfRegularCardinalsFormula)
      (standardTuple ![checkName o γ]) := by
    intro r hr
    apply forcingFormula_entailment singularLimitStageFormula
      (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_ hU hot hr ![ν] (hforced r hr)
    intro W _ _ _ v hv
    have hh : IsLimitOfRegularCardinals (v 0) ∧ InternalDependentChoiceAt (v 0) :=
      (Defined.eval_iff _).mp hv
    change regularCardinalFormula.Evalb v ∨ limitOfRegularCardinalsFormula.Evalb v
    exact Or.inr ((Defined.eval_iff _).mpr hh.1)
  have hDCγ : ∀ r ∈ T, r ∈ forcingFormula T U dependentChoiceAtFormula
      (standardTuple ![checkName o γ]) := by
    intro r hr
    have hh := hforced r hr
    rw [singularLimitStageFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.2
  have hκreg : ∀ r ∈ T, r ∈ forcingFormula T U regularCardinalFormula
      (standardTuple ![hartogsNumberName T U (checkName o γ)]) :=
    fun r hr ↦ hartogsNumberName_forces_regular hU hot hr ν (hγforce r hr) (hDCγ r hr)
  -- the iterand at the packed limit coordinate
  let Q : ForcingName T := ⟨woodinCollapseName T U (forcingInverseHartogsName j s γ)
    (forcingInverseRestorationName j s γ), woodinCollapseName_isName _ _ _ _⟩
  let Qs := forcingInverseCollapseName j s c (forcingInverseHartogsName j s γ)
    (forcingInverseRestorationName j s γ)
  let S := reverseInclusionOrderName T U Qs
  have hiter : IsForcingIterand T U Qs S ∅ := woodinInverseStage_iterand hs hj h0 hlim hinac
  have hrec := woodinIterationRec_inverse (θ := j) h0 hlim hinac
  have hPj : (forcingCodeP (woodinIterationPrefix θ)) ‘ j = twoStepConditions T U Qs ∅ := by
    rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self _), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode,
      forcingInverseCollapseCode, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
      forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new, Qs, T, U, s, K, γ, c,
      forcingInverseCodePoset, forcingInverseCodeOrder]
  have hRj : (forcingCodeR (woodinIterationPrefix θ)) ‘ j = twoStepOrder T U Qs S ∅ := by
    rw [woodinIterationPrefix_order_value hs hj (mem_succ_self _), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode,
      forcingInverseCollapseCode, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
      forcingIterationCodeNext, forcingCodeR_code, forcingFamilyNext_new, Qs, S, T, U, s, K, γ, c,
      forcingInverseCodePoset, forcingInverseCodeOrder]
  -- the base coordinate
  have hPi := woodinIterationPrefix_poset_value hsj hij (mem_succ_self i)
  have hRi := woodinIterationPrefix_order_value hsj hij (mem_succ_self i)
  have hoi := woodinIterationPrefix_top_value hsj hij (mem_succ_self i)
  have hbaseR := (hs i hiθ).code.system.order.preorder i (mem_succ_self i)
  have hbaseo := (hs i hiθ).code.system.tops.top i (mem_succ_self i)
  have hsplit := woodinInverseCoordinate_split hsj hij
  rw [hPi, hRi] at hsplit
  have hπfull := hcθ.system.projection hiθ hj hijs
  rw [woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i),
    woodinIterationPrefix_order_value hs hiθ (mem_succ_self i), hPj, hRj] at hπfull
  have hcomp : ∀ z ∈ twoStepConditions T U Qs ∅, τ ‘ (kpair.π₁ z) = π ‘ z := by
    intro z hz
    have hz' : z ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j := hPj ▸ hz
    rw [show π ‘ z = (kpair.π₁ z) ‘ i from
      woodinInverse_projection_value hs hj h0 hlim hinac hij hz']
    exact forcingThreadCoordinate_value (woodinInverse_first_mem hs hj h0 hlim hinac hz')
  -- the candidate's first coordinate is the bound history
  have hmemlocal : ∀ k ∈ j, woodinQuotientBoundRec θ i p f.val k ∈ (forcingCodeP s) ‘ k := by
    intro k hk
    rw [hcj.tableP.value_of_subset hcθ.tableP (woodinIterationPrefix_extends hsub).subP hk]
    exact (hprev k hk).1
  have hhist := woodinQuotientBoundHistory_inverse_condition hsj hij hmemlocal
  have hq : q ∈ T := hhist.1
  have hqb : τ ‘ q = p := hhist.2
  have hqp : ⟨q, E ‘ p⟩ₖ ∈ U := (hsplit.below q hq p hp).mpr (hqb.symm ▸ hbaseR.2.1 p hp)
  have hηi : η = (kpair.π₂ (woodinIterationRec i)) ‘ i := woodinIterationCardinalPrefix_value_of_stages hsj hij
  have hαη : α ∈ η := hηi.symm ▸ hα
  let : IsOrdinal η := (h.inaccessible i hij).1
  have hcl : ForcesProjectionQuotientClosedBelow
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) T U τ η := by
    simpa only [IterationQuotientClosedBelow, forcingInverseCode, forcingThreadCode,
      forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code, forcingCodet_code,
      forcingCodeπ_code, forcingFamilyNext_old hij, forcingFamilyNext_new,
      forcingMatrixNext_column hij, forcingLimitProjectionColumn_value hij, hPi, hRi, hoi,
      T, U, τ, η, s, K, forcingInverseCodePoset, forcingInverseCodeOrder] using hclosure i hij
  have hDCforce : ∀ r ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
      r ∈ forcingFormula ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) dependentChoiceBelowFormula
        (standardTuple ![checkName ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) η]) := by
    have hh := (h.stage i hij).2.2.2.2
    simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code, s, K, hPi, hRi, hoi, η] using hh
  let μ : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    ⟨woodinBoundCoordinateName θ i f.val j, woodinBoundCoordinateName_isName _ _ _ _⟩
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
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ))
        (A.check α) := by
    let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
    have hd0 := woodinQuotientSequence_semantics hs hiθ f hf G hG hpG
    have hfun := mem_function_of_mem_function_of_subset hd0.1 sep_subset
    have hnext := A.woodinCoordinate_descending hs hiθ hj hijs rfl rfl rfl f hd0
    rw [hPj, hRj] at hnext
    have hDCs : ∀ β ∈ A.check η, InternalDependentChoiceAt β :=
      (Defined.eval_iff _).mp ((A.checked_unary_truth dependentChoiceBelowFormula η).mpr
        ⟨p, hpG, hDCforce p hp⟩)
    have hclosed := A.projectionQuotient_closedBelow_of_forced hsplit.projection hU hcl
    have hmapsD := (woodinInverseCoordinate_split hs hiθ).projection.maps
    rw [woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)] at hmapsD
    refine ⟨hnext, ?_, hDCs _ ((A.check_mem_iff _ _).mpr hαη), ?_⟩
    · intro a ha
      obtain ⟨a₀, ha₀, rfl⟩ := (A.mem_check_iff α a).mp ha
      obtain ⟨d, hdD, hdG, had⟩ := (A.mem_projectionQuotient_iff hmapsD _).mp
        (function_value_mem hd0.1 ha)
      have hv := A.woodinCoordinate_value hs hj rfl rfl rfl f hfun ha hdD had
      have hdj : d ‘ j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j :=
        ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hdD).2.1 j hj
      have hdk : d ‘ j ∈ twoStepConditions T U Qs ∅ := hPj ▸ hdj
      have hν := mem_function_of_mem_function_of_subset hnext.1 sep_subset
      have hρ := twoStepProjection_maps T U Qs ∅
      let := IsFunction.of_mem hρ
      rw [value_compose_of_mem_function hν ((A.check_function_iff _ _ _).mpr hρ) ha,
        hv, A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hdk), twoStepProjection_value hdk]
      have hw : kpair.π₁ (d ‘ j) ∈ T := woodinInverse_first_mem hs hj h0 hlim hinac hdj
      have hwi : d ‘ i = (kpair.π₁ (d ‘ j)) ‘ i :=
        (woodinThread_inverse_coordinate hs hj h0 hlim hinac hdD).2 i hij
      have hdiG : d ‘ i ∈ A.G := by
        rwa [forcingThreadCoordinate_value hdD] at hdG
      have hqQ : A.check q ∈ A.projectionQuotient T τ :=
        (A.check_mem_projectionQuotient_iff hsplit.projection.maps).mpr ⟨hq, by
          show τ ‘ q ∈ G
          rw [hqb]
          exact hpG⟩
      have hwQ : A.check (kpair.π₁ (d ‘ j)) ∈ A.projectionQuotient T τ :=
        (A.check_mem_projectionQuotient_iff hsplit.projection.maps).mpr ⟨hw, by
          show τ ‘ (kpair.π₁ (d ‘ j)) ∈ G
          rw [forcingThreadCoordinate_value hw, ← hwi]
          exact hdiG⟩
      have hL := woodinInverseCodeLift_spec hcj h0j hij
      rw [hPi, hRi] at hL
      have hwk := (woodinThread_inverse_coordinate hs hj h0 hlim hinac hdD).2
      obtain ⟨e, heG, hed, hdec1, hdec2⟩ :=
        woodinBound_decision_for_selected_thread hs hiθ A rfl rfl rfl f hfun ha₀ hdD hdiG had
      have heP : e ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := A.generic.1.1 e heG
      have hed' : ⟨e, (kpair.π₁ (d ‘ j)) ‘ i⟩ₖ ∈
          (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i := by rwa [← hwi]
      have hc1 : ∀ m ∈ j, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
          ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G')
        (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
        (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G' →
        let B : ForcingContext V := ⟨_, _, _, G', hR, ho, hG'⟩
        let μ : ForcingName B.P := ⟨woodinBoundCoordinateName θ i f.val m,
          woodinBoundCoordinateName_isName θ i f.val m⟩
        ∃ X b : B.Model,
          B.ofName μ ∈ B.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ m) ^ X ∧
            b ∈ X ∧ (B.ofName μ) ‘ b = B.check ((kpair.π₁ (d ‘ j)) ‘ m) := by
        intro m hm G' hG' hR' ho' heG'
        have hh := hdec1 m (hsub m hm) G' hG' hR' ho' heG'
        rw [hwk m hm] at hh
        exact hh
      have hc2 : ∀ m ∈ j, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
          ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) G'), e ∈ G' →
        ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i))
          (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodet (woodinIterationPrefix θ)) ‘ i))
          (μ : ForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)),
          μ.val = woodinBoundCoordinateName θ i f.val m →
          let B : ForcingContext V := ⟨_, _, _, G', hRi, hti, hG'⟩
          ∃ X b : B.Model, B.ofName μ ∈
              B.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ m) ^ X ∧
            b ∈ X ∧ (B.ofName μ) ‘ b = B.check ((kpair.π₁ (d ‘ j)) ‘ m) := by
        intro m hm G' hG' heG' hRi' hti' μ' hμ'
        have hh := hdec2 m (hsub m hm) G' hG' heG' hRi' hti' μ' hμ'
        rw [hwk m hm] at hh
        exact hh
      exact A.projectionQuotient_separative_of_lift hsplit.projection.maps hL hqQ hwQ heG
        (fun r hr hrq b hb hbr hbe ↦
          hraw (kpair.π₁ (d ‘ j)) hw e heP hed' hc1 hc2 r hr hrq b hb hbr hbe)
    · intro β hβ hβα
      exact hclosed β (ordinal_mem_of_subset_mem hβα ((A.check_mem_iff _ _).mpr hαη))
  have hcollapse (H : Set V) (hH : IsExternalForcingGeneric T U H) :
      let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
      ∃ β : C.Model, IsRegularCardinal β ∧ β ⊆ C.check c ∧ C.check α ∈ β ∧
        C.ofName ⟨Qs, hiter.posetName⟩ = woodinCollapse β (C.check c) ∧
        C.ofName ⟨S, hiter.orderName⟩ = woodinCollapseOrder β (C.check c) := by
    let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
    obtain ⟨r, hr⟩ := hH.1.2.1
    let ν' : ForcingName T := ⟨checkName o γ, checkName_isName hot.1 _⟩
    have hvv : C.ofName (C.hartogsName ν') = hartogsNumber (C.check γ) := C.hartogsName_value ν'
    have hreg : IsRegularCardinal (hartogsNumber (C.check γ)) := by
      rw [← hvv]
      exact (Defined.eval_iff _).mp ((C.formula_truth regularCardinalFormula
        ![C.hartogsName ν']).mpr ⟨r, hr, hκreg r (hH.1.1 r hr)⟩)
    have hαγ : α ∈ γ := h.cardinal_subset_limit hij α hαη
    have hm : C.check α ∈ C.check γ := (C.check_mem_iff _ _).mpr hαγ
    let := IsOrdinal.of_mem hm
    refine ⟨hartogsNumber (C.check γ), hreg,
      IsOrdinal.toIsTransitive.transitive _ (C.hartogs_checked_mem hci hT hγc), ?_,
      C.saturatedHartogsCollapseName_value hci hT hγc,
      C.saturatedHartogsCollapseOrderName_value hci hT hγc⟩
    exact ordinal_cardLE_iff_mem_hartogsNumber.mp
      (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hm))
  let σ := forcingSelectedUnion T U o (twoStepNames Qs ∅) (twoStepTailSelector T U Qs ∅)
    (nameAction E μ.val)
  let w := forcingLocalCanonicalName T U o c (E ‘ p) σ
  have hpair : ⟨q, w⟩ₖ ∈ twoStepConditions T U Qs ∅ :=
    transported_local_union_pair_mem hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
      hπfull.maps hcomp hdata (fun H hH _ ↦ hcollapse H hH)
  have hqnext : woodinQuotientBoundRec θ i p f.val j = ⟨q, w⟩ₖ := by
    rw [woodinQuotientBoundRec_inverse hij hlim hinac]
    unfold woodinBoundInverseTail woodinBoundTailName
    dsimp only
    simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code,
      woodinStageCardinal_code]
    rfl
  have hnorm : q ∈ atomicEquality T U w σ :=
    transported_local_union_normalization hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
      hπfull.maps hcomp hdata (fun H hH _ ↦ hcollapse H hH)
  refine ⟨?_, ?_⟩
  · apply (woodinQuotientBoundAt_iff_generics hs hiθ hj hijs hp f).mpr
    refine ⟨?_, ?_⟩
    · rw [hqnext, hPj]
      exact hpair
    · intro G hG hpG
      let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
      obtain ⟨hdesc, hbound, hDC, hclosed⟩ := hdata G hG hpG
      have hπpair : π ‘ ⟨q, w⟩ₖ = p := by
        rw [← hcomp _ hpair, kpair.π₁_kpair, hqb]
      have hpQ : A.check ⟨q, w⟩ₖ ∈ A.projectionQuotient (twoStepConditions T U Qs ∅) π :=
        (A.check_mem_projectionQuotient_iff hπfull.maps).mpr ⟨hpair, hπpair.symm ▸ hpG⟩
      dsimp only
      rw [hqnext, hPj, hRj]
      refine ⟨hpQ, ?_⟩
      apply A.local_union_quotient_separative_bound hsplit hU hot hiter hπfull.maps hcomp μ
        hdesc hbound hci hT (function_value_mem hsplit.maps hp) hqp hDC hclosed ?_ hpQ
      intro H hH hA
      obtain ⟨β, hβ, hβc, hαβ, hQ', hS'⟩ := hcollapse H hH
      refine ⟨β, hβ, hβc, ?_, hQ', hS'⟩
      rwa [A.projectionInclusion_check _ hsplit hA α]
  · intro _
    constructor
    · intro he
      exact absurd he hlim
    · intro _ _
      unfold woodinBoundInverseTail woodinBoundTailName woodinBoundInverseRawTail
      dsimp only
      simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code,
        woodinStageCardinal_code]
      exact hnorm

end ZFVP
