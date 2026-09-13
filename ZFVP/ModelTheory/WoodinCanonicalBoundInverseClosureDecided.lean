import ZFVP.ModelTheory.WoodinCanonicalBoundInverseClosure
import ZFVP.ModelTheory.WoodinCanonicalBoundDecision

/-! The canonical quotient bound at the new inverse-limit coordinate, with a raw comparison
premise that carries the decision property.

`woodinInverse_raw_quotient_closedBelow` asks for the raw thread comparison at an arbitrary
base condition `e` below `d ‘ i`. That premise cannot be discharged: the raw comparison lemmas
`woodinRawLift_successor` and `woodinRawLift_inverse` need `e` to decide the selected value of
the canonical coordinate name, and `d ‘ i` does not. Here the comparison premise carries the
two decision properties produced by `woodinBound_decision_condition_uniform`, and the deciding
condition is obtained from the generic filter inside the proof. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The decision condition for a prescribed thread.

`woodinBound_decision_condition_uniform` picks the thread `d` selected by the name `f` at the
index `a` itself and does not hand that choice back. This is the same statement for a thread
`d` supplied by the caller together with the equation `f ‘ ǎ = ď` that identifies it as the
selected one. The two conclusions are literally the two conclusions of
`woodinBound_decision_condition_uniform`. -/
theorem woodinBound_decision_for_selected_thread [Countable V] {δ θ i α a d : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (A : ForcingContext V)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName A.P)
    (hfD : A.ofName f ∈
      A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check α)
    (ha : a ∈ α) (hdD : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hdiG : d ‘ i ∈ A.G) (hveq : (A.ofName f) ‘ (A.check a) = A.check d) :
    ∃ e ∈ A.G, ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i ∧
      (∀ j ∈ θ, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
          ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G')
        (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
        (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G' →
        let B : ForcingContext V := ⟨_, _, _, G', hR, ho, hG'⟩
        let μ : ForcingName B.P := ⟨woodinBoundCoordinateName θ i f.val j,
          woodinBoundCoordinateName_isName θ i f.val j⟩
        ∃ X b : B.Model,
          B.ofName μ ∈ B.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
            b ∈ X ∧ (B.ofName μ) ‘ b = B.check (d ‘ j)) ∧
      (∀ j ∈ θ, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
          ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) G'), e ∈ G' →
        ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i))
          (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodet (woodinIterationPrefix θ)) ‘ i))
          (μ : ForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)),
          μ.val = woodinBoundCoordinateName θ i f.val j →
          let B : ForcingContext V := ⟨_, _, _, G', hRi, hti, hG'⟩
          ∃ X b : B.Model, B.ofName μ ∈
              B.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
            b ∈ X ∧ (B.ofName μ) ‘ b = B.check (d ‘ j)) := by
  have hPi : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value hs hi (mem_succ_self i)
  have hRi : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_order_value hs hi (mem_succ_self i)
  have hoi : (forcingCodet (woodinIterationPrefix θ)) ‘ i =
      (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_top_value hs hi (mem_succ_self i)
  obtain ⟨P, R, one, G, hpre, htop, hG⟩ := A
  have hP' : P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := hP
  have hR' : R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i := hR
  have ho' : one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i := ho
  subst hP'
  subst hR'
  subst ho'
  let A : ForcingContext V := ⟨_, _, _, G, hpre, htop, hG⟩
  let uα : ForcingName A.P := ⟨checkName A.one α, checkName_isName A.top.1 α⟩
  let uD : ForcingName A.P :=
    ⟨checkName A.one (forcingInverseCodePoset θ (woodinIterationPrefix θ)),
      checkName_isName A.top.1 _⟩
  obtain ⟨q1, hq1G, hq1⟩ := (A.formula_truth boundedFunctionFormula ![f, uα, uD]).mp
    ((Defined.eval_iff _).mpr hfD)
  obtain ⟨q2, hq2G, hq2⟩ := (A.checkedFunctionValue_truth f a d).mpr
    ⟨IsFunction.of_mem hfD, hveq⟩
  obtain ⟨r, hrG, hr1, hr2⟩ := hG.1.2.2.2 q1 hq1G q2 hq2G
  obtain ⟨e, heG, he1, he2⟩ := hG.1.2.2.2 r hrG (d ‘ i) hdiG
  have heP : e ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := hG.1.1 e heG
  have hrP : r ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := hG.1.1 r hrG
  have hq1P : q1 ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := hG.1.1 q1 hq1G
  have hq2P : q2 ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := hG.1.1 q2 hq2G
  have heq1 : ⟨e, q1⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    hpre.2.2 e heP r hrP q1 hq1P he1 hr1
  have heq2 : ⟨e, q2⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    hpre.2.2 e heP r hrP q2 hq2P he1 hr2
  have h1 : e ∈ forcingFormula ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) boundedFunctionFormula
      (standardTuple ![f.val, checkName ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) α,
        checkName ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
          (forcingInverseCodePoset θ (woodinIterationPrefix θ))]) :=
    (forcingFormula_regular hpre boundedFunctionFormula _).2.1 q1 hq1 e heP heq1
  have h2 : ForcesCheckedFunctionValue ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) f.val e a d :=
    (forcingFormula_regular hpre functionValueFormula _).2.1 q2 hq2 e heP heq2
  have h1' : e ∈ forcingFormula ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
      ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) boundedFunctionFormula
      (standardTuple ![f.val, checkName ((forcingCodet (woodinIterationPrefix θ)) ‘ i) α,
        checkName ((forcingCodet (woodinIterationPrefix θ)) ‘ i)
          (forcingInverseCodePoset θ (woodinIterationPrefix θ))]) := by
    rw [hPi, hRi, hoi]; exact h1
  have h2' : ForcesCheckedFunctionValue ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
      ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
      ((forcingCodet (woodinIterationPrefix θ)) ‘ i) f.val e a d := by
    rw [hPi, hRi, hoi]; exact h2
  refine ⟨e, heG, by rw [← hR]; exact he2, ?_, ?_⟩
  · intro j hj G' hG' hR' ho' heG' B μ
    let f' : ForcingName B.P := ⟨f.val, f.property⟩
    obtain ⟨hfun, hb, hval⟩ := forcedName_function_decision B h1 h2 ha heG' f' rfl
    exact ⟨B.check α, B.check a,
      (B.woodinCoordinate_typing_value hs hj rfl rfl rfl f' hfun hb hdD hval).1, hb,
      (B.woodinCoordinate_typing_value hs hj rfl rfl rfl f' hfun hb hdD hval).2⟩
  · intro j hj G' hG' heG' hR' ho' μ hμ B
    let f' : ForcingName B.P := ⟨f.val, by
      rw [show B.P = (forcingCodeP (woodinIterationPrefix θ)) ‘ i from rfl, hPi]
      exact f.property⟩
    obtain ⟨hfun, hb, hval⟩ := forcedName_function_decision B h1' h2' ha heG' f' rfl
    have hμeq : μ = ⟨woodinBoundCoordinateName θ i f'.val j,
        by simpa only [← hPi] using woodinBoundCoordinateName_isName θ i f'.val j⟩ :=
      Subtype.ext hμ
    rw [hμeq]
    exact ⟨B.check α, B.check a,
      (B.woodinCoordinate_typing_value hs hj hPi hRi hoi f' hfun hb hdD hval).1, hb,
      (B.woodinCoordinate_typing_value hs hj hPi hRi hoi f' hfun hb hdD hval).2⟩

/-- Closure of the raw inverse-limit projection quotient at the new coordinate `θ`, from a raw
order comparison whose base condition decides the selected coordinate values.

Same as `woodinInverse_raw_quotient_closedBelow` except that `hraw` may assume the two decision
properties for the thread `d` and the condition `e`. Those two properties are exactly what
`woodinBound_decision_condition_uniform` produces, and the proof gets `e` from the generic
filter through `woodinBound_decision_for_selected_thread`. -/
theorem woodinInverse_raw_quotient_closedBelow_decided [Countable V] {δ θ i : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (h0 : ∅ ∈ θ) (hi : i ∈ θ)
    (hinv : ∀ p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
      ∀ f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i),
      ∀ α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i,
      ForcesWoodinQuotientSequence θ i p f.val α →
      ∀ j ∈ θ, i ∈ j → j ≠ succ (⋃ˢ j) →
        ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) →
        (∀ k ∈ j, IsWoodinNormalizedQuotientBoundAt θ i p f.val α k) →
        IsWoodinNormalizedQuotientBoundAt θ i p f.val α j)
    (hraw : ∀ p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
      ∀ f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i),
      ∀ α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i,
      ForcesWoodinQuotientSequence θ i p f.val α →
      ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      ∀ e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
        ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        (∀ j ∈ θ, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
            ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G')
          (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
          (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
            ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G' →
          let A : ForcingContext V := ⟨_, _, _, G', hR, ho, hG'⟩
          let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val j,
            woodinBoundCoordinateName_isName θ i f.val j⟩
          ∃ X b : A.Model,
            A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
              b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)) →
        (∀ j ∈ θ, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
            ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) G'), e ∈ G' →
          ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
              ((forcingCodeR (woodinIterationPrefix θ)) ‘ i))
            (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
              ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
              ((forcingCodet (woodinIterationPrefix θ)) ‘ i))
            (μ : ForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)),
            μ.val = woodinBoundCoordinateName θ i f.val j →
            let A : ForcingContext V := ⟨_, _, _, G', hRi, hti, hG'⟩
            ∃ X b : A.Model, A.ofName μ ∈
                A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
              b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)) →
        ∀ r ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
          ⟨r, woodinQuotientBoundHistory θ i p f.val θ⟩ₖ
            ∈ forcingInverseCodeOrder θ (woodinIterationPrefix θ) →
          ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
            ⟨b, (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘ r⟩ₖ
              ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
            ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
            ⟨(woodinInverseCodeLift θ (woodinIterationPrefix θ) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ
              ∈ forcingInverseCodeOrder θ (woodinIterationPrefix θ)) :
    IterationQuotientClosedBelow (forcingInverseCode θ (woodinIterationPrefix θ)) i θ
      ((woodinIterationCardinalPrefix θ) ‘ i) := by
  let := IsOrdinal.of_mem hi
  have hprefix := woodinIterationPrefix_of_stages hs
  have hcθ := hprefix.code
  let := (hprefix.inaccessible i hi).1
  have hηval : (woodinIterationCardinalPrefix θ) ‘ i = (kpair.π₂ (woodinIterationRec i)) ‘ i :=
    woodinIterationCardinalPrefix_value_of_stages hs hi
  have hPi : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value hs hi (mem_succ_self i)
  have hRi : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_order_value hs hi (mem_succ_self i)
  have hti : (forcingCodet (woodinIterationPrefix θ)) ‘ i =
      (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_top_value hs hi (mem_succ_self i)
  have hcol := hcθ.system.inverseColumn h0 hcθ.subset_universe
  have hUpre : IsForcingPreorder (forcingInverseCodePoset θ (woodinIterationPrefix θ))
      (forcingInverseCodeOrder θ (woodinIterationPrefix θ)) := hcol.order.preorder
  have hRpre : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) := by
    rw [← hPi, ← hRi]; exact hcθ.system.order.preorder i hi
  have htop : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) := by
    rw [← hPi, ← hRi, ← hti]; exact hcθ.system.tops.top i hi
  have hproj : IsForcingProjection ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (forcingInverseCodePoset θ (woodinIterationPrefix θ))
      (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
      (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) := by
    rw [← hPi, ← hRi]; exact (woodinInverseCoordinate_split hs hi).projection
  have hL := woodinInverseCodeLift_spec hcθ h0 hi
  rw [hPi, hRi] at hL
  have key : ForcesProjectionQuotientClosedBelow
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (forcingInverseCodePoset θ (woodinIterationPrefix θ))
      (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
      (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)
      ((woodinIterationCardinalPrefix θ) ‘ i) := by
    apply forcesProjectionQuotientClosedBelow_of_named_bounds hRpre htop hproj hUpre
    intro α hα p hp f hdesc
    have hαrec : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i := hηval ▸ hα
    let := IsOrdinal.of_mem hα
    have hf : ForcesWoodinQuotientSequence θ i p f.val α := hdesc
    refine ⟨⟨checkName ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (woodinQuotientBoundHistory θ i p f.val θ), checkName_isName htop.1 _⟩, ?_⟩
    apply projectionQuotient_bound_forced_of_generics hRpre htop hproj hUpre hp f
    intro G hG hpG
    let A : ForcingContext V := ⟨_, _, _, G, hRpre, htop, hG⟩
    have hmaps : (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)
        ∈ A.P ^ (forcingInverseCodePoset θ (woodinIterationPrefix θ)) := hproj.maps
    have hhist := woodinQuotientBoundHistory_mem_and_projects hs hc hi hαrec hp f hf
    have hqQ : A.check (woodinQuotientBoundHistory θ i p f.val θ) ∈
        A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) := by
      refine (A.check_mem_projectionQuotient_iff hmaps).mpr ⟨hhist.1, ?_⟩
      show _ ∈ G
      rw [hhist.2]
      exact hpG
    refine ⟨hqQ, ?_⟩
    intro a ha
    have hdescG : IsForcingDescending
        (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
        (forcingSeparativeOrder
          (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
            (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
          (A.projectionQuotientOrder (forcingInverseCodePoset θ (woodinIterationPrefix θ))
            (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
            (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)))
        (A.check α) (A.ofName f) :=
      woodinQuotientSequence_semantics hs hi f hf G hG hpG
    obtain ⟨a₀, ha₀, rfl⟩ := (A.mem_check_iff α a).mp ha
    obtain ⟨w, hw, hwG, hval⟩ :=
      (A.mem_projectionQuotient_iff hmaps _).mp (function_value_mem hdescG.1 ha)
    have hwi : w ‘ i ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := by
      rw [← hPi]
      exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hw).2.1 i hi
    have hwiG : w ‘ i ∈ A.G := by
      show _ ∈ G
      rwa [forcingThreadCoordinate_value hw] at hwG
    have hwQ : A.check w ∈
        A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) :=
      (A.check_mem_projectionQuotient_iff hmaps).mpr ⟨hw, hwG⟩
    have hfD : A.ofName f ∈
        A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check α := by
      refine mem_function_iff.mpr ⟨fun z hz ↦ ?_, (mem_function_iff.mp hdescG.1).2⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hdescG.1).1 z hz)
      exact kpair_mem_iff.mpr ⟨hx, (mem_sep_iff.mp hy).1⟩
    obtain ⟨e, heG, hed, hdec1, hdec2⟩ :=
      woodinBound_decision_for_selected_thread hs hi A rfl rfl rfl f hfD ha₀ hw hwiG hval
    have heP : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i := by
      rw [hPi]; exact A.generic.1.1 e heG
    have hed' : ⟨e, w ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by
      rw [hRi]; exact hed
    rw [hval]
    refine A.projectionQuotient_separative_of_lift
      (L := woodinInverseCodeLift θ (woodinIterationPrefix θ) i) hmaps hL hqQ hwQ heG ?_
    intro r hr hrq b hb hbr hbe
    have hb' : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i := by rw [hPi]; exact hb
    have hbr' : ⟨b, (forcingThreadCoordinate
        (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘ r⟩ₖ
        ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by rw [hRi]; exact hbr
    have hbe' : ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by
      rw [hRi]; exact hbe
    exact hraw p hp f α hαrec hf w hw e heP hed' hdec1 hdec2 r hr hrq b hb' hbr' hbe'
  simpa only [IterationQuotientClosedBelow, forcingInverseCode, forcingThreadCode,
    forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code, forcingCodet_code,
    forcingCodeπ_code, forcingFamilyNext_old hi, forcingFamilyNext_new,
    forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi, hPi, hRi, hti,
    forcingInverseCodePoset, forcingInverseCodeOrder] using key

end ZFVP
