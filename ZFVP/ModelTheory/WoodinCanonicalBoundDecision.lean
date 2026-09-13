import ZFVP.ModelTheory.WoodinBoundInvariantSemantics
import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.ModelTheory.ForcingCompositionName

/-! The base condition that decides the selected coordinate values.

The raw order comparison lemmas `woodinRawLift_successor` and `woodinRawLift_inverse` both take a
premise saying that a condition `e` of the coordinate `i` poset decides the selected value of the
canonical coordinate name at a stage `j` to be the `j`-th coordinate of a fixed ground thread `d`.
This file produces one such `e`, together with the thread `d`, from a condition `p` forcing the
descending sequence, inside a fixed generic filter containing `p`. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Enlarging the codomain of an internal function. -/
private theorem decision_mem_function_mono {g X Y Y' : V} (hg : g ∈ Y ^ X) (hY : Y ⊆ Y') :
    g ∈ Y' ^ X := by
  refine mem_function_iff.mpr ⟨fun p hp ↦ ?_, (mem_function_iff.mp hg).2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hg).1 p hp)
  exact kpair_mem_iff.mpr ⟨hx, hY y hy⟩

/-- A condition forcing that a name is a function on `ᾰ` into `Ď` with value `ď` at `ǎ` decides
those three facts in every generic filter containing it. -/
theorem forcedName_function_decision (B : ForcingContext V) {ν D d α a e : V}
    (h1 : e ∈ forcingFormula B.P B.R boundedFunctionFormula
      (standardTuple ![ν, checkName B.one α, checkName B.one D]))
    (h2 : ForcesCheckedFunctionValue B.P B.R B.one ν e a d) (ha : a ∈ α) (heG : e ∈ B.G)
    (g : ForcingName B.P) (hg : g.val = ν) :
    B.ofName g ∈ B.check D ^ B.check α ∧ B.check a ∈ B.check α ∧
      (B.ofName g) ‘ (B.check a) = B.check d := by
  let uα : ForcingName B.P := ⟨checkName B.one α, checkName_isName B.top.1 α⟩
  let uD : ForcingName B.P := ⟨checkName B.one D, checkName_isName B.top.1 D⟩
  let gν : ForcingName B.P := ⟨ν, by rw [← hg]; exact g.property⟩
  have hgν : gν = g := (Subtype.ext hg).symm
  have hmeet : GenericMeets B.G (forcingFormula B.P B.R boundedFunctionFormula
      (standardTuple (fun k ↦ ((![gν, uα, uD] : Fin 3 → ForcingName B.P) k).val))) :=
    ⟨e, heG, h1⟩
  have hev := (B.formula_truth boundedFunctionFormula ![gν, uα, uD]).mpr hmeet
  have hfun : B.ofName g ∈ B.check D ^ B.check α := by
    rw [← hgν]
    exact (Defined.eval_iff _).mp hev
  have hvalue := (B.checkedFunctionValue_truth g a d).mp ⟨e, heG, by rw [hg]; exact h2⟩
  exact ⟨hfun, (B.check_mem_iff a α).mpr ha, hvalue.2⟩

section

variable {δ θ : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k)))
include hs

/-- The coordinate name at `j` is a function into the stage `j` poset, and its value at `a` is the
`j`-th coordinate of the thread `d` selected by `f` at `a`. -/
theorem ForcingContext.woodinCoordinate_typing_value {i j d : V} (A : ForcingContext V)
    (hj : j ∈ θ)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName A.P) {X a : A.Model}
    (hf : A.ofName f ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ X)
    (ha : a ∈ X) (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (had : (A.ofName f) ‘ a = A.check d) :
    let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val j,
      by simpa only [← hP] using woodinBoundCoordinateName_isName θ i f.val j⟩
    A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
      (A.ofName μ) ‘ a = A.check (d ‘ j) := by
  let D := forcingInverseCodePoset θ (woodinIterationPrefix θ)
  let ρ := forcingThreadCoordinate D j
  have hρ : ρ ∈ ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ D :=
    (woodinInverseCoordinate_split hs hj).projection.maps
  intro μ
  refine ⟨?_, A.woodinCoordinate_value hs hj hP hR ho f hf ha hd had⟩
  have hv : A.ofName μ = compose (A.ofName f) (A.check ρ) := by
    have he := A.forcingCompositionName_value f ⟨checkName A.one ρ, checkName_isName A.top.1 ρ⟩
    change A.ofName ⟨forcingCompositionName A.P A.R f.val (checkName A.one ρ), _⟩ =
      compose (A.ofName f) (A.check ρ) at he
    simpa only [μ, woodinBoundCoordinateName, ← hP, ← hR, ← ho, ρ, D] using he
  rw [hv]
  exact compose_function hf ((A.check_function_iff ρ D _).mpr hρ)

variable {i p α a : V} [IsOrdinal α] (hi : i ∈ θ)
include hi

/-- One base condition of the generic filter decides all coordinate values of one ground thread.

From a condition `p` forcing that the name `f` is a descending sequence in the projection quotient
of the inverse limit, and a generic filter `G` containing `p`, one reads off a ground thread `d`
selected by `f` at the index `a`, and a condition `e ∈ G` below `d ‘ i` which forces, for every
stage `j ∈ θ` at once, that the coordinate name at `j` is a function whose value at `ǎ` is the
check of `d ‘ j`. The two conclusions are the premises `hdecide` of `woodinRawLift_successor`
and of `woodinRawLift_inverse`, written in their respective spellings of the coordinate `i`
poset. -/
theorem woodinBound_decision_condition_uniform [Countable V]
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) (hpG : p ∈ G)
    (ha : a ∈ α) :
    ∃ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      ∃ e ∈ G, ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i ∧
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
              b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)) ∧
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
              b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)) := by
  have hPi : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value hs hi (mem_succ_self i)
  have hRi : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_order_value hs hi (mem_succ_self i)
  have hoi : (forcingCodet (woodinIterationPrefix θ)) ‘ i =
      (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_top_value hs hi (mem_succ_self i)
  have hpre : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    (hs i hi).code.system.order.preorder i (mem_succ_self i)
  have htop : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    (hs i hi).code.system.tops.top i (mem_succ_self i)
  let A : ForcingContext V := ⟨_, _, _, G, hpre, htop, hG⟩
  have hsplit := (woodinInverseCoordinate_split hs hi).projection
  rw [hPi, hRi] at hsplit
  have hπ : forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i ∈
      A.P ^ (forcingInverseCodePoset θ (woodinIterationPrefix θ)) := hsplit.maps
  have hdesc : IsForcingDescending
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
  have haα : A.check a ∈ A.check α := (A.check_mem_iff a α).mpr ha
  obtain ⟨d, hdD, hdG, hveq⟩ :=
    (A.mem_projectionQuotient_iff hπ _).mp (function_value_mem hdesc.1 haα)
  rw [forcingThreadCoordinate_value hdD] at hdG
  have hdiG : d ‘ i ∈ G := hdG
  have hfD : A.ofName f ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check α :=
    decision_mem_function_mono hdesc.1 (fun z hz ↦ (mem_sep_iff.mp hz).1)
  -- the two facts about `f` that the condition has to decide
  let uα : ForcingName A.P := ⟨checkName A.one α, checkName_isName A.top.1 α⟩
  let uD : ForcingName A.P := ⟨checkName A.one (forcingInverseCodePoset θ (woodinIterationPrefix θ)),
    checkName_isName A.top.1 _⟩
  have hmeet := (A.formula_truth boundedFunctionFormula ![f, uα, uD]).mp
    ((Defined.eval_iff _).mpr hfD)
  obtain ⟨q1, hq1G, hq1⟩ := hmeet
  obtain ⟨q2, hq2G, hq2⟩ := (A.checkedFunctionValue_truth f a d).mpr
    ⟨IsFunction.of_mem hfD, hveq⟩
  -- one condition of the filter below both decisions and below `d ‘ i`
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
  refine ⟨d, hdD, e, heG, he2, ?_, ?_⟩
  · intro j hj G' hG' hR' ho' heG' B μ
    obtain ⟨hfun, hb, hval⟩ := forcedName_function_decision B h1 h2 ha heG' f rfl
    exact ⟨B.check α, B.check a,
      (B.woodinCoordinate_typing_value hs hj rfl rfl rfl f hfun hb hdD hval).1, hb,
      (B.woodinCoordinate_typing_value hs hj rfl rfl rfl f hfun hb hdD hval).2⟩
  · intro j hj G' hG' heG' hR' ho' μ hμ B
    let f' : ForcingName B.P :=
      ⟨f.val, by rw [show B.P = (forcingCodeP (woodinIterationPrefix θ)) ‘ i from rfl, hPi]
                 exact f.property⟩
    obtain ⟨hfun, hb, hval⟩ := forcedName_function_decision B h1' h2' ha heG' f' rfl
    have hμeq : μ = ⟨woodinBoundCoordinateName θ i f'.val j,
        by simpa only [← hPi] using woodinBoundCoordinateName_isName θ i f'.val j⟩ :=
      Subtype.ext hμ
    rw [hμeq]
    exact ⟨B.check α, B.check a,
      (B.woodinCoordinate_typing_value hs hj hPi hRi hoi f' hfun hb hdD hval).1, hb,
      (B.woodinCoordinate_typing_value hs hj hPi hRi hoi f' hfun hb hdD hval).2⟩

/-- The fixed stage form of `woodinBound_decision_condition_uniform`. -/
theorem woodinBound_decision_condition [Countable V]
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) (hpG : p ∈ G)
    (j : V) (hj : j ∈ θ) (ha : a ∈ α) :
    ∃ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      ∃ e ∈ G, ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i ∧
        (∀ (G' : Set V) (hG' : IsExternalForcingGeneric
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
              b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)) ∧
        (∀ (G' : Set V) (hG' : IsExternalForcingGeneric
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
              b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)) := by
  obtain ⟨d, hdD, e, heG, hed, hsucc, hinv⟩ :=
    woodinBound_decision_condition_uniform hs hi f hf G hG hpG ha
  exact ⟨d, hdD, e, heG, hed, hsucc j hj, hinv j hj⟩

end

end ZFVP
