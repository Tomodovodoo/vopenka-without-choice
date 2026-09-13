import ZFVP.ModelTheory.WoodinInverseFirstCoordinates
import ZFVP.ModelTheory.NormalizedUnionStrongerBound
import ZFVP.ModelTheory.WoodinBoundNormalization
import ZFVP.ModelTheory.WoodinQuotientBoundEquations
import ZFVP.ModelTheory.InverseSourceCollapseCode
import ZFVP.ModelTheory.WoodinCoordinateProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 1000000 in
/-- Raw lift comparison at a packed limit coordinate `j` of the W02 iteration.
The candidate at `j` is a thread in the raw inverse limit paired with a collapse
name, so the two-step bound of `twoStepStronger_le_selected_of_normalization`
applies once the spliced thread is checked coordinatewise against `d`. -/
theorem woodinRawLift_inverse [Countable V] {δ θ i j p f d e : V} [IsOrdinal θ]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hj : j ∈ θ) (hij : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (he : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hed : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hiter : IsForcingIterand (forcingInverseCodePoset j (woodinIterationPrefix j))
      (forcingInverseCodeOrder j (woodinIterationPrefix j))
      (forcingInverseCollapseName j (woodinIterationPrefix j)
        (forcingInverseSourceCutoff j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
        (forcingInverseHartogsName j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
        (forcingInverseRestorationName j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j))))
      (reverseInclusionOrderName (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j))
        (forcingInverseCollapseName j (woodinIterationPrefix j)
          (forcingInverseSourceCutoff j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseHartogsName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseRestorationName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j))))) ∅)
    (hmem : ∀ l ∈ succ j, woodinQuotientBoundRec θ i p f l ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ l)
    (hnorm : IsWoodinBoundNormalizationAt θ i p f j)
    (hprev : ∀ m ∈ j, i ⊆ m →
      ∀ r ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ m,
        ⟨r, woodinQuotientBoundRec θ i p f m⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ m →
        ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
          ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, m⟩ₖ) ‘ r⟩ₖ
            ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
          ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
          ⟨((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, m⟩ₖ) ‘ ⟨r, b⟩ₖ, d ‘ m⟩ₖ
            ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ m)
    (hdecide : ∀ (G : Set V) (hG : IsExternalForcingGeneric
        ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
        ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) G), e ∈ G →
      ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix θ)) ‘ i))
        (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
          ((forcingCodet (woodinIterationPrefix θ)) ‘ i))
        (μ : ForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)),
        μ.val = woodinBoundCoordinateName θ i f j →
        let A : ForcingContext V := ⟨_, _, _, G, hRi, hti, hG⟩
        ∃ X a : A.Model, A.ofName μ ∈
            A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
          a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ j)) :
    ∀ r ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j,
      ⟨r, woodinQuotientBoundRec θ i p f j⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ j →
      ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
        ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ r⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨r, b⟩ₖ, d ‘ j⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ j := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hij
  have h0j : (∅ : V) ∈ j := IsOrdinal.empty_mem_iff_nonempty.mpr (ne_empty_iff_isNonempty.mp h0)
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hiθ : i ∈ θ := hsub i hij
  have hsj : ∀ l ∈ j, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)) := fun l hl ↦ hs l (hsub l hl)
  have hcj := (woodinIterationPrefix_of_stages hsj).code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have hext := woodinIterationPrefix_extends hsub
  have hPval : ∀ m ∈ j, (forcingCodeP (woodinIterationPrefix j)) ‘ m =
      (forcingCodeP (woodinIterationPrefix θ)) ‘ m :=
    fun m hm ↦ hcj.tableP.value_of_subset hcθ.tableP hext.subP hm
  have hRval : ∀ m ∈ j, (forcingCodeR (woodinIterationPrefix j)) ‘ m =
      (forcingCodeR (woodinIterationPrefix θ)) ‘ m :=
    fun m hm ↦ hcj.tableR.value_of_subset hcθ.tableR hext.subR hm
  have hπval : ∀ m ∈ j, ∀ n ∈ j, (forcingCodeπ (woodinIterationPrefix j)) ‘ ⟨m, n⟩ₖ =
      (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨m, n⟩ₖ :=
    fun m hm n hn ↦ hcj.tableπ.value_of_subset hcθ.tableπ hext.subπ
      (mem_prod_iff.mpr ⟨m, hm, n, hn, rfl⟩)
  have hLval : ∀ m ∈ j, ∀ n ∈ j, (forcingCodeL (woodinIterationPrefix j)) ‘ ⟨m, n⟩ₖ =
      (forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨m, n⟩ₖ :=
    fun m hm n hn ↦ hcj.tableL.value_of_subset hcθ.tableL hext.subL
      (mem_prod_iff.mpr ⟨m, hm, n, hn, rfl⟩)
  have hrec := woodinIterationRec_inverse (θ := j) h0 hlim hinac
  -- the stage data at the limit coordinate
  have hPj : (forcingCodeP (woodinIterationPrefix θ)) ‘ j =
      twoStepConditions (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j))
        (forcingInverseCollapseName j (woodinIterationPrefix j)
          (forcingInverseSourceCutoff j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseHartogsName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseRestorationName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))) ∅ := by
    rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self _), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode,
      forcingInverseCollapseCode, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
      forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new,
      forcingInverseCodePoset, forcingInverseCodeOrder, forcingInverseCollapseName]
  have hRj : (forcingCodeR (woodinIterationPrefix θ)) ‘ j =
      twoStepOrder (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j))
        (forcingInverseCollapseName j (woodinIterationPrefix j)
          (forcingInverseSourceCutoff j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseHartogsName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseRestorationName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j))))
        (reverseInclusionOrderName (forcingInverseCodePoset j (woodinIterationPrefix j))
          (forcingInverseCodeOrder j (woodinIterationPrefix j))
          (forcingInverseCollapseName j (woodinIterationPrefix j)
            (forcingInverseSourceCutoff j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseHartogsName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseRestorationName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j))))) ∅ := by
    rw [woodinIterationPrefix_order_value hs hj (mem_succ_self _), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode,
      forcingInverseCollapseCode, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
      forcingIterationCodeNext, forcingCodeR_code, forcingFamilyNext_new,
      forcingInverseCodePoset, forcingInverseCodeOrder, forcingInverseCollapseName]
  have hcol := hcj.system.inverseColumn h0j hcj.subset_universe
  have hUpre : IsForcingPreorder (forcingInverseCodePoset j (woodinIterationPrefix j))
      (forcingInverseCodeOrder j (woodinIterationPrefix j)) := hcol.order.preorder
  have hot : IsForcingTop (forcingInverseCodePoset j (woodinIterationPrefix j))
      (forcingInverseCodeOrder j (woodinIterationPrefix j))
      (forcingInverseCodeTop j (woodinIterationPrefix j)) := hcol.tops.top
  have hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
      ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) := hcθ.system.order.preorder i hiθ
  have hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
      ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
      ((forcingCodet (woodinIterationPrefix θ)) ‘ i) := hcθ.system.tops.top i hiθ
  have hsplit : IsForcingSplitProjection ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
      ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
      (forcingInverseCodePoset j (woodinIterationPrefix j))
      (forcingInverseCodeOrder j (woodinIterationPrefix j))
      (forcingThreadCoordinate (forcingInverseCodePoset j (woodinIterationPrefix j)) i)
      (forcingThreadSection j (forcingCodeP (woodinIterationPrefix j))
        (forcingCodeπ (woodinIterationPrefix j)) (forcingCodeE (woodinIterationPrefix j)) i) := by
    have hh := woodinInverseCoordinate_split (θ := j) hsj hij
    rwa [hPval i hij, hRval i hij] at hh
  have hdj : d ‘ j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j :=
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 j hj
  have hdi : d ‘ i ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i :=
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 i hiθ
  -- the coordinate name of the descending sequence at stage `j`
  have hμname : IsForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
      (woodinBoundCoordinateName θ i f j) := by
    rw [woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)]
    exact woodinBoundCoordinateName_isName θ i f j
  intro r hr hrq b hb hbr hbe
  have hr2 : r ∈ twoStepConditions (forcingInverseCodePoset j (woodinIterationPrefix j))
      (forcingInverseCodeOrder j (woodinIterationPrefix j))
      (forcingInverseCollapseName j (woodinIterationPrefix j)
        (forcingInverseSourceCutoff j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
        (forcingInverseHartogsName j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
        (forcingInverseRestorationName j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j)))) ∅ := hPj ▸ hr
  obtain ⟨r', hr'T, τ, hτ, rfl, hcτ⟩ := (mem_twoStepConditions _ _ _ _ _).mp hr2
  have hr'lim : r' ∈ forcingInverseLimit j (forcingCodeP (woodinIterationPrefix j))
      (forcingCodeπ (woodinIterationPrefix j))
      (forcingCodeUniverse (woodinIterationPrefix j)) := hr'T
  have hbj : b ∈ (forcingCodeP (woodinIterationPrefix j)) ‘ i := (hPval i hij) ▸ hb
  have hproj : ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨r', τ⟩ₖ = r' ‘ i := by
    rw [woodinInverse_projection_value hs hj h0 hlim hinac hij hr, kpair.π₁_kpair]
  have hble : ⟨b, r' ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix j)) ‘ i := by
    rw [hRval i hij, ← hproj]
    exact hbr
  have hπmono : ∀ m ∈ i, ∀ x ∈ (forcingCodeP (woodinIterationPrefix j)) ‘ i,
      ∀ y ∈ (forcingCodeP (woodinIterationPrefix j)) ‘ i,
      ⟨x, y⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix j)) ‘ i →
      ⟨((forcingCodeπ (woodinIterationPrefix j)) ‘ ⟨m, i⟩ₖ) ‘ x,
        ((forcingCodeπ (woodinIterationPrefix j)) ‘ ⟨m, i⟩ₖ) ‘ y⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix j)) ‘ m := by
    intro m hm x hx y hy hxy
    exact (hcj.system.splitProjection (IsOrdinal.toIsTransitive.mem_trans hm hij) hij
      (IsOrdinal.toIsTransitive.transitive _ hm)).projection.monotone x hx y hy hxy
  set w := forcingThreadSplice j (forcingCodeπ (woodinIterationPrefix j))
    (forcingCodeL (woodinIterationPrefix j)) r' i b with hwdef
  have hw : w ∈ forcingInverseCodePoset j (woodinIterationPrefix j) :=
    forcingThreadSplice_mem hcj.system.split hcj.system.lifts hr'lim hij hbj hble
      hcj.subset_universe
  have hwr : ⟨w, r'⟩ₖ ∈ forcingInverseCodeOrder j (woodinIterationPrefix j) :=
    forcingThreadSplice_le hcj.system.split hcj.system.lifts hr'lim hij hbj hble
      hcj.subset_universe hπmono
  have hwi : w ‘ i = b := by
    rw [hwdef, forcingThreadSplice_value hij]
    exact forcingSpliceValue_self hcj.system.split hcj.system.lifts hr'lim hij hbj hble
  have hbd : ⟨b, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i :=
    hRi.2.2 b hb e he (d ‘ i) hdi hbe hed
  have hthread := woodinThread_inverse_coordinate hs hj h0 hlim hinac hd
  have hrqpair : ⟨⟨r', τ⟩ₖ, ⟨woodinQuotientBoundHistory θ i p f j,
      woodinBoundInverseTail θ i p f j⟩ₖ⟩ₖ ∈
      twoStepOrder (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j))
        (forcingInverseCollapseName j (woodinIterationPrefix j)
          (forcingInverseSourceCutoff j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseHartogsName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseRestorationName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j))))
        (reverseInclusionOrderName (forcingInverseCodePoset j (woodinIterationPrefix j))
          (forcingInverseCodeOrder j (woodinIterationPrefix j))
          (forcingInverseCollapseName j (woodinIterationPrefix j)
            (forcingInverseSourceCutoff j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseHartogsName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseRestorationName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j))))) ∅ := by
    rw [← hRj, ← woodinQuotientBoundRec_inverse hij hlim hinac]
    exact hrq
  have hr'hist : ⟨r', woodinQuotientBoundHistory θ i p f j⟩ₖ ∈
      forcingInverseCodeOrder j (woodinIterationPrefix j) := by
    simpa only [kpair.π₁_kpair] using
      ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hrqpair).2.2.1
  -- the spliced thread is below the thread `d` reads off at `j`
  have hwc : ⟨w, kpair.π₁ (d ‘ j)⟩ₖ ∈ forcingInverseCodeOrder j (woodinIterationPrefix j) := by
    apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
    refine ⟨hw, woodinInverse_first_mem hs hj h0 hlim hinac hdj, ?_⟩
    intro m hm
    have hmθ : m ∈ θ := hsub m hm
    let := IsOrdinal.of_mem hm
    rw [← hthread.2 m hm, hwdef]
    by_cases hmi : m ∈ i
    · rw [forcingThreadSplice_value hm]
      simp only [forcingSpliceValue, ite_eq_left hmi]
      have hmi' : m ⊆ i := IsOrdinal.toIsTransitive.transitive _ hmi
      rw [hRval m hm, hπval m hm i hij,
        ← woodinInverseThread_project hs hmθ hiθ hmi' hd]
      exact (hcθ.system.splitProjection hmθ hiθ hmi').projection.monotone b hb (d ‘ i) hdi hbd
    · have him : i ⊆ m := by
        rcases IsOrdinal.mem_trichotomy i m with h1 | h1 | h1
        · exact IsOrdinal.toIsTransitive.transitive _ h1
        · exact h1 ▸ subset_refl _
        · exact absurd h1 hmi
      rw [forcingThreadSplice_coordinate hm him, hRval m hm, hLval i hij m hm]
      have hr'm : r' ‘ m ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ m := by
        rw [← hPval m hm]
        exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hr'lim).2.1 m hm
      have hr'mq : ⟨r' ‘ m, woodinQuotientBoundRec θ i p f m⟩ₖ ∈
          (forcingCodeR (woodinIterationPrefix θ)) ‘ m := by
        rw [← hPval m hm] at hr'm
        rw [← hRval m hm, ← woodinQuotientBoundHistory_value (θ := θ) (i := i) (p := p) (f := f) hm]
        exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hr'hist).2.2 m hm
      have hbm : ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, m⟩ₖ) ‘ (r' ‘ m)⟩ₖ ∈
          (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by
        rw [← hπval i hij m hm,
          forcingInverseLimit_project_subset hcj.system.split hr'lim hij hm him, ← hproj]
        exact hbr
      exact hprev m hm him (r' ‘ m) hr'm hr'mq b hb hbm hbe
  have hwd : ⟨(forcingThreadCoordinate (forcingInverseCodePoset j (woodinIterationPrefix j)) i)
      ‘ w, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by
    rw [forcingThreadCoordinate_value hw, hwi]
    exact hbe
  have hn : woodinQuotientBoundHistory θ i p f j ∈
      atomicEquality (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j))
        (woodinBoundInverseTail θ i p f j)
        (forcingSelectedUnion (forcingInverseCodePoset j (woodinIterationPrefix j))
          (forcingInverseCodeOrder j (woodinIterationPrefix j))
          (forcingInverseCodeTop j (woodinIterationPrefix j))
          (twoStepNames (forcingInverseCollapseName j (woodinIterationPrefix j)
            (forcingInverseSourceCutoff j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseHartogsName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseRestorationName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))) ∅)
          (twoStepTailSelector (forcingInverseCodePoset j (woodinIterationPrefix j))
            (forcingInverseCodeOrder j (woodinIterationPrefix j))
            (forcingInverseCollapseName j (woodinIterationPrefix j)
              (forcingInverseSourceCutoff j (woodinIterationPrefix j)
                (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
              (forcingInverseHartogsName j (woodinIterationPrefix j)
                (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
              (forcingInverseRestorationName j (woodinIterationPrefix j)
                (woodinLimitCardinal (woodinIterationCardinalPrefix j)))) ∅)
          (nameAction (forcingThreadSection j (forcingCodeP (woodinIterationPrefix j))
            (forcingCodeπ (woodinIterationPrefix j)) (forcingCodeE (woodinIterationPrefix j)) i)
            (woodinBoundCoordinateName θ i f j))) := by
    have hh := (hnorm hij).2 hlim hinac
    unfold woodinBoundInverseRawTail at hh
    exact hh
  have hLift : ((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨⟨r', τ⟩ₖ, b⟩ₖ = ⟨w, τ⟩ₖ := by
    rw [woodinInverse_lift_value hs hj hij hlim hinac hr hb]
    simp only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair, kpair.π₂_kpair,
      forcingLimitLiftColumn_value hij, forcingLimitLift_value hr'T hbj, hwdef]
  rw [hRj, hLift]
  refine twoStepStronger_le_selected_of_normalization hRi hti hUpre hot hsplit hiter
    ⟨woodinBoundCoordinateName θ i f j, hμname⟩ hrqpair (hPj ▸ hdj) hw hwr hwc he hwd hn
    ?_ ?_
  · intro G hG heG
    simpa only [hPj] using hdecide G hG heG hRi hti ⟨woodinBoundCoordinateName θ i f j, hμname⟩ rfl
  · intro H hH _
    exact ForcingContext.reverseOrderName_value _ ⟨_, hiter.posetName⟩

end ZFVP
