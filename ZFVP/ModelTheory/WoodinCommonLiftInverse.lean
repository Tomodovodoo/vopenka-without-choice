import ZFVP.ModelTheory.WoodinCommonLiftInverseFirst
import ZFVP.ModelTheory.WoodinSelectedThreadDecision
import ZFVP.ModelTheory.WoodinBoundNormalization
import ZFVP.ModelTheory.NormalizedUnionStrongerBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem woodinCommonLiftBoundAt_inverse [Countable V] {δ θ i j p z d : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (hi : i ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hz : z ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hd : d ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hdz : ⟨d, z ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hqnext : woodinQuotientBoundRec θ i p f.val j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hnorm : IsWoodinBoundNormalizationAt θ i p f.val j)
    (hselected : IsWoodinSelectedThreadDecision θ i f.val z d)
    (hprev : ∀ k ∈ j, IsWoodinCommonLiftBoundAt θ i p f.val z d k) :
    IsWoodinCommonLiftBoundAt θ i p f.val z d j := by
  let := IsOrdinal.of_mem hj
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have h0j : (∅ : V) ∈ j := (IsOrdinal.subset_iff.mp (empty_subset j)).resolve_left
    (fun he ↦ h0 he.symm)
  let s := woodinIterationPrefix j
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix j)
  let c := forcingInverseSourceCutoff j s γ
  let T := forcingInverseCodePoset j s
  let U := forcingInverseCodeOrder j s
  let o := forcingInverseCodeTop j s
  let Q := forcingInverseCollapseName j s c (forcingInverseHartogsName j s γ)
    (forcingInverseRestorationName j s γ)
  let S := reverseInclusionOrderName T U Q
  let τ := forcingThreadCoordinate T i
  let E := forcingThreadSection j (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) i
  let μ : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    ⟨woodinBoundCoordinateName θ i f.val j, woodinBoundCoordinateName_isName _ _ _ _⟩
  have hssub := fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj)
  have h := (woodinIterationPrefix_of_stages hssub).code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have col := h.system.inverseColumn h0j h.subset_universe
  have hU : IsForcingPreorder T U := col.order.preorder
  have hot : IsForcingTop T U o := col.tops.top
  have hbaseR := (hs i hiθ).code.system.order.preorder i (mem_succ_self i)
  have hbaseo := (hs i hiθ).code.system.tops.top i (mem_succ_self i)
  have hsplit := woodinInverseCoordinate_split hssub hi
  rw [woodinIterationPrefix_poset_value hssub hi (mem_succ_self i),
    woodinIterationPrefix_order_value hssub hi (mem_succ_self i)] at hsplit
  have hQ : IsForcingName T Q := forcingSaturatedName_isName _ _ _ _
  have hS : IsForcingName T S := reverseInclusionOrderName_isName _ _ _
  have hN : ∀ ν ∈ twoStepNames Q ∅, IsForcingName T ν := by
    intro ν hν
    rcases mem_union_iff.mp hν with hν | hν
    · obtain ⟨q, hq⟩ := mem_domain_iff.mp hν
      exact forcingName_subname hQ hq
    · exact (mem_singleton_iff.mp hν).symm ▸ empty_forcingName _
  have hrec := woodinIterationRec_inverse h0 hlim hinac
  have hPnext : (forcingCodeP (woodinIterationPrefix θ)) ‘ j = twoStepConditions T U Q ∅ := by
    rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
      forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingFamilyNext_new, T, U, Q, c, γ, s, forcingInverseCodePoset, forcingInverseCodeOrder]
  have hRnext : (forcingCodeR (woodinIterationPrefix θ)) ‘ j = twoStepOrder T U Q S ∅ := by
    rw [woodinIterationPrefix_order_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
      forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeR_code, forcingFamilyNext_new, T, U, Q, S, c, γ, s, forcingInverseCodePoset, forcingInverseCodeOrder]
  intro hij r hr hrq b hb hbr hbd
  obtain ⟨r₀, hr₀, σ, hσ, heqr, hrσ⟩ := (mem_twoStepConditions _ _ _ _ _).mp (hPnext ▸ hr)
  subst r
  let l := ((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨⟨r₀, σ⟩ₖ, b⟩ₖ
  let w := kpair.π₁ l
  have hl := hcθ.system.lifts.lift i hiθ j hj hij _ hr b hb hbr
  have hwl : l = ⟨w, σ⟩ₖ := by
    dsimp only [l, w]
    rw [woodinInverse_lift_value hs hj hi hlim hinac hr hb]
    simp only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair, kpair.π₂_kpair]
  have hw : w ∈ T := woodinInverse_first_mem hs hj h0 hlim hinac hl.1
  have hwσ : ⟨w, σ⟩ₖ ∈ twoStepConditions T U Q ∅ := hwl ▸ (hPnext ▸ hl.1)
  have hwr : ⟨w, r₀⟩ₖ ∈ U := by
    have hh := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp (hRnext ▸ hl.2.1)).2.2.1
    simpa only [kpair.π₁_kpair] using hh
  have hwz : ⟨w, kpair.π₁ (z ‘ j)⟩ₖ ∈ U :=
    woodinCommonLift_inverse_first_le hs hj hi hlim hinac hz hd hdz hqnext hprev hr hrq hb hbr hbd
  have hwd : ⟨τ ‘ w, d⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i := by
    have he : τ ‘ w = b := by
      rw [forcingThreadCoordinate_value hw]
      exact (woodinInverse_projection_value hs hj h0 hlim hinac hi hl.1).symm.trans hl.2.2
    rw [he, ← woodinIterationPrefix_order_value hs hiθ (mem_succ_self i)]
    exact hbd
  have hd' : d ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := by
    rwa [woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)] at hd
  let q := woodinQuotientBoundHistory θ i p f.val j
  let ν := woodinBoundInverseTail θ i p f.val j
  have hn : q ∈ atomicEquality T U ν
      (forcingSelectedUnion T U o (twoStepNames Q ∅) (twoStepTailSelector T U Q ∅)
        (nameAction E μ.val)) := (hnorm hi).2 hlim hinac
  have hrq' : ⟨⟨r₀, σ⟩ₖ, ⟨q, ν⟩ₖ⟩ₖ ∈ twoStepOrder T U Q S ∅ := by
    rw [hRnext, woodinQuotientBoundRec_inverse hi hlim hinac] at hrq
    exact hrq
  have hznext := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hz).2.1 j hj
  have hh := twoStepStronger_le_selected_of_normalization_of_names hbaseR hbaseo hU hot hsplit hQ hS hN μ
    hrq' (hPnext ▸ hznext) hw hwσ hwr hwz hd' hwd hn ?_ ?_
  · change ⟨l, z ‘ j⟩ₖ ∈ _
    rw [hRnext, hwl]
    exact hh
  · intro G hG hdG
    let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
    have hh := A.woodinCoordinate_selected hs hj rfl rfl rfl hz hselected hdG f rfl
    simpa only [hPnext] using hh
  · intro H hH _
    let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
    exact C.reverseOrderName_value ⟨Q, hQ⟩

end ZFVP
