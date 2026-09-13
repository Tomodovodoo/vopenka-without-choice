import ZFVP.ModelTheory.NormalizedUnionStrongerBound
import ZFVP.ModelTheory.WoodinSuccessorLiftCoordinates
import ZFVP.ModelTheory.WoodinBoundSuccessorStep

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 1000000 in
/-- Raw order comparison at a successor coordinate of the canonical quotient bound.
The lift of a condition `r` below the candidate at `succ k`, taken below a base condition `b`,
is below the coordinate `d ‘ (succ k)` of the selected ground thread `d`.
The candidate at `succ k` is the two-step condition built from the candidate at `k` and the
new tail, so the comparison reduces to the generic two-step statement
`twoStepStronger_le_selected_of_normalization`, whose first-coordinate premise is the same
comparison one coordinate down (`hprev`). -/
theorem woodinRawLift_successor [Countable V] {δ θ i k p f d e : V} [IsOrdinal θ]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hk : succ k ∈ θ) (hik : i ∈ succ k)
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hmem : ∀ l ∈ succ (succ k), woodinQuotientBoundRec θ i p f l ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ l)
    (hnorm : IsWoodinBoundNormalizationAt θ i p f (succ k))
    (hprev : ∀ a ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ k,
      ⟨a, woodinQuotientBoundRec θ i p f k⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ k →
      ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
        ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, k⟩ₖ) ‘ ⟨a, b⟩ₖ, d ‘ k⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ k)
    (hdecide : ∀ (G : Set V) (hG : IsExternalForcingGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G)
      (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
      (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G →
      let A : ForcingContext V := ⟨_, _, _, G, hR, ho, hG⟩
      let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f (succ k),
        woodinBoundCoordinateName_isName θ i f (succ k)⟩
      ∃ X a : A.Model,
        A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k)) ^ X ∧
          a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ (succ k))) :
    ∀ r ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k),
      ⟨r, woodinQuotientBoundRec θ i p f (succ k)⟩ₖ
        ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ (succ k) →
      ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
        ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, succ k⟩ₖ) ‘ r⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨r, b⟩ₖ, d ‘ (succ k)⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ (succ k) := by
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem (mem_succ_self k)
  let := IsOrdinal.of_mem hik
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hik hk
  have hkθ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hiksub : i ⊆ k := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hik)
  have hssub := fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hk)
  have hhist := woodinIterationHistory_of_stages hssub
  have he := woodinIterationPrefix_successor hhist
  let s := woodinIterationPrefix (succ k)
  let K := woodinIterationCardinalPrefix (succ k)
  let T := (forcingCodeP s) ‘ k
  let U := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := K ‘ k
  let c := woodinPrefixCutoff T U o κ
  let τ := (forcingCodeπ s) ‘ ⟨i, k⟩ₖ
  let E := (forcingCodeE s) ‘ ⟨i, k⟩ₖ
  let q := woodinQuotientBoundRec θ i p f k
  let ν := woodinBoundSuccessorTail θ i p f k
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
  have hPi := woodinIterationPrefix_poset_value hssub hik (mem_succ_self i)
  have hRi := woodinIterationPrefix_order_value hssub hik (mem_succ_self i)
  have hbaseR := (hs i hiθ).code.system.order.preorder i (mem_succ_self i)
  have hbaseo := (hs i hiθ).code.system.tops.top i (mem_succ_self i)
  have hsplit := h.code.system.splitProjection hik (mem_succ_self k) hiksub
  rw [hPi, hRi] at hsplit
  have hPiθ : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)
  have hRiθ : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_order_value hs hiθ (mem_succ_self i)
  have hPk : (forcingCodeP (woodinIterationPrefix θ)) ‘ k = T := by
    simpa only [T, s, he.1] using woodinIterationPrefix_poset_value hs hkθ (mem_succ_self k)
  have hRk : (forcingCodeR (woodinIterationPrefix θ)) ‘ k = U := by
    simpa only [U, s, he.1] using woodinIterationPrefix_order_value hs hkθ (mem_succ_self k)
  have hτeq : (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, k⟩ₖ = τ := by
    simpa only [τ, s, he.1] using woodinIterationPrefix_projection_value hs hkθ hik (mem_succ_self k)
  have hPnext : (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k) = twoStepConditions T U Qs ∅ := by
    rw [woodinIterationPrefix_poset_value hs hk (mem_succ_self _),
      woodinIterationRec_successor_of_history hhist, kpair.π₁_kpair]
    simp only [woodinIterationSuccessor, forcingSuccessorCode_poset, Qs, c, T, U, o, κ, s, K, he.1, he.2]
  have hRnext : (forcingCodeR (woodinIterationPrefix θ)) ‘ (succ k) = twoStepOrder T U Qs S ∅ := by
    rw [woodinIterationPrefix_order_value hs hk (mem_succ_self _),
      woodinIterationRec_successor_of_history hhist, kpair.π₁_kpair]
    simp only [woodinIterationSuccessor, forcingSuccessorCode_order, Qs, S, c, T, U, o, κ, s, K, he.1, he.2]
  let μ : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    ⟨woodinBoundCoordinateName θ i f (succ k), woodinBoundCoordinateName_isName _ _ _ _⟩
  -- the normalization clause of the successor step
  have hn : q ∈ atomicEquality T U ν
      (forcingSelectedUnion T U o (twoStepNames Qs ∅) (twoStepTailSelector T U Qs ∅)
        (nameAction E μ.val)) := by
    have hh := (hnorm hik).1 (by rw [sUnion_succ_of_transitive])
    simp only [sUnion_succ_of_transitive] at hh
    unfold woodinBoundSuccessorRawTail at hh
    dsimp only at hh
    exact hh
  -- the collapse names are read off the saturated Woodin prefix iterand
  have horder : ∀ (H : Set V) (hH : IsExternalForcingGeneric T U H), ∀ w, w ∈ H →
      let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
      C.ofName ⟨S, hiter.orderName⟩ = reverseInclusionOrder (C.ofName ⟨Qs, hiter.posetName⟩) := by
    intro H hH _ _
    let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
    have h1 : C.ofName ⟨Qs, hiter.posetName⟩ = woodinCollapse (C.check κ) (C.check c) :=
      C.saturatedWoodinPosetName_value hci hT hκsub
    have h2 : C.ofName ⟨S, hiter.orderName⟩ = woodinCollapseOrder (C.check κ) (C.check c) :=
      C.saturatedWoodinOrderName_value hci hT hκsub
    show C.ofName ⟨S, hiter.orderName⟩ = reverseInclusionOrder (C.ofName ⟨Qs, hiter.posetName⟩)
    exact h2.trans (congrArg reverseInclusionOrder h1.symm)
  intro r hr hrq b hb hbπ hbe
  -- the base condition `e` is a condition of the ground poset
  have heB : e ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := by
    have hbe' : ⟨b, e⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i := by
      rwa [hRiθ] at hbe
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_prod_iff.mp (hbaseR.1 _ hbe')
    have hey : e = y := (kpair_inj hxy).2
    rw [hey]
    exact hy
  -- split `r` into its two coordinates
  have hrT : r ∈ twoStepConditions T U Qs ∅ := by rwa [hPnext] at hr
  obtain ⟨r1, hr1, σ, hσ, hreq, hrm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hrT
  subst hreq
  have hrqT : ⟨⟨r1, σ⟩ₖ, ⟨q, ν⟩ₖ⟩ₖ ∈ twoStepOrder T U Qs S ∅ := by
    rw [woodinQuotientBoundRec_successor hik, hRnext] at hrq
    exact hrq
  have hr1θ : r1 ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ k := by rw [hPk]; exact hr1
  have hr1q : ⟨r1, q⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ k := by
    rw [hRk]
    simpa only [kpair.π₁_kpair] using ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hrqT).2.2.1
  -- the projection of `r` to coordinate `i` factors through coordinate `k`
  have hproj : ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, k⟩ₖ) ‘ r1 =
      ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨r1, σ⟩ₖ := by
    simpa only [kpair.π₁_kpair] using woodinSuccessor_projection_comp hs hk hik hr
  have hle : ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, k⟩ₖ) ‘ r1⟩ₖ
      ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by rw [hproj]; exact hbπ
  -- the lift at coordinate `k`
  have hlift := hcθ.system.lifts.lift i hiθ k hkθ hiksub r1 hr1θ b hb hle
  -- rewrite the lift at `succ k` as a two-step condition
  rw [woodinSuccessor_lift_value hs hk hik hr hb, successorForcingLift_section, hRnext]
  refine twoStepStronger_le_selected_of_normalization (d := e) (r := r1) (q := q) (ν := ν)
    (σ := σ) (c := d ‘ (succ k)) hbaseR hbaseo hU hot hsplit hiter μ hrqT ?_ ?_ ?_ ?_ heB ?_ hn ?_ ?_
  · have hdk : d ‘ (succ k) ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k) :=
      ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 (succ k) hk
    rwa [hPnext] at hdk
  · rw [← hPk]; exact hlift.1
  · rw [← hRk]; exact hlift.2.1
  · rw [woodinInverseThread_successor_first hs hk hd, ← hRk]
    exact hprev r1 hr1θ hr1q b hb hle hbe
  · have hτw : τ ‘ (((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, k⟩ₖ) ‘ ⟨r1, b⟩ₖ) = b := by
      rw [← hτeq]; exact hlift.2.2
    rw [hτw, ← hRiθ]
    exact hbe
  · intro G hG heG
    have hh := hdecide G hG hbaseR hbaseo heG
    dsimp only at hh ⊢
    rwa [hPnext] at hh
  · intro H hH hwH
    exact horder H hH _ hwH

end ZFVP
