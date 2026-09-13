import ZFVP.ModelTheory.WoodinCommonLiftProjection
import ZFVP.ModelTheory.WoodinSuccessorLiftCoordinates
import ZFVP.ModelTheory.WoodinSelectedThreadDecision
import ZFVP.ModelTheory.WoodinBoundNormalization
import ZFVP.ModelTheory.NormalizedUnionStrongerBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 800000 in
theorem woodinCommonLiftBoundAt_successor [Countable V] {δ θ i k p z d : V} [IsOrdinal θ]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l))) (hk : succ k ∈ θ) (hi : i ∈ succ k)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hz : z ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hd : d ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hdz : ⟨d, z ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hqnext : woodinQuotientBoundRec θ i p f.val (succ k) ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k))
    (hnorm : IsWoodinBoundNormalizationAt θ i p f.val (succ k))
    (hselected : IsWoodinSelectedThreadDecision θ i f.val z d)
    (hprev : IsWoodinCommonLiftBoundAt θ i p f.val z d k) :
    IsWoodinCommonLiftBoundAt θ i p f.val z d (succ k) := by
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
  intro hij r hr hrq b hb hbr hbd
  obtain ⟨r₀, hr₀, σ, hσ, heqr, hrσ⟩ := (mem_twoStepConditions _ _ _ _ _).mp (hPnext ▸ hr)
  subst r
  let l := ((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨⟨r₀, σ⟩ₖ, b⟩ₖ
  let w := kpair.π₁ l
  have hl := hcθ.system.lifts.lift i hiθ (succ k) hk hij _ hr b hb hbr
  have hwl : l = ⟨w, σ⟩ₖ := by
    dsimp only [l, w]
    rw [woodinSuccessor_lift_value hs hk hi hr hb]
    simp only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair, kpair.π₂_kpair]
  have hw : w ∈ T := by
    have hh := hcθ.system.split.projMaps k hkθ (succ k) hk
      (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)) _ hl.1
    rw [woodinSuccessor_projection_first hs hk hl.1, hPk] at hh
    exact hh
  have hwr : ⟨w, r₀⟩ₖ ∈ U := by
    have hh := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp (hRnext ▸ hl.2.1)).2.2.1
    simpa only [kpair.π₁_kpair] using hh
  have hqp : ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, succ k⟩ₖ) ‘
      (woodinQuotientBoundRec θ i p f.val (succ k)) = q := by
    rw [woodinSuccessor_projection_first hs hk hqnext, woodinQuotientBoundRec_successor hi,
      kpair.π₁_kpair]
  have hwz : ⟨w, kpair.π₁ (z ‘ (succ k))⟩ₖ ∈ U := by
    have hh := woodinCommonLift_project_le hs hk hi (mem_succ_self k) hz hd hdz hqnext
      hqp hprev hr hrq hb hbr hbd
    rw [woodinSuccessor_projection_first hs hk hl.1,
      ← woodinInverseThread_successor_first hs hk hz, hRk] at hh
    exact hh
  have hwd : ⟨τ ‘ w, d⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i := by
    have he : τ ‘ w = b := by
      rw [← hτeq]
      exact (woodinSuccessor_projection_comp hs hk hi hl.1).trans hl.2.2
    rw [he, ← woodinIterationPrefix_order_value hs hiθ (mem_succ_self i)]
    exact hbd
  have hd' : d ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := by
    rwa [woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)] at hd
  let ν := woodinBoundSuccessorTail θ i p f.val k
  have hn : q ∈ atomicEquality T U ν
      (forcingSelectedUnion T U o (twoStepNames Qs ∅) (twoStepTailSelector T U Qs ∅)
        (nameAction E μ.val)) := by
    have hh := (hnorm hi).1 (by rw [sUnion_succ_of_transitive])
    simpa only [sUnion_succ_of_transitive, woodinBoundSuccessorRawTail] using hh
  have hrq' : ⟨⟨r₀, σ⟩ₖ, ⟨q, ν⟩ₖ⟩ₖ ∈ twoStepOrder T U Qs S ∅ := by
    rw [hRnext, woodinQuotientBoundRec_successor hi] at hrq
    exact hrq
  have hznext := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hz).2.1 (succ k) hk
  have hh := twoStepStronger_le_selected_of_normalization hbaseR hbaseo hU hot hsplit hiter μ
    hrq' (hPnext ▸ hznext) hw hwr hwz hd' hwd hn ?_ ?_
  · change ⟨l, z ‘ (succ k)⟩ₖ ∈ _
    rw [hRnext, hwl]
    exact hh
  · intro G hG hdG
    let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
    have hh := A.woodinCoordinate_selected hs hk rfl rfl rfl hz hselected hdG f rfl
    simpa only [hPnext] using hh
  · intro H hH _
    let C : ForcingContext V := ⟨T, U, o, H, hU, hot, hH⟩
    exact C.reverseOrderName_value ⟨Qs, hiter.posetName⟩

end ZFVP
