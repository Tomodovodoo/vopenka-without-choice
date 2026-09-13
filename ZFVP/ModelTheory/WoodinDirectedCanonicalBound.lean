import ZFVP.ModelTheory.WoodinDirectedBoundSemantics
import ZFVP.ModelTheory.WoodinRawHistoryBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ i p f α : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ)
include hs hi

theorem woodinQuotientBoundAt_base_of_directed [Countable V] [IsOrdinal α]
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α) :
    IsWoodinQuotientBoundAt θ i p f.val α i := by
  let := IsOrdinal.of_mem hi
  have hPi := woodinIterationPrefix_poset_value hs hi (mem_succ_self i)
  have hRi := woodinIterationPrefix_order_value hs hi (mem_succ_self i)
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hm := hc.system.functions.projection i hi i hi (subset_refl i)
  have he : ∀ q ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
      ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, i⟩ₖ) ‘ q = q := by
    intro q hq
    exact hc.system.split.projId hi (hPi.symm ▸ hq)
  apply (woodinQuotientBoundAt_iff_generics hs hi hi (subset_refl _) hp f).mpr
  refine ⟨?_, ?_⟩
  · rw [woodinQuotientBoundRec_base, hPi]
    exact hp
  · intro G hG hpG
    let A : ForcingContext V := ⟨_, _, _, G,
      (hs i hi).code.system.order.preorder i (mem_succ_self i),
      (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
    have hdesc := woodinQuotientDirectedFamily_semantics hs hi f hf G hG hpG
    have hd := A.woodinCoordinate_directed hs hi hi (subset_refl _) rfl rfl rfl f hdesc
    rw [hPi, hRi] at hd
    rw [hPi] at hm
    have hpQ : A.check p ∈ A.projectionQuotient A.P ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, i⟩ₖ) :=
      (A.check_mem_projectionQuotient_iff hm).mpr ⟨hp, (he p hp).symm ▸ hpG⟩
    dsimp only
    rw [woodinQuotientBoundRec_base, hPi, hRi]
    exact ⟨hpQ, fun a ha ↦ A.identityQuotient_separative hm he hpQ (function_value_mem hd.1 ha)⟩

end ZFVP

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem woodinQuotientBoundAt_direct_of_directed [Countable V] {δ θ i p α j : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hi : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α)
    (hprev : ∀ k ∈ j, IsWoodinQuotientBoundAt θ i p f.val α k) :
    IsWoodinQuotientBoundAt θ i p f.val α j := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hj
  have hij : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hi
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have hmem : woodinQuotientBoundRec θ i p f.val j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j := by
    apply woodinQuotientBound_direct_mem hs hj hi hlim hinac hα hp f ?_ (fun k hk ↦ (hprev k hk).1)
    intro A hP hR ho hpG g hg
    obtain ⟨P, R, o, G, hR', ho', hG⟩ := A
    dsimp only at hP hR ho
    subst P R o
    have he : g = f := Subtype.ext hg
    subst g
    exact mem_function_of_mem_function_of_subset
      (woodinQuotientDirectedFamily_semantics hs hiθ f hf G hG hpG).1 sep_subset
  apply (woodinQuotientBoundAt_iff_generics hs hiθ hj hij hp f).mpr
  refine ⟨hmem, ?_⟩
  intro G hG hpG
  let A : ForcingContext V := ⟨_, _, _, G,
    (hs i hiθ).code.system.order.preorder i (mem_succ_self i),
    (hs i hiθ).code.system.tops.top i (mem_succ_self i), hG⟩
  let μ (k : V) : ForcingName A.P :=
    ⟨woodinBoundCoordinateName θ i f.val k, woodinBoundCoordinateName_isName _ _ _ _⟩
  have hdesc := woodinQuotientDirectedFamily_semantics hs hiθ f hf G hG hpG
  have hfun := mem_function_of_mem_function_of_subset hdesc.1 sep_subset
  have hsj := fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj)
  have hcj := (woodinIterationPrefix_of_stages hsj).code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have hproj := hcθ.system.projection hiθ hj hij
  rw [woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i),
    woodinIterationPrefix_order_value hs hiθ (mem_succ_self i)] at hproj
  have hqb : ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘
      (woodinQuotientBoundRec θ i p f.val j) = p := by
    rw [woodinQuotientBoundRec_projects_direct hs hj hi hi hlim hinac hmem,
      woodinQuotientBoundRec_base]
  have hqG : A.check (woodinQuotientBoundRec θ i p f.val j) ∈
      A.projectionQuotient ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
        ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) :=
    (A.check_mem_projectionQuotient_iff hproj.maps).mpr ⟨hmem, hqb.symm ▸ hpG⟩
  refine ⟨hqG, ?_⟩
  intro a ha
  obtain ⟨d, hd, had⟩ := (A.mem_check_iff _ _).mp (function_value_mem hfun ha)
  have hv (k : V) (hk : k ∈ θ) : (A.ofName (μ k)) ‘ a = A.check (d ‘ k) :=
    A.woodinCoordinate_value hs hk rfl rfl rfl f hfun ha hd had
  change ⟨A.check (woodinQuotientBoundRec θ i p f.val j), (A.ofName (μ j)) ‘ a⟩ₖ ∈ _
  rw [hv j hj]
  have hstage := A.woodinCoordinate_directed hs hiθ hj hij rfl rfl rfl f hdesc
  have hdG := function_value_mem hstage.1 ha
  change (A.ofName (μ j)) ‘ a ∈ _ at hdG
  rw [hv j hj] at hdG
  let D := forcingDirectLimit j (forcingCodeP (woodinIterationPrefix j))
    (forcingCodeπ (woodinIterationPrefix j)) (forcingCodeE (woodinIterationPrefix j))
    (forcingCodeUniverse (woodinIterationPrefix j))
  have hrec := woodinIterationRec_direct h0 hlim hinac
  have hPj : (forcingCodeP (woodinIterationPrefix θ)) ‘ j = D := by
    rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [forcingDirectCode, forcingThreadCode_poset, D]
  have hRj : (forcingCodeR (woodinIterationPrefix θ)) ‘ j =
      forcingThreadOrder j (forcingCodeR (woodinIterationPrefix j)) D := by
    rw [woodinIterationPrefix_order_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [forcingDirectCode, forcingThreadCode_order, D]
  have hπj : (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ = forcingThreadCoordinate D i := by
    rw [woodinIterationPrefix_projection_value hs hj (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self j),
      hrec, kpair.π₁_kpair]
    simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeπ_code,
      forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi, D]
  rw [hPj, hRj, hπj]
  rw [hPj, hπj] at hqG hdG
  apply A.directLimit_quotient_separative_of_coordinates hcj.system.split hi
    (woodinIterationPrefix_poset_value hsj hi (mem_succ_self i)).symm hcj.subset_universe
    (fun k hk l hl hkl ↦ hcj.system.splitProjection hk hl hkl) hqG hdG
  intro k hk hik
  have hkθ := IsOrdinal.toIsTransitive.mem_trans hk hj
  have hb := ((woodinQuotientBoundAt_iff_generics hs hiθ hkθ hik hp f).mp (hprev k hk)).2 G hG hpG
  have hba := hb.2 a ha
  change ⟨A.check (woodinQuotientBoundRec θ i p f.val k), (A.ofName (μ k)) ‘ a⟩ₖ ∈ _ at hba
  rw [hv k hkθ] at hba
  rw [woodinQuotientBoundRec_direct hi hlim hinac, woodinQuotientBoundHistory_value hk,
    ← (woodinThread_direct_coordinate hs hj h0 hlim hinac hd).2 k hk]
  have hext := woodinIterationPrefix_extends (IsOrdinal.toIsTransitive.transitive _ hj)
  rw [hcj.tableP.value_of_subset hcθ.tableP hext.subP hk,
    hcj.tableR.value_of_subset hcθ.tableR hext.subR hk,
    hcj.tableπ.value_of_subset hcθ.tableπ hext.subπ (mem_prod_iff.mpr ⟨i, hi, k, hk, rfl⟩)]
  exact hba

end ZFVP

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinQuotientBoundAt_base_normalized_of_directed [Countable V] {δ θ i p α : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α) :
    IsWoodinNormalizedQuotientBoundAt θ i p f.val α i :=
  ⟨woodinQuotientBoundAt_base_of_directed hs hi hp f hf, woodinBoundNormalizationAt_base θ i p f.val⟩

theorem woodinQuotientBoundAt_direct_normalized_of_directed [Countable V] {δ θ i p α j : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hi : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α)
    (hprev : ∀ k ∈ j, IsWoodinQuotientBoundAt θ i p f.val α k) :
    IsWoodinNormalizedQuotientBoundAt θ i p f.val α j :=
  ⟨woodinQuotientBoundAt_direct_of_directed hs hj hi hlim hinac hα hp f hf hprev,
    woodinBoundNormalizationAt_direct hlim hinac⟩

end ZFVP

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 1000000 in
theorem woodinQuotientBoundAt_successor_normalized_of_directed [Countable V] {δ θ i k p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hk : succ k ∈ θ) (hi : i ∈ succ k)
    (hclosure : HasWoodinQuotientClosure (succ k) (woodinIterationPrefix (succ k))
      (woodinIterationCardinalPrefix (succ k)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α)
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
      IsForcingDirectedFamily (A.projectionQuotient (twoStepConditions T U Qs ∅) π)
        (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Qs ∅) π)
          (A.projectionQuotientOrder (twoStepConditions T U Qs ∅) (twoStepOrder T U Qs S ∅) π))
        (A.check α) (A.ofName μ) ∧
      (∀ a ∈ A.check α, ⟨A.check q, (compose (A.ofName μ) (A.check (twoStepProjection T U Qs ∅))) ‘ a⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) ∧
      InternalDependentChoiceAt (A.check α) ∧
      IsForcingClosedThrough (A.projectionQuotient T τ)
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) (A.check α) := by
    let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
    have hd := woodinQuotientDirectedFamily_semantics hs hiθ f hf G hG hpG
    have hfun := mem_function_of_mem_function_of_subset hd.1 sep_subset
    have hnext := A.woodinCoordinate_directed hs hiθ hk (IsOrdinal.toIsTransitive.transitive _ hi)
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
    transported_local_directed_union_pair_mem hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
      hπfull.maps hcomp hdata (fun H hH _ ↦ hcollapse H hH)
  have hqnext : woodinQuotientBoundRec θ i p f.val (succ k) = ⟨q, ν⟩ₖ := by
    rw [woodinQuotientBoundRec_successor hi]
    unfold woodinBoundSuccessorTail woodinBoundTailName
    dsimp only
    simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
    rfl
  have hnorm : q ∈ atomicEquality T U ν
      (forcingSelectedUnion T U o (twoStepNames Qs ∅) (twoStepTailSelector T U Qs ∅) (nameAction E μ.val)) :=
    transported_local_directed_union_normalization hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
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
      apply A.local_directed_union_quotient_separative_bound hsplit hU hot hiter hπfull.maps hcomp μ hdesc hbound
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
theorem woodinQuotientBoundAt_successor_of_directed [Countable V] {δ θ i k p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hk : succ k ∈ θ) (hi : i ∈ succ k)
    (hclosure : HasWoodinQuotientClosure (succ k) (woodinIterationPrefix (succ k))
      (woodinIterationCardinalPrefix (succ k)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α)
    (hprev : ∀ l ∈ succ k, IsWoodinQuotientBoundAt θ i p f.val α l) :
    IsWoodinQuotientBoundAt θ i p f.val α (succ k) :=
  (woodinQuotientBoundAt_successor_normalized_of_directed hs hk hi hclosure hα hp f hf hprev).1

end ZFVP

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 1000000 in
theorem woodinQuotientBoundAt_inverse_normalized_of_directed [Countable V] {δ θ i j p α : V}
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
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α)
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
      IsForcingDirectedFamily (A.projectionQuotient (twoStepConditions T U Qs ∅) π)
        (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Qs ∅) π)
          (A.projectionQuotientOrder (twoStepConditions T U Qs ∅) (twoStepOrder T U Qs S ∅) π))
        (A.check α) (A.ofName μ) ∧
      (∀ a ∈ A.check α, ⟨A.check q, (compose (A.ofName μ) (A.check (twoStepProjection T U Qs ∅))) ‘ a⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) ∧
      InternalDependentChoiceAt (A.check α) ∧
      IsForcingClosedThrough (A.projectionQuotient T τ)
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) (A.check α) := by
    let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
    have hd := woodinQuotientDirectedFamily_semantics hs hiθ f hf G hG hpG
    have hfun := mem_function_of_mem_function_of_subset hd.1 sep_subset
    have hnext := A.woodinCoordinate_directed hs hiθ hj hij rfl rfl rfl f hd
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
    transported_local_directed_union_pair_mem hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
      hπfull.maps hcomp hdata (fun H hH _ ↦ hcollapse H hH)
  have hqnext : woodinQuotientBoundRec θ i p f.val j = ⟨q, ν⟩ₖ := by
    rw [woodinQuotientBoundRec_inverse hi hlim hinac]
    unfold woodinBoundInverseTail woodinBoundTailName
    dsimp only
    simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
    rfl
  have hnorm : q ∈ atomicEquality T U ν
      (forcingSelectedUnion T U o (twoStepNames Qs ∅) (twoStepTailSelector T U Qs ∅) (nameAction E μ.val)) :=
    transported_local_directed_union_normalization hbaseR hbaseo hU hot hsplit hci hT hp hq hqp Q μ hiter
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
      apply A.local_directed_union_quotient_separative_bound hsplit hU hot hiter hπfull.maps hcomp μ hdesc hbound
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

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Transfinite induction over the stage index assembling the four proved steps of
the canonical quotient bound, using closure only at earlier completed stages. -/
theorem woodinQuotientBound_all_stages_of_directed [Countable V] {δ θ i p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α) :
    ∀ j ∈ θ, IsWoodinNormalizedQuotientBoundAt θ i p f.val α j := by
  let := IsOrdinal.of_mem hi
  have hall := transfinite_induction
    (fun j : V ↦ j ∈ θ → IsWoodinNormalizedQuotientBoundAt θ i p f.val α j)
    (by definability) ?_
  · intro j hj
    let := IsOrdinal.of_mem hj
    exact hall (IsOrdinal.toOrdinal j) hj
  intro j ih hj
  have hprevn : ∀ l ∈ (j : V), IsWoodinNormalizedQuotientBoundAt θ i p f.val α l := by
    intro l hl
    let := IsOrdinal.of_mem hl
    exact ih (IsOrdinal.toOrdinal l) hl (IsOrdinal.toIsTransitive.mem_trans hl hj)
  have hprev : ∀ l ∈ (j : V), IsWoodinQuotientBoundAt θ i p f.val α l :=
    fun l hl ↦ (hprevn l hl).1
  by_cases hji : (j : V) ∈ succ i
  · rcases mem_succ_iff.mp hji with hje | hji'
    · subst hje
      exact woodinQuotientBoundAt_base_normalized_of_directed hs hi hp f hf
    · exact woodinQuotientBoundAt_before_base_normalized hs hi hji' hp
  have hij : i ∈ (j : V) := by
    rcases IsOrdinal.mem_trichotomy i (j : V) with hij | he | hji'
    · exact hij
    · exact False.elim (hji (he ▸ mem_succ_self i))
    · exact False.elim (hji (mem_succ_iff.mpr (Or.inr hji')))
  by_cases hsucc : (j : V) = succ (⋃ˢ (j : V))
  · have hkprev : ⋃ˢ (j : V) ∈ (j : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (j : V)) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ (j : V)))
    let := IsOrdinal.of_mem hkprev
    have hkθ : succ (⋃ˢ (j : V)) ∈ θ := by rw [← hsucc]; exact hj
    have hik : i ∈ succ (⋃ˢ (j : V)) := by rw [← hsucc]; exact hij
    have hprev' : ∀ l ∈ succ (⋃ˢ (j : V)), IsWoodinQuotientBoundAt θ i p f.val α l := by
      rw [← hsucc]; exact hprev
    have hclosure := hasWoodinQuotientClosure_prefix_of_stages hs hc hkθ
    rw [hsucc]
    exact woodinQuotientBoundAt_successor_normalized_of_directed hs hkθ hik hclosure hα hp f hf hprev'
  · by_cases hinac :
      IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (j : V)))
    · exact woodinQuotientBoundAt_direct_normalized_of_directed hs hj hij hsucc hinac hα hp f hf hprev
    · exact woodinQuotientBoundAt_inverse_normalized_of_directed hs hj hij hsucc hinac (hc _ hj) hα hp f hf hprevn

theorem woodinQuotientBoundAt_all_stages_of_directed [Countable V] {δ θ i p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α) :
    ∀ j ∈ θ, IsWoodinQuotientBoundAt θ i p f.val α j :=
  fun j hj ↦ (woodinQuotientBound_all_stages_of_directed hs hc hi hα hp f hf j hj).1

/-- The whole bound history is a condition of the inverse limit poset at `θ` and it
restricts to `p` at coordinate `i`. -/
theorem woodinQuotientBoundHistory_mem_and_projects_of_directed [Countable V] {δ θ i p α : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α) :
    woodinQuotientBoundHistory θ i p f.val θ ∈
        forcingInverseCodePoset θ (woodinIterationPrefix θ) ∧
      (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘
        (woodinQuotientBoundHistory θ i p f.val θ) = p :=
  woodinQuotientBoundHistory_inverse_condition hs hi
    (fun j hj ↦ (woodinQuotientBoundAt_all_stages_of_directed hs hc hi hα hp f hf j hj).1)

end ZFVP

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem woodinRawHistory_bound_of_directed [Countable V] {δ θ i p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α)
    (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) (hpG : p ∈ G) :
    let A : ForcingContext V := ⟨_, _, _, G,
      (hs i hi).code.system.order.preorder i (mem_succ_self i),
      (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
    let D := forcingInverseCodePoset θ (woodinIterationPrefix θ)
    let U := forcingInverseCodeOrder θ (woodinIterationPrefix θ)
    let π := forcingThreadCoordinate D i
    A.check (woodinQuotientBoundHistory θ i p f.val θ) ∈ A.projectionQuotient D π ∧
      ∀ a ∈ A.check α,
        ⟨A.check (woodinQuotientBoundHistory θ i p f.val θ), (A.ofName f) ‘ a⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient D π) (A.projectionQuotientOrder D U π) := by
  let A : ForcingContext V := ⟨_, _, _, G,
    (hs i hi).code.system.order.preorder i (mem_succ_self i),
    (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
  have hp := hG.1.1 p hpG
  have hn := woodinQuotientBound_all_stages_of_directed hs hc hi hα hp f hf
  have hq := woodinQuotientBoundHistory_mem_and_projects_of_directed hs hc hi hα hp f hf
  have hπ := (woodinInverseCoordinate_split hs hi).projection.maps
  rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i)] at hπ
  refine ⟨(A.check_mem_projectionQuotient_iff hπ).mpr ⟨hq.1, hq.2.symm ▸ hpG⟩, ?_⟩
  intro a ha
  have hd := woodinQuotientDirectedFamily_semantics hs hi f hf G hG hpG
  have hfun := mem_function_of_mem_function_of_subset hd.1 sep_subset
  have hva := function_value_mem hd.1 ha
  obtain ⟨c, hcD, hval⟩ := (A.mem_check_iff _ _).mp (sep_subset _ hva)
  have hcG := ((A.check_mem_projectionQuotient_iff hπ).mp (hval ▸ hva)).2
  rw [forcingThreadCoordinate_value hcD] at hcG
  rw [hval]
  exact A.woodinRawHistory_le_selected hs (fun _ hx ↦ hx) hi rfl rfl rfl f hpG hcD hcG hfun ha hval
    hcD (fun _ _ ↦ rfl) (fun k hk ↦ (hn k hk).1.1) (fun k hk ↦ (hn k hk).2)

end ZFVP

