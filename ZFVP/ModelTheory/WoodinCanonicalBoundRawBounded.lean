import ZFVP.ModelTheory.WoodinCanonicalBoundRawInduction
import ZFVP.ModelTheory.WoodinCanonicalBoundRawDischarged

/-! Range bounded form of the raw lift comparison.

`woodinRawLiftBound_all_stages` proves `IsWoodinRawLiftBoundAt θ i p f d e m` for every `m ∈ θ`
above the base coordinate `i`, for a thread `d` of the inverse limit at the top coordinate `θ`.
The inverse step of the bound induction at an intermediate coordinate `j ∈ θ` has only a thread of
the inverse limit at `j`, and needs the comparison only for `m ∈ j`.

The statement `IsWoodinRawLiftBoundAt θ i p f d e m` reads `d` at the single coordinate `m`, and
the four steps of the induction read `d` at coordinates below the one being treated. So a thread of
the inverse limit at `j` carries all the information the induction uses when the range is cut down
to `m ∈ j`. Two facts do the transport: the coordinates of a `j` thread are conditions of the `θ`
prefix (`woodinBoundedThread_mem`), and they cohere under the `θ` prefix projections
(`woodinBoundedThread_project`). Everything else here is the proof of the unbounded lemma with the
range `θ` replaced by `j`. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Both sides of a condition in a forcing preorder lie in the poset. -/
private theorem bounded_preorder_mem {P R a b : V} (h : IsForcingPreorder P R)
    (hab : ⟨a, b⟩ₖ ∈ R) : a ∈ P ∧ b ∈ P := kpair_mem_iff.mp (h.1 _ hab)

private theorem bounded_subset_of_not_mem {i j : V} [IsOrdinal i] [IsOrdinal j]
    (hji : j ∉ i) : i ⊆ j := by
  rcases IsOrdinal.mem_trichotomy j i with hj | rfl | hi
  · exact (hji hj).elim
  · exact fun _ hx ↦ hx
  · exact IsOrdinal.toIsTransitive.transitive _ hi

section Thread

variable {δ θ n d : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k)))
  (hn : n ∈ θ) (hd : d ∈ forcingInverseCodePoset n (woodinIterationPrefix n))
include hs hn hd

/-- A coordinate of a thread of the inverse limit at `n` is a condition of the `θ` prefix. -/
theorem woodinBoundedThread_mem {m : V} (hm : m ∈ n) :
    d ‘ m ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ m := by
  let := IsOrdinal.of_mem hn
  have hsub : n ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hn
  have hcn := (woodinIterationPrefix_of_stages (fun l hl ↦ hs l (hsub l hl))).code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have hext := woodinIterationPrefix_extends hsub
  rw [← hcn.tableP.value_of_subset hcθ.tableP hext.subP hm]
  exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 m hm

/-- Coordinates of a thread of the inverse limit at `n` cohere under the `θ` prefix
projections. -/
theorem woodinBoundedThread_project {m l : V} (hm : m ∈ n) (hl : l ∈ n) (hml : m ⊆ l) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨m, l⟩ₖ) ‘ (d ‘ l) = d ‘ m := by
  let := IsOrdinal.of_mem hn
  have hsub : n ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hn
  have hcn := (woodinIterationPrefix_of_stages (fun l hl ↦ hs l (hsub l hl))).code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have hext := woodinIterationPrefix_extends hsub
  rw [← hcn.tableπ.value_of_subset hcθ.tableπ hext.subπ
    (mem_prod_iff.mpr ⟨m, hm, l, hl, rfl⟩ : ⟨m, l⟩ₖ ∈ n ×ˢ n)]
  exact forcingInverseLimit_project_subset hcn.system.split hd hm hl hml

/-- `woodinInverseThread_successor_first` for a thread of the inverse limit at `n`. -/
theorem woodinBoundedThread_successor_first {k : V} (hk : succ k ∈ n) :
    kpair.π₁ (d ‘ (succ k)) = d ‘ k := by
  let := IsOrdinal.of_mem hn
  have hsub : n ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hn
  have hkθ : succ k ∈ θ := hsub _ hk
  let := IsOrdinal.of_mem hkθ
  have hkn : k ∈ n := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hc := woodinBoundedThread_mem hs hn hd hk
  rw [← woodinSuccessor_projection_first hs hkθ hc]
  exact woodinBoundedThread_project hs hn hd hkn hk
    (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k))

/-- `woodinThread_direct_coordinate` for a thread of the inverse limit at `n`. -/
theorem woodinBoundedThread_direct_coordinate {j : V} (hj : j ∈ n) (h0 : j ≠ ∅)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j))) :
    d ‘ j ∈ forcingDirectLimit j (forcingCodeP (woodinIterationPrefix j))
      (forcingCodeπ (woodinIterationPrefix j)) (forcingCodeE (woodinIterationPrefix j))
      (forcingCodeUniverse (woodinIterationPrefix j)) ∧
    ∀ k ∈ j, d ‘ k = (d ‘ j) ‘ k := by
  let := IsOrdinal.of_mem hn
  have hsub : n ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hn
  have hjθ : j ∈ θ := hsub _ hj
  let := IsOrdinal.of_mem hjθ
  have hdj := woodinBoundedThread_mem hs hn hd hj
  have hrec := woodinIterationRec_direct h0 hlim hinac
  rw [woodinIterationPrefix_poset_value hs hjθ (mem_succ_self j), hrec, kpair.π₁_kpair] at hdj
  simp only [forcingDirectCode, forcingThreadCode_poset] at hdj
  refine ⟨hdj, ?_⟩
  intro k hk
  have hkn : k ∈ n := IsOrdinal.toIsTransitive.mem_trans hk hj
  rw [← woodinBoundedThread_project hs hn hd hkn hj (IsOrdinal.toIsTransitive.transitive _ hk),
    woodinIterationPrefix_projection_value hs hjθ (mem_succ_iff.mpr (Or.inr hk))
      (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeπ_code,
    forcingMatrixNext_column hk, forcingLimitProjectionColumn_value hk,
    forcingThreadCoordinate_value hdj]

/-- `woodinThread_inverse_coordinate` for a thread of the inverse limit at `n`. -/
theorem woodinBoundedThread_inverse_coordinate {j : V} (hj : j ∈ n) (h0 : j ≠ ∅)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j))) :
    kpair.π₁ (d ‘ j) ∈ forcingInverseCodePoset j (woodinIterationPrefix j) ∧
      ∀ k ∈ j, d ‘ k = (kpair.π₁ (d ‘ j)) ‘ k := by
  let := IsOrdinal.of_mem hn
  have hsub : n ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hn
  have hjθ : j ∈ θ := hsub _ hj
  let := IsOrdinal.of_mem hjθ
  have hdj := woodinBoundedThread_mem hs hn hd hj
  refine ⟨woodinInverse_first_mem hs hjθ h0 hlim hinac hdj, ?_⟩
  intro k hk
  have hkn : k ∈ n := IsOrdinal.toIsTransitive.mem_trans hk hj
  rw [← woodinBoundedThread_project hs hn hd hkn hj (IsOrdinal.toIsTransitive.transitive _ hk),
    woodinInverse_projection_value hs hjθ h0 hlim hinac hk hdj]

end Thread

/-- `woodinRawLift_below_base` for a thread of the inverse limit at `n`. -/
theorem woodinRawLift_below_base_bounded {δ θ n i p f d e j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hn : n ∈ θ) (hi : i ∈ n) (hj : j ∈ i)
    (hd : d ∈ forcingInverseCodePoset n (woodinIterationPrefix n))
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i) :
    ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
      ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
      ⟨((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨j, i⟩ₖ) ‘ b, d ‘ j⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ j := by
  intro b hb hbe
  let := IsOrdinal.of_mem hn
  have hsub : n ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hn
  have hiθ : i ∈ θ := hsub _ hi
  let := IsOrdinal.of_mem hiθ
  have hjn : j ∈ n := IsOrdinal.toIsTransitive.mem_trans hj hi
  have hjθ : j ∈ θ := hsub _ hjn
  have hji : j ⊆ i := IsOrdinal.toIsTransitive.transitive _ hj
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hpre := hc.system.order.preorder i hiθ
  have he := (bounded_preorder_mem hpre hbe).2
  have hdi := (bounded_preorder_mem hpre hde).2
  have hbd := hpre.2.2 b hb e he _ hdi hbe hde
  have hmono := hc.system.order.projMono j hjθ i hiθ hji b hb _ hdi hbd
  rwa [woodinBoundedThread_project hs hn hd hjn hi hji] at hmono

set_option maxHeartbeats 1000000 in
/-- `isWoodinRawLiftBoundAt_direct` for a thread of the inverse limit at `n`. -/
theorem isWoodinRawLiftBoundAt_direct_bounded {δ θ n i p f d e j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hn : n ∈ θ) (hjn : j ∈ n) (hij : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hd : d ∈ forcingInverseCodePoset n (woodinIterationPrefix n))
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hprev : ∀ m ∈ j, i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d e m) :
    IsWoodinRawLiftBoundAt θ i p f d e j := by
  intro r hr hrq b hb hbr hbe
  let := IsOrdinal.of_mem hn
  have hnsub : n ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hn
  have hj : j ∈ θ := hnsub _ hjn
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hin : i ∈ n := IsOrdinal.toIsTransitive.mem_trans hij hjn
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hij hj
  have hijs : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hij
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hij
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hcj := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have hext := woodinIterationPrefix_extends hsub
  have hrec := woodinIterationRec_direct h0 hlim hinac
  set D := forcingDirectLimit j (forcingCodeP (woodinIterationPrefix j))
    (forcingCodeπ (woodinIterationPrefix j)) (forcingCodeE (woodinIterationPrefix j))
    (forcingCodeUniverse (woodinIterationPrefix j)) with hDdef
  have hPj : (forcingCodeP (woodinIterationPrefix θ)) ‘ j = D := by
    rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [forcingDirectCode, forcingThreadCode_poset, hDdef]
  have hRj : (forcingCodeR (woodinIterationPrefix θ)) ‘ j =
      forcingThreadOrder j (forcingCodeR (woodinIterationPrefix j)) D := by
    rw [woodinIterationPrefix_order_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [forcingDirectCode, forcingThreadCode_order, hDdef]
  have hπj : (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ = forcingThreadCoordinate D i := by
    rw [woodinIterationPrefix_projection_value hs hj (mem_succ_iff.mpr (Or.inr hij))
      (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeπ_code,
      forcingMatrixNext_column hij, forcingLimitProjectionColumn_value hij, hDdef]
  have hrD : r ∈ D := hPj ▸ hr
  have hrI := forcingDirectLimit_subset _ _ _ _ _ _ hrD
  have hrI' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hrI
  rw [hπj, forcingThreadCoordinate_value hrD] at hbr
  have hdj := woodinBoundedThread_mem hs hn hd hjn
  have hxmem := (hcθ.system.lifts.lift i hiθ j hj hijs r hr b hb (by rwa [hπj,
    forcingThreadCoordinate_value hrD])).1
  have hxsplice := woodinDirect_lift_value hs hj hij hlim hinac hr hb
  have hrqj := hrq
  rw [hRj] at hrqj
  have hrqc := ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hrqj).2.2
  rw [hRj]
  apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
  refine ⟨hPj ▸ hxmem, hPj ▸ hdj, ?_⟩
  intro m hm
  let := IsOrdinal.of_mem (IsOrdinal.toIsTransitive.mem_trans hm hj)
  have hmθ := IsOrdinal.toIsTransitive.mem_trans hm hj
  have hRm : (forcingCodeR (woodinIterationPrefix j)) ‘ m =
      (forcingCodeR (woodinIterationPrefix θ)) ‘ m :=
    hcj.tableR.value_of_subset hcθ.tableR hext.subR hm
  have hdcoord :=
    (woodinBoundedThread_direct_coordinate hs hn hd hjn h0 hlim hinac).2 m hm
  rw [hRm, ← hdcoord, hxsplice]
  by_cases hmi : m ∈ i
  · rw [forcingThreadSplice_value hm]
    simp only [forcingSpliceValue, hmi, ↓reduceIte]
    rw [hcj.tableπ.value_of_subset hcθ.tableπ hext.subπ
      (kpair_mem_iff.mpr ⟨hm, hij⟩ : ⟨m, i⟩ₖ ∈ j ×ˢ j)]
    exact woodinRawLift_below_base_bounded (p := p) (f := f) hs hn hin hmi hd hde b hb hbe
  · have him : i ⊆ m := bounded_subset_of_not_mem hmi
    rw [forcingThreadSplice_coordinate hm him,
      hcj.tableL.value_of_subset hcθ.tableL hext.subL
        (kpair_mem_iff.mpr ⟨hij, hm⟩ : ⟨i, m⟩ₖ ∈ j ×ˢ j)]
    have hrm : r ‘ m ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ m := by
      rw [← hcj.tableP.value_of_subset hcθ.tableP hext.subP hm]
      exact hrI'.2.1 m hm
    have hrmq : ⟨r ‘ m, woodinQuotientBoundRec θ i p f m⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ m := by
      have := hrqc m hm
      rw [woodinQuotientBoundRec_direct hij hlim hinac, woodinQuotientBoundHistory_value hm,
        hRm] at this
      exact this
    have hbrm : ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, m⟩ₖ) ‘ (r ‘ m)⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by
      rw [← hcj.tableπ.value_of_subset hcθ.tableπ hext.subπ
          (kpair_mem_iff.mpr ⟨hij, hm⟩ : ⟨i, m⟩ₖ ∈ j ×ˢ j),
        forcingInverseLimit_project_subset hcj.system.split hrI hij hm him]
      exact hbr
    exact hprev m hm him (r ‘ m) hrm hrmq b hb hbrm hbe

set_option maxHeartbeats 1000000 in
/-- `woodinRawLift_successor` for a thread of the inverse limit at `n`. -/
theorem woodinRawLift_successor_bounded [Countable V] {δ θ n i k p f d e : V} [IsOrdinal θ]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hn : n ∈ θ) (hkn : succ k ∈ n) (hik : i ∈ succ k)
    (hd : d ∈ forcingInverseCodePoset n (woodinIterationPrefix n))
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
  let := IsOrdinal.of_mem hn
  have hnsub : n ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hn
  have hk : succ k ∈ θ := hnsub _ hkn
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
    simp only [c, T, U, o, κ, woodinIterationCardinalNext, forcingFamilyNext_new,
      woodinSuccessorStep, woodinSuccessorAt, woodinIterationStage, woodinStagePoset_code,
      woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
  have hci : IsChoicelessInaccessible c := hnew ▸ hnewstage.inaccessible (succ k) (mem_succ_self _)
  let := hci.1
  have hold : (woodinIterationCardinalNext k s K) ‘ k = K ‘ k :=
    forcingFamilyNext_old (mem_succ_self k)
  have hκc : κ ∈ c := by
    simpa only [hnew, hold, κ] using hnewstage.increasing k
      (mem_succ_iff.mpr (Or.inr (mem_succ_self k))) (succ k) (mem_succ_self _) (mem_succ_self k)
  have hT : T ∈ hierarchy c := by
    have hh := h.small k (mem_succ_self k) c hci
    simp only [woodinIterationStage, woodinStageCardinal_code, woodinStagePoset_code] at hh
    exact hh hκc
  have hκforce : ∀ r ∈ T, r ∈ forcingFormula T U regularCardinalFormula
      (standardTuple ![checkName o κ]) := by
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
    simpa only [τ, s, he.1] using
      woodinIterationPrefix_projection_value hs hkθ hik (mem_succ_self k)
  have hPnext : (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k) =
      twoStepConditions T U Qs ∅ := by
    rw [woodinIterationPrefix_poset_value hs hk (mem_succ_self _),
      woodinIterationRec_successor_of_history hhist, kpair.π₁_kpair]
    simp only [woodinIterationSuccessor, forcingSuccessorCode_poset, Qs, c, T, U, o, κ, s, K,
      he.1, he.2]
  have hRnext : (forcingCodeR (woodinIterationPrefix θ)) ‘ (succ k) =
      twoStepOrder T U Qs S ∅ := by
    rw [woodinIterationPrefix_order_value hs hk (mem_succ_self _),
      woodinIterationRec_successor_of_history hhist, kpair.π₁_kpair]
    simp only [woodinIterationSuccessor, forcingSuccessorCode_order, Qs, S, c, T, U, o, κ, s, K,
      he.1, he.2]
  let μ : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    ⟨woodinBoundCoordinateName θ i f (succ k), woodinBoundCoordinateName_isName _ _ _ _⟩
  -- the normalization clause of the successor step
  have hn' : q ∈ atomicEquality T U ν
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
    (σ := σ) (c := d ‘ (succ k)) hbaseR hbaseo hU hot hsplit hiter μ hrqT ?_ ?_ ?_ ?_ heB ?_ hn'
    ?_ ?_
  · have hdk : d ‘ (succ k) ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k) :=
      woodinBoundedThread_mem hs hn hd hkn
    rwa [hPnext] at hdk
  · rw [← hPk]; exact hlift.1
  · rw [← hRk]; exact hlift.2.1
  · rw [woodinBoundedThread_successor_first hs hn hd hkn, ← hRk]
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

set_option maxHeartbeats 1000000 in
/-- `woodinRawLift_inverse` for a thread of the inverse limit at `n`. -/
theorem woodinRawLift_inverse_bounded [Countable V] {δ θ n i j p f d e : V} [IsOrdinal θ]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hn : n ∈ θ) (hjn : j ∈ n) (hij : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hd : d ∈ forcingInverseCodePoset n (woodinIterationPrefix n))
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
  let := IsOrdinal.of_mem hn
  have hnsub : n ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hn
  have hj : j ∈ θ := hnsub _ hjn
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hin : i ∈ n := IsOrdinal.toIsTransitive.mem_trans hij hjn
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
  have hπval : ∀ m ∈ j, ∀ l ∈ j, (forcingCodeπ (woodinIterationPrefix j)) ‘ ⟨m, l⟩ₖ =
      (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨m, l⟩ₖ :=
    fun m hm l hl ↦ hcj.tableπ.value_of_subset hcθ.tableπ hext.subπ
      (mem_prod_iff.mpr ⟨m, hm, l, hl, rfl⟩)
  have hLval : ∀ m ∈ j, ∀ l ∈ j, (forcingCodeL (woodinIterationPrefix j)) ‘ ⟨m, l⟩ₖ =
      (forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨m, l⟩ₖ :=
    fun m hm l hl ↦ hcj.tableL.value_of_subset hcθ.tableL hext.subL
      (mem_prod_iff.mpr ⟨m, hm, l, hl, rfl⟩)
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
    woodinBoundedThread_mem hs hn hd hjn
  have hdi : d ‘ i ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i :=
    woodinBoundedThread_mem hs hn hd hin
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
  have hthread := woodinBoundedThread_inverse_coordinate hs hn hd hjn h0 hlim hinac
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
    have hmn : m ∈ n := IsOrdinal.toIsTransitive.mem_trans hm hjn
    let := IsOrdinal.of_mem hm
    rw [← hthread.2 m hm, hwdef]
    by_cases hmi : m ∈ i
    · rw [forcingThreadSplice_value hm]
      simp only [forcingSpliceValue, ite_eq_left hmi]
      have hmi' : m ⊆ i := IsOrdinal.toIsTransitive.transitive _ hmi
      rw [hRval m hm, hπval m hm i hij,
        ← woodinBoundedThread_project hs hn hd hmn hin hmi']
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
  have hn' : woodinQuotientBoundHistory θ i p f j ∈
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
    ⟨woodinBoundCoordinateName θ i f j, hμname⟩ hrqpair (hPj ▸ hdj) hw hwr hwc he hwd hn'
    ?_ ?_
  · intro G hG heG
    simpa only [hPj] using hdecide G hG heG hRi hti ⟨woodinBoundCoordinateName θ i f j, hμname⟩ rfl
  · intro H hH _
    exact ForcingContext.reverseOrderName_value _ ⟨_, hiter.posetName⟩

set_option maxHeartbeats 1000000 in
/-- Range bounded form of `woodinRawLiftBound_all_stages`. The ground thread `d` is a thread of
the inverse limit at the intermediate coordinate `j ∈ θ`, and the comparison is proved for the
coordinates `m ∈ j` above the base coordinate `i`. -/
theorem woodinRawLiftBound_bounded [Countable V] {δ θ i j p f d e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hij : i ∈ j)
    (hd : d ∈ forcingInverseCodePoset j (woodinIterationPrefix j))
    (he : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hmem : ∀ m ∈ j, woodinQuotientBoundRec θ i p f m ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ m)
    (hnorm : ∀ m ∈ j, IsWoodinBoundNormalizationAt θ i p f m)
    (hiter : ∀ m ∈ j, i ∈ m → m ≠ succ (⋃ˢ m) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix m)) →
      IsForcingIterand (forcingInverseCodePoset m (woodinIterationPrefix m))
        (forcingInverseCodeOrder m (woodinIterationPrefix m))
        (forcingInverseCollapseName m (woodinIterationPrefix m)
          (forcingInverseSourceCutoff m (woodinIterationPrefix m)
            (woodinLimitCardinal (woodinIterationCardinalPrefix m)))
          (forcingInverseHartogsName m (woodinIterationPrefix m)
            (woodinLimitCardinal (woodinIterationCardinalPrefix m)))
          (forcingInverseRestorationName m (woodinIterationPrefix m)
            (woodinLimitCardinal (woodinIterationCardinalPrefix m))))
        (reverseInclusionOrderName (forcingInverseCodePoset m (woodinIterationPrefix m))
          (forcingInverseCodeOrder m (woodinIterationPrefix m))
          (forcingInverseCollapseName m (woodinIterationPrefix m)
            (forcingInverseSourceCutoff m (woodinIterationPrefix m)
              (woodinLimitCardinal (woodinIterationCardinalPrefix m)))
            (forcingInverseHartogsName m (woodinIterationPrefix m)
              (woodinLimitCardinal (woodinIterationCardinalPrefix m)))
            (forcingInverseRestorationName m (woodinIterationPrefix m)
              (woodinLimitCardinal (woodinIterationCardinalPrefix m))))) ∅)
    (hdecideSucc : ∀ k, succ k ∈ j → i ∈ succ k →
      ∀ (G : Set V) (hG : IsExternalForcingGeneric
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
            a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ (succ k)))
    (hdecideInv : ∀ m ∈ j, i ∈ m → m ≠ succ (⋃ˢ m) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix m)) →
      ∀ (G : Set V) (hG : IsExternalForcingGeneric
          ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) G), e ∈ G →
        ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i))
          (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodet (woodinIterationPrefix θ)) ‘ i))
          (μ : ForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)),
          μ.val = woodinBoundCoordinateName θ i f m →
          let A : ForcingContext V := ⟨_, _, _, G, hRi, hti, hG⟩
          ∃ X a : A.Model, A.ofName μ ∈
              A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ m) ^ X ∧
            a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ m)) :
    ∀ m ∈ j, i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d e m := by
  let := IsOrdinal.of_mem hj
  have hjsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hiθ : i ∈ θ := hjsub _ hij
  let := IsOrdinal.of_mem hiθ
  have hall := transfinite_induction
    (fun m : V ↦ m ∈ j → i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d e m)
    (by definability) ?_
  · intro m hm him
    let := IsOrdinal.of_mem (hjsub _ hm)
    exact hall (IsOrdinal.toOrdinal m) hm him
  intro m ih hm hsub
  let := IsOrdinal.of_mem (hjsub _ hm)
  have hprev : ∀ l ∈ (m : V), i ⊆ l → IsWoodinRawLiftBoundAt θ i p f d e l := by
    intro l hl hil
    let := IsOrdinal.of_mem (hjsub _ (IsOrdinal.toIsTransitive.mem_trans hl hm))
    exact ih (IsOrdinal.toOrdinal l) hl (IsOrdinal.toIsTransitive.mem_trans hl hm) hil
  rcases IsOrdinal.subset_iff.mp hsub with rfl | him
  · exact isWoodinRawLiftBoundAt_base hs hiθ hde
  by_cases hsucc : (m : V) = succ (⋃ˢ (m : V))
  · have hkprev : ⋃ˢ (m : V) ∈ (m : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (m : V)) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ (m : V)))
    let := IsOrdinal.of_mem (hjsub _ (IsOrdinal.toIsTransitive.mem_trans hkprev hm))
    have hkj : succ (⋃ˢ (m : V)) ∈ j := by rw [← hsucc]; exact hm
    have hik : i ∈ succ (⋃ˢ (m : V)) := by rw [← hsucc]; exact him
    have hiksub : i ⊆ ⋃ˢ (m : V) := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hik)
    have hprevk : IsWoodinRawLiftBoundAt θ i p f d e (⋃ˢ (m : V)) :=
      hprev _ hkprev hiksub
    have hmem' : ∀ l ∈ succ (succ (⋃ˢ (m : V))),
        woodinQuotientBoundRec θ i p f l ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ l := by
      intro l hl
      rcases mem_succ_iff.mp hl with rfl | hl
      · exact hmem _ hkj
      · exact hmem l (IsOrdinal.toIsTransitive.mem_trans hl hkj)
    rw [hsucc]
    unfold IsWoodinRawLiftBoundAt
    dsimp only
    exact woodinRawLift_successor_bounded hs hj hkj hik hd hmem' (hnorm _ hkj) hprevk
      (hdecideSucc _ hkj hik)
  by_cases hinac :
      IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (m : V)))
  · exact isWoodinRawLiftBoundAt_direct_bounded hs hj hm him hsucc hinac hd hde hprev
  have hmem' : ∀ l ∈ succ (m : V),
      woodinQuotientBoundRec θ i p f l ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ l := by
    intro l hl
    rcases mem_succ_iff.mp hl with rfl | hl
    · exact hmem _ hm
    · exact hmem l (IsOrdinal.toIsTransitive.mem_trans hl hm)
  unfold IsWoodinRawLiftBoundAt
  dsimp only
  exact woodinRawLift_inverse_bounded hs hj hm him hsucc hinac hd he hde
    (hiter _ hm him hsucc hinac) hmem' (hnorm _ hm)
    (fun l hl hil ↦ hprev l hl hil) (hdecideInv _ hm him hsucc hinac)

set_option maxHeartbeats 1000000 in
/-- `woodinRawLiftBound_bounded` with the iterand premise proved from `hs` and the two decision
premises replaced by the pair of clauses that `woodinBound_decision_condition_uniform`
delivers. -/
theorem woodinRawLiftBound_bounded_decided [Countable V] {δ θ i j p f d e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hij : i ∈ j)
    (hd : d ∈ forcingInverseCodePoset j (woodinIterationPrefix j))
    (he : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hmem : ∀ m ∈ j, woodinQuotientBoundRec θ i p f m ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ m)
    (hnorm : ∀ m ∈ j, IsWoodinBoundNormalizationAt θ i p f m)
    (hdec : WoodinBoundDecidesDirect θ i f d e ∧ WoodinBoundDecidesPrefix θ i f d e) :
    ∀ m ∈ j, i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d e m := by
  let := IsOrdinal.of_mem hj
  have hjsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  exact woodinRawLiftBound_bounded hs hj hij hd he hde hmem hnorm
    (fun m hm ↦ woodinRawLiftBound_iterand_of_stages (i := i) hs m (hjsub _ hm))
    (fun k hk ↦ woodinRawLiftBound_decideSucc_of_decides hdec.1 k (hjsub _ hk))
    (fun m hm ↦ woodinRawLiftBound_decideInv_of_decides hdec.2 m (hjsub _ hm))

end ZFVP
