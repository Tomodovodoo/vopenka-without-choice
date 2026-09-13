import ZFVP.ModelTheory.WoodinCanonicalBoundLift
import ZFVP.ModelTheory.WoodinBoundCoherence
import ZFVP.ModelTheory.WoodinDirectLiftCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Both sides of a condition in a forcing preorder lie in the poset. -/
private theorem preorder_mem {P R a b : V} (h : IsForcingPreorder P R)
    (hab : ⟨a, b⟩ₖ ∈ R) : a ∈ P ∧ b ∈ P := kpair_mem_iff.mp (h.1 _ hab)

private theorem ordinal_subset_of_not_mem {i j : V} [IsOrdinal i] [IsOrdinal j]
    (hji : j ∉ i) : i ⊆ j := by
  rcases IsOrdinal.mem_trichotomy j i with hj | rfl | hi
  · exact (hji hj).elim
  · exact fun _ hx ↦ hx
  · exact IsOrdinal.toIsTransitive.transitive _ hi

/-- The raw-order comparison at one coordinate `j`: every condition `r` below the canonical
quotient bound at `j`, lifted along a base condition `b` that sits below `e`, stays below the
`j`-th value of the ground thread `d`. -/
def IsWoodinRawLiftBoundAt (θ i p f d e j : V) : Prop :=
  let s := woodinIterationPrefix θ
  ∀ r ∈ (forcingCodeP s) ‘ j, ⟨r, woodinQuotientBoundRec θ i p f j⟩ₖ ∈ (forcingCodeR s) ‘ j →
  ∀ b ∈ (forcingCodeP s) ‘ i,
    ⟨b, ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ r⟩ₖ ∈ (forcingCodeR s) ‘ i →
    ⟨b, e⟩ₖ ∈ (forcingCodeR s) ‘ i →
    ⟨((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨r, b⟩ₖ, d ‘ j⟩ₖ ∈ (forcingCodeR s) ‘ j

instance isWoodinRawLiftBoundAt_definable (θ i p f d e : V) :
    ℒₛₑₜ-predicate[V] (IsWoodinRawLiftBoundAt θ i p f d e) := by
  unfold IsWoodinRawLiftBoundAt
  dsimp only
  definability

/-- Below the base coordinate the lift is a projection of `b`, and the comparison follows from
projection monotonicity together with the thread coherence of `d`. -/
theorem woodinRawLift_below_base {δ θ i p f d e j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hj : j ∈ i)
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i) :
    ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
      ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
      ⟨((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨j, i⟩ₖ) ‘ b, d ‘ j⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ j := by
  intro b hb hbe
  let := IsOrdinal.of_mem hi
  have hjθ := IsOrdinal.toIsTransitive.mem_trans hj hi
  have hji : j ⊆ i := IsOrdinal.toIsTransitive.transitive _ hj
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hpre := hc.system.order.preorder i hi
  have he := (preorder_mem hpre hbe).2
  have hdi := (preorder_mem hpre hde).2
  have hbd := hpre.2.2 b hb e he _ hdi hbe hde
  have hmono := hc.system.order.projMono j hjθ i hi hji b hb _ hdi hbd
  rwa [forcingInverseLimit_project_subset hc.system.split hd hjθ hi hji] at hmono

/-- At the base coordinate the lift is the identity, so the comparison is transitivity of the
preorder through `e`. -/
theorem isWoodinRawLiftBoundAt_base {δ θ i p f d e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ)
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i) :
    IsWoodinRawLiftBoundAt θ i p f d e i := by
  intro r hr _ b hb hbr hbe
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hpre := hc.system.order.preorder i hi
  have hlift := hc.system.lifts.lift i hi i hi (fun _ hx ↦ hx) r hr b hb hbr
  have hid : ((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, i⟩ₖ) ‘ ⟨r, b⟩ₖ = b :=
    (hc.system.split.projId hi hlift.1).symm.trans hlift.2.2
  rw [hid]
  exact hpre.2.2 b hb e (preorder_mem hpre hbe).2 _ (preorder_mem hpre hde).2 hbe hde

/-- At a direct-limit coordinate the lift is the splice thread, so the comparison reduces to the
earlier coordinates: below `i` it is `woodinRawLift_below_base`, above `i` it is `hprev`. -/
theorem isWoodinRawLiftBoundAt_direct {δ θ i p f d e j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hij : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hprev : ∀ m ∈ j, i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d e m) :
    IsWoodinRawLiftBoundAt θ i p f d e j := by
  intro r hr hrq b hb hbr hbe
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
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
  have hdj := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 j hj
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
  have hdcoord := (woodinThread_direct_coordinate hs hj h0 hlim hinac hd).2 m hm
  rw [hRm, ← hdcoord, hxsplice]
  by_cases hmi : m ∈ i
  · rw [forcingThreadSplice_value hm]
    simp only [forcingSpliceValue, hmi, ↓reduceIte]
    rw [hcj.tableπ.value_of_subset hcθ.tableπ hext.subπ
      (kpair_mem_iff.mpr ⟨hm, hij⟩ : ⟨m, i⟩ₖ ∈ j ×ˢ j)]
    exact woodinRawLift_below_base (p := p) (f := f) hs hiθ hmi hd hde b hb hbe
  · have him : i ⊆ m := ordinal_subset_of_not_mem hmi
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

/-- The canonical lift of a thread `r` below the bound history, taken below `b`, is below the
ground thread `d` in the raw inverse-limit order. -/
theorem woodinInverseCodeLift_le_thread {δ θ i p f d e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (h0 : ∅ ∈ θ)
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hmem : ∀ j ∈ θ, woodinQuotientBoundRec θ i p f j ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hraw : ∀ j ∈ θ, i ⊆ j → IsWoodinRawLiftBoundAt θ i p f d e j) :
    ∀ r ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      ⟨r, woodinQuotientBoundHistory θ i p f θ⟩ₖ ∈
        forcingInverseCodeOrder θ (woodinIterationPrefix θ) →
      ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
        ⟨b, (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘ r⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨(woodinInverseCodeLift θ (woodinIterationPrefix θ) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ
          ∈ forcingInverseCodeOrder θ (woodinIterationPrefix θ) := by
  intro r hr hrle b hb hbr hbe
  let := IsOrdinal.of_mem hi
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hspec := woodinInverseCodeLift_spec hc h0 hi r hr b hb hbr
  rw [forcingThreadCoordinate_value hr] at hbr
  apply (mem_forcingInverseCodeOrder_iff).mpr
  refine ⟨hspec.1, hd, ?_⟩
  intro j hj
  let := IsOrdinal.of_mem hj
  have hrle' := (mem_forcingInverseCodeOrder_iff).mp hrle
  by_cases hji : j ∈ i
  · rw [woodinInverseCodeLift_value_of_mem hc h0 hi hji hr hb]
    exact woodinRawLift_below_base (p := p) (f := f) hs hi hji hd hde b hb hbe
  · have hij : i ⊆ j := ordinal_subset_of_not_mem hji
    rw [woodinInverseCodeLift_value_of_le hc h0 hi hj hij hr hb]
    have hrm : r ‘ j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j :=
      ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hr).2.1 j hj
    have hrmq : ⟨r ‘ j, woodinQuotientBoundRec θ i p f j⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ j := by
      have := hrle'.2.2 j hj
      rwa [woodinQuotientBoundHistory_value hj] at this
    have hbrm : ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ (r ‘ j)⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by
      rwa [forcingInverseLimit_project_subset hc.system.split hr hi hj hij]
    exact hraw j hj hij (r ‘ j) hrm hrmq b hb hbrm hbe

end ZFVP
