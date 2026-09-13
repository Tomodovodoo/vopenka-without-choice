import ZFVP.ModelTheory.WoodinCanonicalBoundRawOrder
import ZFVP.ModelTheory.WoodinCoordinateProjection

/-! The raw-order comparison of the canonical lift with a ground thread, taken at an intermediate
coordinate `j ∈ θ` instead of at the top coordinate `θ`.

`woodinInverseCodeLift_le_thread` compares the lift of a thread of the full inverse limit with a
thread `d` of that same limit. The inverse step of the bound induction needs the same statement one
level down: the thread `r` and the ground thread `d` live in the raw inverse limit of the prefix at
`j`, the history is cut off at `j`, but the candidate still carries the ambient index `θ`, so the
poset and order at the coordinates below `j` are read off the prefix at `θ`. The two prefixes agree
on those coordinates, which is what makes the transfer work. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem subset_of_not_mem_ordinal {i j : V} [IsOrdinal i] [IsOrdinal j]
    (hji : j ∉ i) : i ⊆ j := by
  rcases IsOrdinal.mem_trichotomy j i with hj | rfl | hi
  · exact (hji hj).elim
  · exact fun _ hx ↦ hx
  · exact IsOrdinal.toIsTransitive.transitive _ hi

/-- Below the base coordinate the lift is a projection of `b`, and the comparison follows from
projection monotonicity together with thread coherence of `d`. Same as `woodinRawLift_below_base`
except that `d` is a thread of the raw inverse limit at `j` rather than at `θ`. -/
theorem woodinRawLift_below_base_at {δ θ i j m d e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hij : i ∈ j) (hmi : m ∈ i)
    (hd : d ∈ forcingInverseCodePoset j (woodinIterationPrefix j))
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i) :
    ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
      ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
      ⟨((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨m, i⟩ₖ) ‘ b, d ‘ m⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ m := by
  intro b hb hbe
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hiθ : i ∈ θ := hsub i hij
  have hmj : m ∈ j := IsOrdinal.toIsTransitive.mem_trans hmi hij
  have hmθ : m ∈ θ := hsub m hmj
  have hmi' : m ⊆ i := IsOrdinal.toIsTransitive.transitive _ hmi
  have hcj := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have hext := woodinIterationPrefix_extends hsub
  have hpre := hcθ.system.order.preorder i hiθ
  have he := (kpair_mem_iff.mp (hpre.1 _ hbe)).2
  have hdi := (kpair_mem_iff.mp (hpre.1 _ hde)).2
  have hbd := hpre.2.2 b hb e he _ hdi hbe hde
  have hmono := hcθ.system.order.projMono m hmθ i hiθ hmi' b hb _ hdi hbd
  have hπeq : (forcingCodeπ (woodinIterationPrefix j)) ‘ ⟨m, i⟩ₖ =
      (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨m, i⟩ₖ :=
    hcj.tableπ.value_of_subset hcθ.tableπ hext.subπ (mem_prod_iff.mpr ⟨m, hmj, i, hij, rfl⟩)
  have hdval : ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨m, i⟩ₖ) ‘ (d ‘ i) = d ‘ m := by
    rw [← hπeq]
    exact forcingInverseLimit_project_subset hcj.system.split hd hmj hij hmi'
  rwa [hdval] at hmono

/-- The canonical lift at the coordinate `j`, taken below `b`, is below the ground thread `d` in the
raw inverse-limit order of the prefix at `j`. This is `woodinInverseCodeLift_le_thread` with the
coordinate range `θ` replaced by `j`. -/
theorem woodinInverseCodeLift_le_thread_at {δ θ i j p f d e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hij : i ∈ j) (h0 : ∅ ∈ j)
    (hd : d ∈ forcingInverseCodePoset j (woodinIterationPrefix j))
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hmem : ∀ m ∈ j, woodinQuotientBoundRec θ i p f m ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ m)
    (hraw : ∀ m ∈ j, i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d e m) :
    ∀ r ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      ⟨r, woodinQuotientBoundHistory θ i p f j⟩ₖ ∈
        forcingInverseCodeOrder j (woodinIterationPrefix j) →
      ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
        ⟨b, (forcingThreadCoordinate (forcingInverseCodePoset j (woodinIterationPrefix j)) i) ‘ r⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨(woodinInverseCodeLift j (woodinIterationPrefix j) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ
          ∈ forcingInverseCodeOrder j (woodinIterationPrefix j) := by
  intro r hr hrle b hb hbr hbe
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hiθ : i ∈ θ := hsub i hij
  have hcj := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
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
  have hbj : b ∈ (forcingCodeP (woodinIterationPrefix j)) ‘ i := (hPval i hij) ▸ hb
  have hbrj : ⟨b, (forcingThreadCoordinate
      (forcingInverseCodePoset j (woodinIterationPrefix j)) i) ‘ r⟩ₖ ∈
      (forcingCodeR (woodinIterationPrefix j)) ‘ i := (hRval i hij) ▸ hbr
  have hspec := woodinInverseCodeLift_spec hcj h0 hij r hr b hbj hbrj
  rw [forcingThreadCoordinate_value hr] at hbrj
  apply (mem_forcingInverseCodeOrder_iff).mpr
  refine ⟨hspec.1, hd, ?_⟩
  intro m hm
  let := IsOrdinal.of_mem (hsub m hm)
  rw [hRval m hm]
  by_cases hmi : m ∈ i
  · rw [woodinInverseCodeLift_value_of_mem hcj h0 hij hmi hr hbj, hπval m hm i hij]
    exact woodinRawLift_below_base_at hs hj hij hmi hd hde b hb hbe
  · have him : i ⊆ m := subset_of_not_mem_ordinal hmi
    rw [woodinInverseCodeLift_value_of_le hcj h0 hij hm him hr hbj, hLval i hij m hm]
    have hrm : r ‘ m ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ m := by
      rw [← hPval m hm]
      exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hr).2.1 m hm
    have hrmq : ⟨r ‘ m, woodinQuotientBoundRec θ i p f m⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ m := by
      have hh := (mem_forcingInverseCodeOrder_iff).mp hrle
      have hmm := hh.2.2 m hm
      rw [woodinQuotientBoundHistory_value hm, hRval m hm] at hmm
      exact hmm
    have hbrm : ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, m⟩ₖ) ‘ (r ‘ m)⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by
      rw [← hπval i hij m hm,
        forcingInverseLimit_project_subset hcj.system.split hr hij hm him, ← hRval i hij]
      exact hbrj
    exact hraw m hm him (r ‘ m) hrm hrmq b hb hbrm hbe

/-- The premise of `woodinQuotientBoundAt_inverse_normalized_of_raw`, with the poset and order at the base
coordinate written through `woodinIterationRec i`, and with a fixed auxiliary condition `e` below
each ground thread in place of the thread's own `i`-th value. -/
theorem woodinBoundInverseStep_raw_premise {δ θ i j p f e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hij : i ∈ j) (h0 : ∅ ∈ j)
    (hmem : ∀ m ∈ j, woodinQuotientBoundRec θ i p f m ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ m)
    (hraw : ∀ d ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
      ∀ m ∈ j, i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d e m) :
    ∀ d ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
      ∀ r ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
        ⟨r, woodinQuotientBoundHistory θ i p f j⟩ₖ ∈
          forcingInverseCodeOrder j (woodinIterationPrefix j) →
        ∀ b ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
          ⟨b, (forcingThreadCoordinate
            (forcingInverseCodePoset j (woodinIterationPrefix j)) i) ‘ r⟩ₖ ∈
            (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
          ⟨b, e⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
          ⟨(woodinInverseCodeLift j (woodinIterationPrefix j) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ ∈
            forcingInverseCodeOrder j (woodinIterationPrefix j) := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hiθ : i ∈ θ := hsub i hij
  have hPi : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)
  have hRi : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_order_value hs hiθ (mem_succ_self i)
  intro d hd hde r hr hrle b hb hbr hbe
  exact woodinInverseCodeLift_le_thread_at (p := p) (f := f) hs hj hij h0 hd (hRi ▸ hde) hmem
    (fun m hm him ↦ hraw d hd hde m hm him) r hr hrle b (hPi ▸ hb) (hRi ▸ hbr) (hRi ▸ hbe)

/-- The premise of `woodinQuotientBoundAt_inverse_normalized_of_raw` exactly as that theorem states it,
obtained from the raw comparison for the auxiliary condition `e = d ‘ i`. -/
theorem woodinBoundInverseStep_raw_premise_self {δ θ i j p f : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hij : i ∈ j) (h0 : ∅ ∈ j)
    (hmem : ∀ m ∈ j, woodinQuotientBoundRec θ i p f m ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ m)
    (hraw : ∀ d ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      ∀ m ∈ j, i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d (d ‘ i) m) :
    ∀ d ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      ∀ r ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
        ⟨r, woodinQuotientBoundHistory θ i p f j⟩ₖ ∈
          forcingInverseCodeOrder j (woodinIterationPrefix j) →
        ∀ b ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
          ⟨b, (forcingThreadCoordinate
            (forcingInverseCodePoset j (woodinIterationPrefix j)) i) ‘ r⟩ₖ ∈
            (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
          ⟨b, d ‘ i⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
          ⟨(woodinInverseCodeLift j (woodinIterationPrefix j) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ ∈
            forcingInverseCodeOrder j (woodinIterationPrefix j) := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hiθ : i ∈ θ := hsub i hij
  have hcj := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have hext := woodinIterationPrefix_extends hsub
  have hPi : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)
  have hRi : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_order_value hs hiθ (mem_succ_self i)
  intro d hd r hr hrle b hb hbr hbd
  have hdi : d ‘ i ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i := by
    rw [← hcj.tableP.value_of_subset hcθ.tableP hext.subP hij]
    exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 i hij
  have hrefl : ⟨d ‘ i, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i :=
    (hcθ.system.order.preorder i hiθ).2.1 _ hdi
  exact woodinInverseCodeLift_le_thread_at (p := p) (f := f) hs hj hij h0 hd hrefl hmem
    (fun m hm him ↦ hraw d hd m hm him) r hr hrle b (hPi ▸ hb) (hRi ▸ hbr) (hRi ▸ hbd)

end ZFVP
