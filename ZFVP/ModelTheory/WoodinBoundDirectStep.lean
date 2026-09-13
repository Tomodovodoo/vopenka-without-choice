import ZFVP.ModelTheory.WoodinBoundInvariantSemantics
import ZFVP.ModelTheory.WoodinDirectBoundMembership
import ZFVP.ModelTheory.DirectLimitQuotientBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem woodinQuotientBoundAt_direct [Countable V] {δ θ i p α j : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hi : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
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
      (woodinQuotientSequence_semantics hs hiθ f hf G hG hpG).1 sep_subset
  apply (woodinQuotientBoundAt_iff_generics hs hiθ hj hij hp f).mpr
  refine ⟨hmem, ?_⟩
  intro G hG hpG
  let A : ForcingContext V := ⟨_, _, _, G,
    (hs i hiθ).code.system.order.preorder i (mem_succ_self i),
    (hs i hiθ).code.system.tops.top i (mem_succ_self i), hG⟩
  let μ (k : V) : ForcingName A.P :=
    ⟨woodinBoundCoordinateName θ i f.val k, woodinBoundCoordinateName_isName _ _ _ _⟩
  have hdesc := woodinQuotientSequence_semantics hs hiθ f hf G hG hpG
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
  have hstage := A.woodinCoordinate_descending hs hiθ hj hij rfl rfl rfl f hdesc
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
