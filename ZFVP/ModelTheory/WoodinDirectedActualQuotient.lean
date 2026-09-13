import ZFVP.ModelTheory.WoodinDirectedCanonicalBound
import ZFVP.ModelTheory.WoodinEndpointDirect

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem woodinRawInverse_quotient_directedClosedBelow [Countable V] {δ θ i : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) :
    ∀ (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G),
    let A : ForcingContext V := ⟨_, _, _, G,
      (hs i hi).code.system.order.preorder i (mem_succ_self i),
      (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
    ∀ β ∈ A.check ((kpair.π₂ (woodinIterationRec i)) ‘ i),
      IsForcingDirectedClosedAt
        (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
        (forcingSeparativeOrder
          (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
            (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
          (A.projectionQuotientOrder (forcingInverseCodePoset θ (woodinIterationPrefix θ))
            (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
            (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))) β := by
  let := IsOrdinal.of_mem hi
  have h := woodinIterationPrefix_of_stages hs
  have hPi := woodinIterationPrefix_poset_value hs hi (mem_succ_self i)
  have hRi := woodinIterationPrefix_order_value hs hi (mem_succ_self i)
  have hoi := woodinIterationPrefix_top_value hs hi (mem_succ_self i)
  have hKi : (woodinIterationCardinalPrefix θ) ‘ i = (kpair.π₂ (woodinIterationRec i)) ‘ i := by
    have hh := woodinIterationHistory_of_stages hs
    simpa only [woodinIterationCardinalPrefix, woodinIterationHistory_cardinal_value hi] using
      hh.cardinal_union_value hi (mem_succ_self i)
  let B := (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i
  let R := (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i
  let o := (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i
  let D := forcingInverseCodePoset θ (woodinIterationPrefix θ)
  let U := forcingInverseCodeOrder θ (woodinIterationPrefix θ)
  let π := forcingThreadCoordinate D i
  let η := (kpair.π₂ (woodinIterationRec i)) ‘ i
  have hR := (hs i hi).code.system.order.preorder i (mem_succ_self i)
  have ho := (hs i hi).code.system.tops.top i (mem_succ_self i)
  have hπ := (woodinInverseCoordinate_split hs hi).projection
  rw [hPi, hRi] at hπ
  have h0 : (∅ : V) ∈ θ := by
    rcases IsOrdinal.subset_iff.mp (empty_subset i) with he | he
    · exact he.symm ▸ hi
    · exact IsOrdinal.toIsTransitive.mem_trans he hi
  have hU := (h.code.system.inverseColumn h0 h.code.subset_universe).order.preorder
  intro G hG
  let A : ForcingContext V := ⟨B, R, o, G, hR, ho, hG⟩
  change ∀ β ∈ A.check η, IsForcingDirectedClosedAt (A.projectionQuotient D π)
    (forcingSeparativeOrder (A.projectionQuotient D π) (A.projectionQuotientOrder D U π)) β
  intro β hβ
  obtain ⟨α, hα, rfl⟩ := (A.mem_check_iff η β).mp hβ
  have hη : IsOrdinal η := ((hs i hi).inaccessible i (mem_succ_self i)).1
  let := hη
  let := IsOrdinal.of_mem hα
  intro z hz
  obtain ⟨f, rfl⟩ := A.ofName_surjective z
  let QN : ForcingName B := ⟨projectionQuotientName D π o, projectionQuotientName_isName ho.1 hπ.maps⟩
  let SN : ForcingName B := ⟨projectionQuotientOrderName U π o,
    projectionQuotientOrderName_isName ho.1 hπ.maps hU⟩
  have ht : forcingSeparativeDirectedFormula.Evalb
      (fun k ↦ A.ofName ((![QN, SN, ⟨checkName o α, checkName_isName ho.1 α⟩, f] :
        Fin 4 → ForcingName B) k)) := by
    apply (Defined.eval_iff _).mpr
    change IsForcingDirectedFamily (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN))
      (A.check α) (A.ofName f)
    rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hU]
    exact hz
  obtain ⟨p, hpG, hpf⟩ := (A.formula_truth forcingSeparativeDirectedFormula
    ![QN, SN, ⟨checkName o α, checkName_isName ho.1 α⟩, f]).mp ht
  have hf : ForcesWoodinQuotientDirectedFamily θ i p f.val α := hpf
  exact ⟨A.check (woodinQuotientBoundHistory θ i p f.val θ),
    woodinRawHistory_bound_of_directed hs hc hi hα f hf G hG hpG⟩

theorem woodinCompleted_quotient_directedClosedBelow [Countable V] {δ θ i j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) :
    let A : ForcingContext V := ⟨_, _, _, G,
      (hs i hi).code.system.order.preorder i (mem_succ_self i),
      (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
    ∀ β ∈ A.check ((kpair.π₂ (woodinIterationRec i)) ‘ i),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
          ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
            ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ j)
            ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))) β := by
  let A : ForcingContext V := ⟨_, _, _, G,
    (hs i hi).code.system.order.preorder i (mem_succ_self i),
    (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
  have hsys := (woodinIterationPrefix_of_stages hs).code.system
  have hπ := (woodinInverseCoordinate_split hs hi).projection.maps
  have hτ := (hsys.projection hi hj hij).maps
  rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i)] at hπ hτ
  have hsplit := A.projectionQuotient_splitProjection hπ hτ (woodinInverseCoordinate_split hs hj) (by
    intro q hq
    rw [forcingThreadCoordinate_value hq, forcingThreadCoordinate_value hq]
    exact woodinInverseThread_project hs hi hj hij hq)
  dsimp only
  intro β hβ
  exact hsplit.separative_directedClosedAt_of_source
    (woodinRawInverse_quotient_directedClosedBelow hs hc hi G hG β hβ)

/-- Completed-row directed closure follows from the construction, including
the endpoint row. No closure or normalization hypothesis is supplied by the caller. -/
theorem ForcingContext.woodinActual_quotient_directedClosedBelow [Countable V]
    (A : ForcingContext V) {Ω i j : V} [IsOrdinal i] [IsOrdinal j]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hij : i ⊆ j) (hjΩ : j ⊆ Ω)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) :
    ∀ β ∈ A.check ((kpair.π₂ (woodinIterationRec i)) ‘ i),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
          ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
            ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec j))) ‘ j)
            ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ))) β := by
  let := hΩ.inaccessible.1
  have hst : ∀ k ∈ succ j,
      IsWoodinIteration (succ Ω) (succ k) (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k)) ∧
      HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k)) := by
    intro k hk
    let := IsOrdinal.of_mem hk
    have hkΩ : k ⊆ Ω := subset_trans
      (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hk)) hjΩ
    rcases IsOrdinal.subset_iff.mp hkΩ with rfl | hkΩ
    · exact woodinIteration_endpoint_valid hΩ hAC
    · have hh := (woodinIterationExit hΩ hAC).2.1 k hkΩ
      exact ⟨hh.1.enlarge_bound (fun _ hx ↦ mem_succ_iff.mpr (Or.inr hx)), hh.2⟩
  have hs := fun k hk ↦ (hst k hk).1
  have hc := fun k hk ↦ (hst k hk).2
  have hi : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  obtain ⟨P, R, o, G, hRa, hoa, hG⟩ := A
  dsimp only at hP hR ho
  subst P R o
  have hh := woodinCompleted_quotient_directedClosedBelow hs hc hi (mem_succ_self j) hij G hG
  rw [woodinIterationPrefix_poset_value hs (mem_succ_self j) (mem_succ_self j),
    woodinIterationPrefix_order_value hs (mem_succ_self j) (mem_succ_self j),
    woodinIterationPrefix_projection_value hs (mem_succ_self j) hi (mem_succ_self j)] at hh
  exact hh

end ZFVP
