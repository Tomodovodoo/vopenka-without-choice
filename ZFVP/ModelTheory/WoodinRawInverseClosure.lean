import ZFVP.ModelTheory.WoodinRawHistoryBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem woodinRawInverse_quotient_closedBelow [Countable V] {δ θ i : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) :
    let s := woodinIterationPrefix θ
    ForcesProjectionQuotientClosedBelow ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingCodet s) ‘ i) (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingThreadCoordinate (forcingInverseCodePoset θ s) i)
      ((woodinIterationCardinalPrefix θ) ‘ i) := by
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
  dsimp only
  rw [hPi, hRi, hoi, hKi]
  apply projectionQuotient_closedBelow_forced_of_generics hR ho hπ hU
  intro G hG
  let A : ForcingContext V := ⟨B, R, o, G, hR, ho, hG⟩
  change IsForcingClosedBelow (A.projectionQuotient D π)
    (forcingSeparativeOrder (A.projectionQuotient D π) (A.projectionQuotientOrder D U π)) (A.check η)
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
  have ht : forcingSeparativeDescendingFormula.Evalb
      (fun k ↦ A.ofName ((![QN, SN, ⟨checkName o α, checkName_isName ho.1 α⟩, f] :
        Fin 4 → ForcingName B) k)) := by
    apply (Defined.eval_iff _).mpr
    change IsForcingDescending (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN))
      (A.check α) (A.ofName f)
    rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hU]
    exact hz
  obtain ⟨p, hpG, hpf⟩ := (A.formula_truth forcingSeparativeDescendingFormula
    ![QN, SN, ⟨checkName o α, checkName_isName ho.1 α⟩, f]).mp ht
  have hf : ForcesWoodinQuotientSequence θ i p f.val α := hpf
  exact ⟨A.check (woodinQuotientBoundHistory θ i p f.val θ),
    woodinRawHistory_bound hs hc hi hα f hf G hG hpG⟩

end ZFVP
