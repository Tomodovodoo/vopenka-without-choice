import ZFVP.ModelTheory.IterationQuotientClosure
import ZFVP.ModelTheory.WoodinDirectIndex
import ZFVP.ModelTheory.DirectLimitQuotientClosure
import ZFVP.ModelTheory.DirectQuotientClosureTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.woodin_direct_quotient_closedBelow (A : ForcingContext V)
    {δ θ s K i : V} [IsOrdinal θ] (h : IsWoodinIteration δ θ s K)
    (hc : HasWoodinQuotientClosure θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K)) (hi : i ∈ θ)
    (hAP : A.P = (forcingCodeP s) ‘ i) (hAR : A.R = (forcingCodeR s) ‘ i)
    (hAt : A.one = (forcingCodet s) ‘ i) :
    IsForcingClosedBelow
      (A.projectionQuotient (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s))
        (forcingThreadCoordinate (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s)) i))
      (forcingSeparativeOrder
        (A.projectionQuotient (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s))
          (forcingThreadCoordinate (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s)) i))
        (A.projectionQuotientOrder
          (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s))
          (forcingThreadOrder θ (forcingCodeR s)
            (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s)))
          (forcingThreadCoordinate (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s)) i)))
      (A.check (K ‘ i)) := by
  have he := h.index_eq_regular_limit hlim hinac.regular
  have hθ : IsChoicelessInaccessible θ := he.symm ▸ hinac
  have hKi : K ‘ i ∈ θ := he.symm ▸ h.cardinal_mem_limit hlim hi
  have hsmall : A.P ∈ hierarchy θ := by
    rw [hAP]
    have hs := h.small i hi θ hθ
    simp only [woodinIterationStage, woodinStagePoset_code, woodinStageCardinal_code] at hs
    exact hs hKi
  apply A.directLimit_quotient_separative_closedBelow_of_small hθ hsmall h.code.system.split hi hAP
    h.code.subset_universe (fun j hj k hk hjk ↦ h.code.system.splitProjection hj hk hjk)
    ((A.checkEmbedding.subset_iff _ _).mpr (IsOrdinal.toIsTransitive.transitive _ hKi))
  intro j hj hij
  have hπ := h.code.system.projection hi hj hij
  rw [← hAP, ← hAR] at hπ
  apply A.projectionQuotient_closedBelow_of_forced hπ (h.code.system.order.preorder j hj)
  simpa only [hAP, hAR, hAt, IterationQuotientClosedBelow, ForcesProjectionQuotientClosedBelow] using hc i hi j hj hij

theorem HasWoodinQuotientClosure.direct_final_countable [Countable V]
    {δ θ s K i : V} [IsOrdinal θ] (h : IsWoodinIteration δ θ s K)
    (hc : HasWoodinQuotientClosure θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K)) (hi : i ∈ θ) (h0 : ∅ ∈ θ) :
    IterationQuotientClosedBelow (forcingDirectCode θ s) i θ (K ‘ i) := by
  let z := forcingDirectCode θ s
  have hz : IsForcingIterationCode (succ θ) z := forcingDirectCode_valid h.code h0
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hPi : (forcingCodeP z) ‘ i = (forcingCodeP s) ‘ i := by
    simp only [z, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_old hi]
  have hRi : (forcingCodeR z) ‘ i = (forcingCodeR s) ‘ i := by
    simp only [z, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeR_code, forcingFamilyNext_old hi]
  have hti : (forcingCodet z) ‘ i = (forcingCodet s) ‘ i := by
    simp only [z, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodet_code, forcingFamilyNext_old hi]
  have hπ := hz.system.projection hi' (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi)
  rw [hPi, hRi] at hπ
  change IterationQuotientClosedBelow z i θ (K ‘ i)
  unfold IterationQuotientClosedBelow
  rw [hPi, hRi, hti]
  apply projectionQuotient_closedBelow_forced_of_generics (h.code.system.order.preorder i hi)
    (h.code.system.tops.top i hi) hπ (hz.system.order.preorder θ (mem_succ_self θ))
  intro G hG
  let A : ForcingContext V := ⟨_, _, _, G, h.code.system.order.preorder i hi, h.code.system.tops.top i hi, hG⟩
  simpa only [z, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingFamilyNext_new,
    forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi]
    using A.woodin_direct_quotient_closedBelow h hc hlim hinac hi rfl rfl rfl

theorem HasWoodinQuotientClosure.direct_countable [Countable V]
    {δ θ s K : V} [IsOrdinal θ] (h : IsWoodinIteration δ θ s K)
    (hc : HasWoodinQuotientClosure θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K)) (h0 : ∅ ∈ θ) :
    HasWoodinQuotientClosure (succ θ) (forcingDirectCode θ s)
      (forcingFamilyNext θ K (woodinLimitCardinal K)) := by
  intro i hi j hj hij
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases mem_succ_iff.mp hj with rfl | hj
  · rcases mem_succ_iff.mp hi with rfl | hi
    · exact (forcingDirectCode_valid h.code h0).diagonal_quotient_closedBelow (mem_succ_self _) _
    · rw [forcingFamilyNext_old hi]
      exact hc.direct_final_countable h hlim hinac hi h0
  · have hiold : i ∈ θ := ordinal_mem_of_subset_mem hij hj
    simp only [IterationQuotientClosedBelow, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingCodeR_code, forcingCodet_code, forcingCodeπ_code,
      forcingFamilyNext_old hiold, forcingFamilyNext_old hj, forcingMatrixNext_old hi hj]
    exact hc i hiold j hj hij

theorem HasWoodinQuotientClosure.direct_final
    {δ θ s K i : V} [IsOrdinal θ] (h : IsWoodinIteration δ θ s K)
    (hc : HasWoodinQuotientClosure θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K)) (hi : i ∈ θ) :
    IterationQuotientClosedBelow (forcingDirectCode θ s) i θ (K ‘ i) := by
  have he := h.index_eq_regular_limit hlim hinac.regular
  have hθ : IsChoicelessInaccessible θ := he.symm ▸ hinac
  have hKi : K ‘ i ∈ θ := he.symm ▸ h.cardinal_mem_limit hlim hi
  have hs := h.small i hi θ hθ
  simp only [woodinIterationStage, woodinStagePoset_code, woodinStageCardinal_code] at hs
  simp only [IterationQuotientClosedBelow, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodet_code, forcingCodeπ_code,
    forcingFamilyNext_old hi, forcingFamilyNext_new, forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi]
  exact directQuotient_closedBelow_forced hθ (hs hKi) h.code.system.split h.code.system.order.preorder
    (h.code.system.tops.top i hi) (fun j hj k hk hjk ↦ h.code.system.splitProjection hj hk hjk)
    h.code.subset_universe hi (IsOrdinal.toIsTransitive.transitive _ hKi) rfl rfl rfl
    (fun k hk hik ↦ hc i hi k hk hik)

theorem HasWoodinQuotientClosure.direct
    {δ θ s K : V} [IsOrdinal θ] (h : IsWoodinIteration δ θ s K)
    (hc : HasWoodinQuotientClosure θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K)) (h0 : ∅ ∈ θ) :
    HasWoodinQuotientClosure (succ θ) (forcingDirectCode θ s)
      (forcingFamilyNext θ K (woodinLimitCardinal K)) := by
  intro i hi j hj hij
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases mem_succ_iff.mp hj with rfl | hj
  · rcases mem_succ_iff.mp hi with rfl | hi
    · exact (forcingDirectCode_valid h.code h0).diagonal_quotient_closedBelow (mem_succ_self _) _
    · rw [forcingFamilyNext_old hi]
      exact hc.direct_final h hlim hinac hi
  · have hiold : i ∈ θ := ordinal_mem_of_subset_mem hij hj
    simp only [IterationQuotientClosedBelow, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingCodeR_code, forcingCodet_code, forcingCodeπ_code,
      forcingFamilyNext_old hiold, forcingFamilyNext_old hj, forcingMatrixNext_old hi hj]
    exact hc i hiold j hj hij

end ZFVP
