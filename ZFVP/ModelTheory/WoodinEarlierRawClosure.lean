import ZFVP.ModelTheory.WoodinInverseIterandFromStages
import ZFVP.ModelTheory.SplitClosureDownward
import ZFVP.ModelTheory.QuotientSplitProjection
import ZFVP.ModelTheory.IterationQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem woodinEarlierRaw_quotient_closedBelow [Countable V] {δ θ j i : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (hi : i ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hclosure : HasWoodinQuotientClosure (succ j) (kpair.π₁ (woodinIterationRec j))
      (kpair.π₂ (woodinIterationRec j))) :
    let s := woodinIterationPrefix j
    ForcesProjectionQuotientClosedBelow ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingCodet s) ‘ i) (forcingInverseCodePoset j s) (forcingInverseCodeOrder j s)
      (forcingThreadCoordinate (forcingInverseCodePoset j s) i)
      ((woodinIterationCardinalPrefix j) ‘ i) := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hj
  have hij : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hi
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have h0j : (∅ : V) ∈ j := (IsOrdinal.subset_iff.mp (empty_subset j)).resolve_left (fun he ↦ h0 he.symm)
  let s := woodinIterationPrefix j
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix j)
  let T := forcingInverseCodePoset j s
  let U := forcingInverseCodeOrder j s
  let Q := forcingInverseCollapseName j s (forcingInverseSourceCutoff j s γ)
    (forcingInverseHartogsName j s γ) (forcingInverseRestorationName j s γ)
  let S := reverseInclusionOrderName T U Q
  let τ := forcingThreadCoordinate T i
  let π := (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ
  have hssub := fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj)
  have hlocal := (woodinIterationPrefix_of_stages hssub).code
  have hglobal := (woodinIterationPrefix_of_stages hs).code
  have hext := woodinIterationPrefix_extends (IsOrdinal.toIsTransitive.transitive _ hj)
  have hPi := hlocal.tableP.value_of_subset hglobal.tableP hext.subP hi
  have hRi := hlocal.tableR.value_of_subset hglobal.tableR hext.subR hi
  have hoi := hlocal.tablet.value_of_subset hglobal.tablet hext.subt hi
  have col := hlocal.system.inverseColumn h0j hlocal.subset_universe
  have hiter := woodinInverse_iterand_of_stages hs hj h0 hlim hinac
  have hrec := woodinIterationRec_inverse h0 hlim hinac
  have hPnext : (forcingCodeP (woodinIterationPrefix θ)) ‘ j = twoStepConditions T U Q ∅ := by
    rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
      forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingFamilyNext_new, T, U, Q, γ, s, forcingInverseCodePoset, forcingInverseCodeOrder]
  have hRnext : (forcingCodeR (woodinIterationPrefix θ)) ‘ j = twoStepOrder T U Q S ∅ := by
    rw [woodinIterationPrefix_order_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
      forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeR_code, forcingFamilyNext_new, T, U, Q, S, γ, s, forcingInverseCodePoset, forcingInverseCodeOrder]
  have hπ := hglobal.system.projection hiθ hj hij
  rw [← hPi, ← hRi, hPnext, hRnext] at hπ
  have hτ := (woodinInverseCoordinate_split hssub hi).projection
  have hK : (kpair.π₂ (woodinIterationRec j)) ‘ i = (woodinIterationCardinalPrefix j) ‘ i := by
    rw [hrec, kpair.π₂_kpair]
    simp only [woodinInverseCardinalNext, forcingFamilyNext_old hi]
  have hi' : i ∈ succ j := mem_succ_iff.mpr (Or.inr hi)
  have hcl := hclosure i hi' j (mem_succ_self j) hij
  unfold IterationQuotientClosedBelow at hcl
  rw [← woodinIterationPrefix_poset_value hs hj hi',
    ← woodinIterationPrefix_order_value hs hj hi',
    ← woodinIterationPrefix_top_value hs hj hi',
    ← woodinIterationPrefix_poset_value hs hj (mem_succ_self j),
    ← woodinIterationPrefix_order_value hs hj (mem_succ_self j),
    ← woodinIterationPrefix_projection_value hs hj hi' (mem_succ_self j),
    hK, ← hPi, ← hRi, ← hoi, hPnext, hRnext] at hcl
  apply projectionQuotient_closedBelow_forced_of_generics
    (hlocal.system.order.preorder i hi) (hlocal.system.tops.top i hi) hτ col.order.preorder
  intro G hG
  let A : ForcingContext V := ⟨_, _, _, G, hlocal.system.order.preorder i hi,
    hlocal.system.tops.top i hi, hG⟩
  have hfull := A.projectionQuotient_closedBelow_of_forced hπ
    (twoStep_preorder col.order.preorder col.tops.top hiter) hcl
  have hsplit := A.projectionQuotient_splitProjection hπ.maps hτ.maps
    (twoStep_splitProjection col.order.preorder col.tops.top hiter) ?_
  · change IsForcingClosedBelow (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ))
        (A.check ((woodinIterationCardinalPrefix j) ‘ i))
    let := ((woodinIterationPrefix_of_stages hssub).inaccessible i hi).1
    intro α hα
    let := IsOrdinal.of_mem hα
    exact hsplit.separative_closedAt_base (hfull α hα)
  · intro z hz
    rw [twoStepProjection_value hz]
    have hz' := hPnext.symm ▸ hz
    have hf := woodinInverse_first_mem hs hj h0 hlim hinac hz'
    rw [forcingThreadCoordinate_value hf]
    exact (woodinInverse_projection_value hs hj h0 hlim hinac hi hz').symm

theorem woodinEarlierRaw_code_quotient_closedBelow [Countable V] {δ θ j i : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (hi : i ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hclosure : HasWoodinQuotientClosure (succ j) (kpair.π₁ (woodinIterationRec j))
      (kpair.π₂ (woodinIterationRec j))) :
    IterationQuotientClosedBelow (forcingInverseCode j (woodinIterationPrefix j)) i j
      ((woodinIterationCardinalPrefix j) ‘ i) := by
  simpa only [IterationQuotientClosedBelow, forcingInverseCode, forcingThreadCode,
    forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code, forcingCodet_code,
    forcingCodeπ_code, forcingFamilyNext_old hi, forcingFamilyNext_new, forcingMatrixNext_column hi,
    forcingLimitProjectionColumn_value hi, forcingInverseCodePoset, forcingInverseCodeOrder,
    forcingInverseCodeTop] using woodinEarlierRaw_quotient_closedBelow hs hj hi hlim hinac hclosure

end ZFVP
