import ZFVP.ModelTheory.WoodinSuccessorLiftCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j)))
include hs

theorem woodinInverse_lift_value {j i a b : V} (hj : j ∈ θ) (hi : i ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (ha : a ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i) :
    ((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ =
      successorForcingLiftValue
        ((forcingLimitLiftColumn (forcingInverseCodePoset j (woodinIterationPrefix j)) j
          (forcingCodeP (woodinIterationPrefix j)) (forcingCodeπ (woodinIterationPrefix j))
          (forcingCodeL (woodinIterationPrefix j))) ‘ i) a b := by
  let := IsOrdinal.of_mem hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have hrec := woodinIterationRec_inverse h0 hlim hinac
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hc := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
  have hb' : b ∈ (forcingCodeP (woodinIterationPrefix j)) ‘ i := by
    rw [hc.tableP.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableP
      (woodinIterationPrefix_extends hsub).subP hi]
    exact hb
  have ha' := ha
  rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self _), hrec, kpair.π₁_kpair] at ha'
  simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code,
    forcingFamilyNext_new] at ha'
  rw [woodinIterationPrefix_lift_value hs hj (mem_succ_iff.mpr (Or.inr hi))
    (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeL_code,
    forcingMatrixNext_column hi, forcingTwoStepLiftColumn_value hi ha' hb']
  rfl

theorem woodinInverse_lift_tail {j i a b : V} (hj : j ∈ θ) (hi : i ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (ha : a ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i) :
    kpair.π₂ (((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ) =
      kpair.π₂ a := by
  rw [woodinInverse_lift_value hs hj hi hlim hinac ha hb]
  simp only [successorForcingLiftValue, twoStepStronger, kpair.π₂_kpair]

end ZFVP
