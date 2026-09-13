import ZFVP.ModelTheory.WoodinInverseLiftCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ j : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (h0 : j ≠ ∅)
  (hlim : j ≠ succ (⋃ˢ j))
  (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
include hs hj h0 hlim hinac

theorem woodinInverse_first_mem {c : V}
    (hc : c ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    kpair.π₁ c ∈ forcingInverseCodePoset j (woodinIterationPrefix j) := by
  let := IsOrdinal.of_mem hj
  have hrec := woodinIterationRec_inverse h0 hlim hinac
  rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self _), hrec, kpair.π₁_kpair] at hc
  simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code,
    forcingFamilyNext_new] at hc
  simpa only [twoStepProjection_value hc, forcingInverseCodePoset] using
    function_value_mem (twoStepProjection_maps _ _ _ _) hc

theorem woodinInverse_projection_value {i c : V} (hi : i ∈ j)
    (hc : c ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ c = (kpair.π₁ c) ‘ i := by
  let := IsOrdinal.of_mem hj
  have hrec := woodinIterationRec_inverse h0 hlim hinac
  have hc' := hc
  rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self _), hrec, kpair.π₁_kpair] at hc'
  simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code,
    forcingFamilyNext_new] at hc'
  rw [woodinIterationPrefix_projection_value hs hj (mem_succ_iff.mpr (Or.inr hi))
    (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeπ_code,
    forcingMatrixNext_column hi, forcingComposeProjectionColumn_value hi, forcingLimitProjectionColumn_value hi]
  rw [value_compose_of_mem_function (twoStepProjection_maps _ _ _ _) (forcingThreadCoordinate_maps hi) hc',
    twoStepProjection_value hc']
  have hh := woodinInverse_first_mem hs hj h0 hlim hinac hc
  unfold forcingInverseCodePoset at hh
  exact forcingThreadCoordinate_value hh

theorem woodinInverse_lift_first {i a b : V} (hi : i ∈ j)
    (ha : a ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i) :
    kpair.π₁ (((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ) =
      forcingThreadSplice j (forcingCodeπ (woodinIterationPrefix j))
        (forcingCodeL (woodinIterationPrefix j)) (kpair.π₁ a) i b := by
  let := IsOrdinal.of_mem hj
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hc := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
  have hb' : b ∈ (forcingCodeP (woodinIterationPrefix j)) ‘ i := by
    rw [hc.tableP.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableP
      (woodinIterationPrefix_extends hsub).subP hi]
    exact hb
  rw [woodinInverse_lift_value hs hj hi hlim hinac ha hb]
  simp only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair,
    forcingLimitLiftColumn_value hi,
    forcingLimitLift_value (woodinInverse_first_mem hs hj h0 hlim hinac ha) hb']

theorem woodinThread_inverse_coordinate {d : V}
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ)) :
    kpair.π₁ (d ‘ j) ∈ forcingInverseCodePoset j (woodinIterationPrefix j) ∧
      ∀ k ∈ j, d ‘ k = (kpair.π₁ (d ‘ j)) ‘ k := by
  have hdj := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 j hj
  refine ⟨woodinInverse_first_mem hs hj h0 hlim hinac hdj, ?_⟩
  intro k hk
  let := IsOrdinal.of_mem hj
  rw [← woodinInverseThread_project hs (IsOrdinal.toIsTransitive.mem_trans hk hj) hj
    (IsOrdinal.toIsTransitive.transitive _ hk) hd,
    woodinInverse_projection_value hs hj h0 hlim hinac hk hdj]

end ZFVP
