import ZFVP.ModelTheory.WoodinPrefixCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j)))
include hs

theorem woodinIterationPrefix_section_successor {k b q : V} [IsOrdinal k]
    (hk : succ k ∈ θ) (hb : b ∈ succ k)
    (hq : q ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ b) :
    ((forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨b, succ k⟩ₖ) ‘ q =
      ⟨((forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨b, k⟩ₖ) ‘ q, ∅⟩ₖ := by
  have hhist := woodinIterationHistory_of_stages
    (fun j hj ↦ hs j (IsOrdinal.toIsTransitive.mem_trans hj hk))
  have hrec := woodinIterationRec_successor_of_history hhist
  have hkθ : k ∈ θ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hqb := hq
  rw [woodinIterationPrefix_poset_value hs hkθ hb] at hqb
  rw [woodinIterationPrefix_section_value hs hk (mem_succ_iff.mpr (Or.inr hb))
    (mem_succ_self (succ k)), hrec, kpair.π₁_kpair]
  simp only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeE_code, forcingMatrixNext_column hb, successorSectionColumn_value hb hqb]
  rw [woodinIterationPrefix_section_value hs hkθ hb (mem_succ_self k)]

theorem woodinIterationPrefix_section_direct {j b q : V}
    (hj : j ∈ θ) (hb : b ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hq : q ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ b) :
    ((forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨b, j⟩ₖ) ‘ q =
      forcingSectionThread j (forcingCodeπ (woodinIterationPrefix j))
        (forcingCodeE (woodinIterationPrefix j)) b q := by
  let := IsOrdinal.of_mem hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hb
  have hrec := woodinIterationRec_direct h0 hlim hinac
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hc := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
  have hqj : q ∈ (forcingCodeP (woodinIterationPrefix j)) ‘ b := by
    rw [hc.tableP.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableP
      (woodinIterationPrefix_extends hsub).subP hb]
    exact hq
  rw [woodinIterationPrefix_section_value hs hj (mem_succ_iff.mpr (Or.inr hb))
    (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeE_code,
    forcingMatrixNext_column hb, forcingLimitSectionColumn_value hb, forcingThreadSection_value hqj]

theorem woodinIterationPrefix_section_inverse {j b q : V}
    (hj : j ∈ θ) (hb : b ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hq : q ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ b) :
    ((forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨b, j⟩ₖ) ‘ q =
      ⟨forcingSectionThread j (forcingCodeπ (woodinIterationPrefix j))
        (forcingCodeE (woodinIterationPrefix j)) b q, ∅⟩ₖ := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hb
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hb
  have hrec := woodinIterationRec_inverse h0 hlim hinac
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hc := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
  have hqj : q ∈ (forcingCodeP (woodinIterationPrefix j)) ‘ b := by
    rw [hc.tableP.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableP
      (woodinIterationPrefix_extends hsub).subP hb]
    exact hq
  have col := hc.system.inverseColumn (ordinal_mem_of_subset_mem (empty_subset b) hb) hc.subset_universe
  have hF := col.functions.sectionMap b hb
  rw [forcingLimitSectionColumn_value hb] at hF
  let C := forcingInverseCodePoset j (woodinIterationPrefix j)
  have he : twoStepSection C (∅ : V) ∈ (C ×ˢ {∅}) ^ C := by
    apply definableGraph_mem_function_of_mapsTo
    intro x hx
    exact kpair_mem_iff.mpr ⟨hx, by simp⟩
  have hH : forcingSectionThread j (forcingCodeπ (woodinIterationPrefix j))
      (forcingCodeE (woodinIterationPrefix j)) b q ∈ C := by
    simpa only [C, forcingInverseCodePoset, forcingThreadSection_value hqj] using function_value_mem hF hqj
  rw [woodinIterationPrefix_section_value hs hj (mem_succ_iff.mpr (Or.inr hb))
    (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeE_code,
    forcingMatrixNext_column hb, forcingComposeSectionColumn_value hb, forcingLimitSectionColumn_value hb]
  dsimp only [C, forcingInverseCodePoset] at he hH
  rw [value_compose_of_mem_function hF he hqj, forcingThreadSection_value hqj]
  exact twoStepSection_value hH

end ZFVP
