import ZFVP.ModelTheory.WoodinPrefixCoordinates
import ZFVP.ModelTheory.WoodinQuotientBoundEquations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

variable {δ θ ξ i p f : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j))) (hi : i ∈ θ)

include hs hi

theorem woodinQuotientBoundRec_before_base {j : V} (hj : j ∈ succ i)
    (hp : p ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i) :
    woodinQuotientBoundRec ξ i p f j =
      ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨j, i⟩ₖ) ‘ p := by
  let := IsOrdinal.of_mem hi
  rcases mem_succ_iff.mp hj with rfl | hj
  · rw [woodinQuotientBoundRec_base]
    exact ((woodinIterationPrefix_of_stages hs).code.system.split.projId hi hp).symm
  · rw [woodinQuotientBoundRec_before hj,
      woodinIterationPrefix_projection_value hs hi (mem_succ_iff.mpr (Or.inr hj)) (mem_succ_self i)]

theorem woodinQuotientBoundRec_projects_before_base {j k : V}
    (hj : j ∈ succ i) (hk : k ∈ succ j)
    (hp : p ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, j⟩ₖ) ‘ (woodinQuotientBoundRec ξ i p f j) =
      woodinQuotientBoundRec ξ i p f k := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hk
  have hji : j ⊆ i := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hj)
  have hkj : k ⊆ j := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hk)
  have hjθ : j ∈ θ := ordinal_mem_of_subset_mem hji hi
  have hkθ : k ∈ θ := ordinal_mem_of_subset_mem hkj hjθ
  have hki : k ∈ succ i := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_trans hkj hji))
  rw [woodinQuotientBoundRec_before_base hs hi hj hp, woodinQuotientBoundRec_before_base hs hi hki hp]
  exact (woodinIterationPrefix_of_stages hs).code.system.split.projComp k hkθ j hjθ i hi hkj hji p hp

omit hi in
theorem woodinQuotientBoundRec_projects_successor {k l : V} [IsOrdinal k]
    (hk : succ k ∈ θ) (hik : i ∈ succ k) (hl : l ∈ succ k)
    (hq : woodinQuotientBoundRec ξ i p f (succ k) ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k))
    (hprev : ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨l, k⟩ₖ) ‘
      (woodinQuotientBoundRec ξ i p f k) = woodinQuotientBoundRec ξ i p f l) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨l, succ k⟩ₖ) ‘
      (woodinQuotientBoundRec ξ i p f (succ k)) = woodinQuotientBoundRec ξ i p f l := by
  have hhist := woodinIterationHistory_of_stages
    (fun j hj ↦ hs j (IsOrdinal.toIsTransitive.mem_trans hj hk))
  have hrec := woodinIterationRec_successor_of_history hhist
  have hkθ : k ∈ θ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  rw [woodinIterationPrefix_poset_value hs hk (mem_succ_self (succ k)), hrec, kpair.π₁_kpair] at hq
  simp only [woodinIterationSuccessor, forcingSuccessorCode_poset] at hq
  rw [woodinIterationPrefix_projection_value hs hk (mem_succ_iff.mpr (Or.inr hl))
    (mem_succ_self (succ k)), hrec, kpair.π₁_kpair]
  simp only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeπ_code, forcingMatrixNext_column hl, successorProjectionColumn_value hl hq]
  rw [woodinQuotientBoundRec_successor hik, kpair.π₁_kpair,
    ← woodinIterationPrefix_projection_value hs hkθ hl (mem_succ_self k)]
  exact hprev

omit hi in
theorem woodinQuotientBoundRec_projects_direct {j k : V}
    (hj : j ∈ θ) (hij : i ∈ j) (hk : k ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hq : woodinQuotientBoundRec ξ i p f j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, j⟩ₖ) ‘
      (woodinQuotientBoundRec ξ i p f j) = woodinQuotientBoundRec ξ i p f k := by
  let := IsOrdinal.of_mem hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hij
  have hrec := woodinIterationRec_direct h0 hlim hinac
  rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair] at hq
  simp only [forcingDirectCode, forcingThreadCode_poset] at hq
  rw [woodinIterationPrefix_projection_value hs hj (mem_succ_iff.mpr (Or.inr hk))
    (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeπ_code,
    forcingMatrixNext_column hk, forcingLimitProjectionColumn_value hk]
  rw [forcingThreadCoordinate_value hq, woodinQuotientBoundRec_direct hij hlim hinac,
    woodinQuotientBoundHistory_value hk]

omit hi in
theorem woodinQuotientBoundRec_projects_inverse {j k : V}
    (hj : j ∈ θ) (hij : i ∈ j) (hk : k ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hq : woodinQuotientBoundRec ξ i p f j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, j⟩ₖ) ‘
      (woodinQuotientBoundRec ξ i p f j) = woodinQuotientBoundRec ξ i p f k := by
  let := IsOrdinal.of_mem hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hij
  have hrec := woodinIterationRec_inverse h0 hlim hinac
  rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair] at hq
  simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingFamilyNext_new] at hq
  have hH := function_value_mem (twoStepProjection_maps _ _ _ _) hq
  rw [twoStepProjection_value hq] at hH
  rw [woodinIterationPrefix_projection_value hs hj (mem_succ_iff.mpr (Or.inr hk))
    (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeπ_code,
    forcingMatrixNext_column hk, forcingComposeProjectionColumn_value hk, forcingLimitProjectionColumn_value hk]
  rw [value_compose_of_mem_function (twoStepProjection_maps _ _ _ _) (forcingThreadCoordinate_maps hk) hq,
    twoStepProjection_value hq, forcingThreadCoordinate_value hH,
    woodinQuotientBoundRec_inverse hij hlim hinac, kpair.π₁_kpair, woodinQuotientBoundHistory_value hk]

theorem woodinQuotientBoundRec_projects_of_membership
    (hmem : ∀ j ∈ θ, woodinQuotientBoundRec ξ i p f j ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    ∀ j ∈ θ, ∀ k ∈ succ j,
      ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, j⟩ₖ) ‘
        (woodinQuotientBoundRec ξ i p f j) = woodinQuotientBoundRec ξ i p f k := by
  let := IsOrdinal.of_mem hi
  have hp : p ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i := by
    simpa only [woodinQuotientBoundRec_base] using hmem i hi
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hall := transfinite_induction
    (fun j : V ↦ j ∈ θ → ∀ k ∈ succ j,
      ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, j⟩ₖ) ‘
        (woodinQuotientBoundRec ξ i p f j) = woodinQuotientBoundRec ξ i p f k)
    (by definability) ?_
  · intro j hj
    let := IsOrdinal.of_mem hj
    exact hall (IsOrdinal.toOrdinal j) hj
  intro j ih hj k hk
  rcases mem_succ_iff.mp hk with rfl | hk
  · exact hc.system.split.projId hj (hmem j hj)
  by_cases hji : (j : V) ∈ succ i
  · exact woodinQuotientBoundRec_projects_before_base hs hi hji (mem_succ_iff.mpr (Or.inr hk)) hp
  have hij : i ∈ (j : V) := by
    rcases IsOrdinal.mem_trichotomy i (j : V) with hij | he | hji'
    · exact hij
    · exact False.elim (hji (he ▸ mem_succ_self i))
    · exact False.elim (hji (mem_succ_iff.mpr (Or.inr hji')))
  by_cases hsucc : (j : V) = succ (⋃ˢ (j : V))
  · have hkprev : ⋃ˢ (j : V) ∈ (j : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (j : V)) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ (j : V)))
    let := IsOrdinal.of_mem hkprev
    have hprev := ih (IsOrdinal.toOrdinal (⋃ˢ (j : V))) hkprev
      (IsOrdinal.toIsTransitive.mem_trans hkprev hj) k (hsucc ▸ hk)
    have hh := woodinQuotientBoundRec_projects_successor hs (hsucc ▸ hj)
      (hsucc ▸ hij) (hsucc ▸ hk) (hsucc ▸ hmem j hj) hprev
    change ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, succ (⋃ˢ (j : V))⟩ₖ) ‘
      (woodinQuotientBoundRec ξ i p f (succ (⋃ˢ (j : V)))) = woodinQuotientBoundRec ξ i p f k at hh
    rwa [← hsucc] at hh
  · by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (j : V)))
    · exact woodinQuotientBoundRec_projects_direct hs hj hij hk hsucc hinac (hmem j hj)
    · exact woodinQuotientBoundRec_projects_inverse hs hj hij hk hsucc hinac (hmem j hj)

theorem woodinQuotientBoundHistory_mem_inverse_of_membership
    (hmem : ∀ j ∈ θ, woodinQuotientBoundRec ξ i p f j ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    woodinQuotientBoundHistory ξ i p f θ ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ) := by
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  have hc := (woodinIterationPrefix_of_stages hs).code
  refine ⟨?_, ?_, ?_⟩
  · apply (woodinQuotientBoundHistory_table ξ i p f θ).mem_function
    intro j hj
    rw [woodinQuotientBoundHistory_value hj]
    exact hc.subset_universe j hj _ (hmem j hj)
  · intro j hj
    rw [woodinQuotientBoundHistory_value hj]
    exact hmem j hj
  · intro j hj k hk hkθ
    rw [woodinQuotientBoundHistory_value hj, woodinQuotientBoundHistory_value hkθ]
    exact woodinQuotientBoundRec_projects_of_membership hs hi hmem j hj k (mem_succ_iff.mpr (Or.inr hk))

theorem woodinQuotientBoundHistory_inverse_condition
    (hmem : ∀ j ∈ θ, woodinQuotientBoundRec ξ i p f j ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    woodinQuotientBoundHistory ξ i p f θ ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ) ∧
      (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘
        (woodinQuotientBoundHistory ξ i p f θ) = p := by
  have hm := woodinQuotientBoundHistory_mem_inverse_of_membership hs hi hmem
  refine ⟨hm, ?_⟩
  let := IsOrdinal.of_mem hi
  rw [forcingThreadCoordinate_value hm, woodinQuotientBoundHistory_value hi, woodinQuotientBoundRec_base]

end ZFVP
