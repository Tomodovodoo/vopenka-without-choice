import ZFVP.ModelTheory.WoodinSourceLimits

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinInsertSeed_sectionThread {θ P π E t k p : V} [IsOrdinal θ]
    (hk : k ∈ θ) (hp : p ∈ P ‘ k) :
    woodinInsertSeed θ (forcingSectionThread θ π E k p) ∅ =
      forcingSectionThread (woodinSourceIndex θ) (woodinSeedProjections θ P π)
        (woodinSeedSections θ E t) (woodinSourceIndex k) p := by
  classical
  let := IsOrdinal.of_mem hk
  have hfun : IsFunction (forcingSectionThread (woodinSourceIndex θ)
      (woodinSeedProjections θ P π) (woodinSeedSections θ E t) (woodinSourceIndex k) p) := by
    unfold forcingSectionThread
    infer_instance
  let := hfun
  apply functions_eq_of_domain_values
  · rw [woodinInsertSeed_domain]
    simp only [forcingSectionThread, domain_definableGraph]
  · intro i hi
    rw [woodinInsertSeed_domain] at hi
    rw [forcingSectionThread_value hi]
    rcases woodinSourceIndex_cases hi with rfl | ⟨j, hj, rfl⟩
    · have hz : (∅ : V) ∈ woodinSourceIndex k :=
        subset_ordinalAdd 1 k ∅ (by change (0 : V) ∈ succ 0; simp)
      rw [woodinInsertSeed_zero, forcingSectionValue, ite_eq_left hz,
        woodinSeedProjections, woodinSeedMatrix_zero (woodinSourceIndex_mem_iff.mpr hk),
        woodinSeedProjectionColumn_value (woodinSourceIndex_mem_iff.mpr hk)]
      simpa only [woodinInsertSeed_at_sourceIndex hk] using hp
    · let := IsOrdinal.of_mem hj
      rw [woodinInsertSeed_at_sourceIndex hj, forcingSectionThread_value hj]
      simp only [forcingSectionValue, woodinSourceIndex_mem_iff,
        woodinSeedProjections, woodinSeedSections, woodinSeedMatrix_at_sourceIndex hj hk,
        woodinSeedMatrix_at_sourceIndex hk hj]

theorem woodinSourceCode_sectionThread {θ s k p : V} [IsOrdinal θ]
    (hk : k ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ k) :
    woodinInsertSeed θ (forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) k p) ∅ =
      forcingSectionThread (woodinSourceIndex θ) (forcingCodeπ (woodinSourceCode θ s))
        (forcingCodeE (woodinSourceCode θ s)) (woodinSourceIndex k) p := by
  simpa only [woodinSourceCode, forcingCodeπ_code, forcingCodeE_code] using
    woodinInsertSeed_sectionThread (π := forcingCodeπ s) (E := forcingCodeE s)
      (t := forcingCodet s) hk hp

theorem woodinSourceCode_direct_projection {θ s α f : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hzero : (∅ : V) ∈ θ) (hα : α ∈ θ)
    (hf : f ∈ (forcingCodeP (forcingDirectCode θ s)) ‘ θ) :
    ((forcingLimitProjectionColumn (woodinSourceIndex θ)
        ((forcingCodeP (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘
          (woodinSourceIndex θ))) ‘ (woodinSourceIndex α)) ‘
        ((woodinSeedThreadMap θ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)) ‘ f) =
      ((forcingLimitProjectionColumn θ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)) ‘ α) ‘ f := by
  let := IsOrdinal.of_mem hα
  have hmap := function_value_mem (woodinSourceCode_direct_isomorphism hs hzero).1 hf
  rw [woodinSeedThreadMap, value_definableGraph _ _ _ hf] at hmap ⊢
  rw [forcingLimitProjectionColumn_value (woodinSourceIndex_mem_iff.mpr hα),
    forcingThreadCoordinate_value hmap, forcingLimitProjectionColumn_value hα,
    forcingThreadCoordinate_value hf, woodinInsertSeed_at_sourceIndex hα]

theorem woodinSourceCode_limit_section {θ s C k p : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hk : k ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ k)
    (hC : forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s)
      (forcingCodeE s) (forcingCodeUniverse s) ⊆ C) :
    (woodinSeedThreadMap θ C) ‘
        (((forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s)) ‘ k) ‘ p) =
      ((forcingLimitSectionColumn (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeE (woodinSourceCode θ s))) ‘
          (woodinSourceIndex k)) ‘ p := by
  let := IsOrdinal.of_mem hk
  have hp' : p ∈ (forcingCodeP (woodinSourceCode θ s)) ‘ (woodinSourceIndex k) := by
    simpa only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_at_sourceIndex hk] using hp
  rw [forcingLimitSectionColumn_value hk, forcingThreadSection_value hp,
    forcingLimitSectionColumn_value (woodinSourceIndex_mem_iff.mpr hk), forcingThreadSection_value hp']
  have hm := hC _ (forcingSectionThread_mem hs.system.split hk hp hs.subset_universe)
  rw [woodinSeedThreadMap, value_definableGraph _ _ _ hm]
  exact woodinSourceCode_sectionThread hk hp

theorem woodinSourceCode_inverse_section {θ s k p : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hk : k ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ k) :
    (woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) ‘
        (((forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s)) ‘ k) ‘ p) =
      ((forcingLimitSectionColumn (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeE (woodinSourceCode θ s))) ‘
          (woodinSourceIndex k)) ‘ p :=
  woodinSourceCode_limit_section hs hk hp (forcingDirectLimit_subset _ _ _ _ _)

theorem woodinSourceCode_direct_section {θ s k p : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hk : k ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ k) :
    (woodinSeedThreadMap θ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)) ‘
        (((forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s)) ‘ k) ‘ p) =
      ((forcingLimitSectionColumn (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeE (woodinSourceCode θ s))) ‘
          (woodinSourceIndex k)) ‘ p := by
  apply woodinSourceCode_limit_section hs hk hp
  simp only [forcingDirectCode, forcingThreadCode_poset]
  exact subset_refl _

end ZFVP
