import ZFVP.ModelTheory.WoodinSourceCode
import ZFVP.ModelTheory.InverseCollapseCode
import ZFVP.SetTheory.ForcingLimitUniverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceCode_universe_zero {θ s : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) : (∅ : V) ∈ forcingCodeUniverse (woodinSourceCode θ s) := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  apply (woodinSourceCode_valid hs).subset_universe ∅ hz
  simp only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_zero, mem_singleton_iff]

theorem woodinSourceCode_universe_old {θ s : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) :
    ∀ i ∈ θ, (forcingCodeP s) ‘ i ⊆ forcingCodeUniverse (woodinSourceCode θ s) := by
  intro i hi
  let := IsOrdinal.of_mem hi
  have hh := (woodinSourceCode_valid hs).subset_universe (woodinSourceIndex i)
    (woodinSourceIndex_mem_iff.mpr hi)
  simpa only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_at_sourceIndex hi] using hh

theorem woodinSourceCode_inverse_isomorphism {θ s : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) :
    IsForcingIsomorphism (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s))
      (forcingInverseCodeOrder (woodinSourceIndex θ) (woodinSourceCode θ s))
      (woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) := by
  have he := forcingInverseLimit_universe_eq (π := forcingCodeπ s)
    (woodinSourceCode_universe_old hs) hs.subset_universe
  have hh := woodinSeed_inverseLimit_isomorphism (θ := θ) (P := forcingCodeP s) (R := forcingCodeR s)
    (π := forcingCodeπ s) (woodinSourceCode_universe_zero hs)
  rw [he] at hh
  simpa only [forcingInverseCodePoset, forcingInverseCodeOrder,
    woodinSourceCode, forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code] using hh

theorem woodinSourceCode_direct_isomorphism {θ s : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hzero : (∅ : V) ∈ θ) :
    IsForcingIsomorphism
      ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeR (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeP (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘ (woodinSourceIndex θ))
      ((forcingCodeR (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘ (woodinSourceIndex θ))
      (woodinSeedThreadMap θ ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)) := by
  have he := forcingDirectLimit_universe_eq (π := forcingCodeπ s) (E := forcingCodeE s)
    (woodinSourceCode_universe_old hs) hs.subset_universe
  have hh := woodinSeed_directLimit_isomorphism (P := forcingCodeP s) (R := forcingCodeR s)
    (π := forcingCodeπ s) (E := forcingCodeE s) (t := forcingCodet s)
    (woodinSourceCode_universe_zero hs) hzero hs.system.tops.secTop
  rw [he] at hh
  simpa only [forcingDirectCode, forcingThreadCode_poset, forcingThreadCode_order,
    woodinSourceCode, forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingCodeE_code] using hh

theorem woodinSourceCode_inverse_top {θ s : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hzero : (∅ : V) ∈ θ) :
    woodinInsertSeed θ (forcingInverseCodeTop θ s) ∅ =
      forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s) := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hfun : IsFunction (forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s)) := by
    unfold forcingInverseCodeTop forcingSectionThread
    infer_instance
  let := hfun
  apply functions_eq_of_domain_values
  · rw [woodinInsertSeed_domain]
    simp only [forcingInverseCodeTop, forcingSectionThread, domain_definableGraph]
  · intro i hi
    rw [woodinInsertSeed_domain] at hi
    have hv := forcingSectionThread_top_value (woodinSourceCode_valid hs).system.tops hz hi
    change (forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s)) ‘ i =
      (forcingCodet (woodinSourceCode θ s)) ‘ i at hv
    rw [hv]
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · simp only [woodinInsertSeed_zero, woodinSourceCode, forcingCodet_code]
    · rw [woodinInsertSeed_at_sourceIndex ha]
      have hh := forcingSectionThread_top_value hs.system.tops hzero ha
      change (forcingInverseCodeTop θ s) ‘ a = (forcingCodet s) ‘ a at hh
      rw [hh]
      simp only [woodinSourceCode, forcingCodet_code, woodinInsertSeed_at_sourceIndex ha]

theorem woodinSourceCode_inverse_projection {θ s α f : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hα : α ∈ θ) (hf : f ∈ forcingInverseCodePoset θ s) :
    ((forcingLimitProjectionColumn (woodinSourceIndex θ)
        (forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘ (woodinSourceIndex α)) ‘
        ((woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) ‘ f) =
      ((forcingLimitProjectionColumn θ (forcingInverseCodePoset θ s)) ‘ α) ‘ f := by
  let := IsOrdinal.of_mem hα
  have hmap := function_value_mem (woodinSourceCode_inverse_isomorphism hs).1 hf
  rw [woodinSeedThreadMap, value_definableGraph _ _ _ hf] at hmap ⊢
  rw [forcingLimitProjectionColumn_value (woodinSourceIndex_mem_iff.mpr hα),
    forcingThreadCoordinate_value hmap, forcingLimitProjectionColumn_value hα,
    forcingThreadCoordinate_value hf, woodinInsertSeed_at_sourceIndex hα]

theorem woodinSourceCode_successor_stage (k s K : V) [IsOrdinal k] :
    woodinIterationStage (woodinSourceCode (succ (succ k)) (woodinIterationSuccessor k s K))
      (woodinSourceCardinals (succ (succ k)) (woodinIterationCardinalNext k s K))
      (succ (woodinSourceIndex k)) =
    woodinSuccessorStep (woodinIterationStage (woodinSourceCode (succ k) s)
      (woodinSourceCardinals (succ k) K) (woodinSourceIndex k)) := by
  rw [← woodinSourceIndex_successor,
    woodinSourceCode_stage (mem_succ_self (succ k)), woodinIterationSuccessor_stage,
    woodinSourceCode_stage (mem_succ_self k)]

end ZFVP
