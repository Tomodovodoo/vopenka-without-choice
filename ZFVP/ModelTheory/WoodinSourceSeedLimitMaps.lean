import ZFVP.ModelTheory.WoodinSourceCompletedReplacement
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
theorem woodinSourceCode_threadSplice_seed {θ s f : V} [IsOrdinal θ]
    (hf : f ∈ forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s)) :
    forcingThreadSplice (woodinSourceIndex θ) (forcingCodeπ (woodinSourceCode θ s))
      (forcingCodeL (woodinSourceCode θ s)) f ∅ ∅ = f := by
  have hf' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  let := IsFunction.of_mem hf'.1
  have hfun : IsFunction (forcingThreadSplice (woodinSourceIndex θ)
      (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeL (woodinSourceCode θ s)) f ∅ ∅) := by
    unfold forcingThreadSplice
    infer_instance
  let := hfun
  apply functions_eq_of_domain_values
  · rw [forcingThreadSplice, domain_definableGraph, domain_eq_of_mem_function hf'.1]
  · intro j hj
    rw [forcingThreadSplice, domain_definableGraph] at hj
    rw [forcingThreadSplice_value hj]
    simp only [forcingSpliceValue, not_mem_empty, ↓reduceIte, woodinSourceCode, forcingCodeL_code]
    apply woodinSeedLifts_zero_value hj
    simpa only [woodinSourceCode, forcingCodeP_code] using hf'.2.1 j hj



theorem woodinSourceCode_thread_seed {θ s f : V} [IsOrdinal θ]
    (hf : f ∈ forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s)) :
    f ‘ ∅ = ∅ := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hm := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 ∅ hz
  simpa only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_zero, mem_singleton_iff] using hm

theorem woodinSourceCode_limit_seed_projection {θ s C f : V} [IsOrdinal θ]
    (hC : C ⊆ forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s))
    (hf : f ∈ C) :
    ((forcingLimitProjectionColumn (woodinSourceIndex θ) C) ‘ ∅) ‘ f = ∅ := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  rw [forcingLimitProjectionColumn_value hz, forcingThreadCoordinate_value hf]
  exact woodinSourceCode_thread_seed (hC f hf)

theorem woodinSourceCode_limit_seed_section {θ s : V} [IsOrdinal θ] :
    ((forcingLimitSectionColumn (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
      (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeE (woodinSourceCode θ s))) ‘ ∅) ‘ ∅ =
        forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s) := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hp : (∅ : V) ∈ (forcingCodeP (woodinSourceCode θ s)) ‘ ∅ := by
    simp only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_zero, mem_singleton_iff]
  rw [forcingLimitSectionColumn_value hz, forcingThreadSection_value hp]
  simp only [forcingInverseCodeTop, woodinSourceCode, forcingCodet_code, woodinInsertSeed_zero]

theorem woodinSourceCode_limit_seed_replacement {θ s C f : V} [IsOrdinal θ]
    (hC : C ⊆ forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s))
    (hf : f ∈ C) :
    ((forcingLimitLiftColumn C (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
      (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeL (woodinSourceCode θ s))) ‘ ∅) ‘ ⟨f, ∅⟩ₖ = f := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hp : (∅ : V) ∈ (forcingCodeP (woodinSourceCode θ s)) ‘ ∅ := by
    simp only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_zero, mem_singleton_iff]
  rw [forcingLimitLiftColumn_value hz, forcingLimitLift_value hf hp]
  exact woodinSourceCode_threadSplice_seed (hC f hf)


theorem woodinSourceCode_completed_seed_projection {θ s ζ γ x : V} [IsOrdinal θ]
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ (woodinSourceIndex θ)) :
    ((forcingCodeπ (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ) ‘ x = ∅ := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  rw [forcingInverseSourceCollapseCode_projection hz hx]
  exact woodinSourceCode_thread_seed (forcingInverseSourceCollapseCode_first hx)

theorem woodinSourceCode_completed_seed_section {θ s ζ γ : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) :
    ((forcingCodeE (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ) ‘ ∅ =
      ⟨forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s), ∅⟩ₖ := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hp : (∅ : V) ∈ (forcingCodeP (woodinSourceCode θ s)) ‘ ∅ := by
    simp only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_zero, mem_singleton_iff]
  rw [forcingInverseSourceCollapseCode_section (woodinSourceCode_valid hs) hz hp]
  simp only [forcingInverseCodeTop, woodinSourceCode, forcingCodet_code, woodinInsertSeed_zero]

theorem woodinSourceCode_completed_seed_replacement {θ s ζ γ x : V} [IsOrdinal θ]
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ (woodinSourceIndex θ)) :
    ((forcingCodeL (forcingInverseSourceCollapseCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) ζ γ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ) ‘ ⟨x, ∅⟩ₖ = x := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hp : (∅ : V) ∈ (forcingCodeP (woodinSourceCode θ s)) ‘ ∅ := by
    simp only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_zero, mem_singleton_iff]
  rw [forcingInverseSourceCollapseCode_replacement hz hp hx,
    woodinSourceCode_threadSplice_seed (forcingInverseSourceCollapseCode_first hx)]
  simp only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new] at hx
  obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hx
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
end ZFVP
