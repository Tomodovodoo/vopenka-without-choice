import ZFVP.ModelTheory.WoodinSourceLimitMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinInsertSeed_threadSplice {θ P π L f i b : V} [IsOrdinal θ]
    (hi : i ∈ θ) (hb : b ∈ P ‘ i) :
    woodinInsertSeed θ (forcingThreadSplice θ π L f i b) ∅ =
      forcingThreadSplice (woodinSourceIndex θ) (woodinSeedProjections θ P π)
        (woodinSeedLifts θ P L) (woodinInsertSeed θ f ∅) (woodinSourceIndex i) b := by
  classical
  let := IsOrdinal.of_mem hi
  have hfun : IsFunction (forcingThreadSplice (woodinSourceIndex θ)
      (woodinSeedProjections θ P π) (woodinSeedLifts θ P L)
        (woodinInsertSeed θ f ∅) (woodinSourceIndex i) b) := by
    unfold forcingThreadSplice
    infer_instance
  let := hfun
  apply functions_eq_of_domain_values
  · rw [woodinInsertSeed_domain]
    simp only [forcingThreadSplice, domain_definableGraph]
  · intro j hj
    rw [woodinInsertSeed_domain] at hj
    rw [forcingThreadSplice_value hj]
    rcases woodinSourceIndex_cases hj with rfl | ⟨k, hk, rfl⟩
    · have hz : (∅ : V) ∈ woodinSourceIndex i :=
        subset_ordinalAdd 1 i ∅ (by change (0 : V) ∈ succ 0; simp)
      rw [woodinInsertSeed_zero, forcingSpliceValue, ite_eq_left hz,
        woodinSeedProjections, woodinSeedMatrix_zero (woodinSourceIndex_mem_iff.mpr hi),
        woodinSeedProjectionColumn_value (woodinSourceIndex_mem_iff.mpr hi)]
      simpa only [woodinInsertSeed_at_sourceIndex hi] using hb
    · let := IsOrdinal.of_mem hk
      rw [woodinInsertSeed_at_sourceIndex hk, forcingThreadSplice_value hk]
      simp only [forcingSpliceValue, woodinSourceIndex_mem_iff,
        woodinSeedProjections, woodinSeedLifts, woodinSeedMatrix_at_sourceIndex hk hi,
        woodinSeedMatrix_at_sourceIndex hi hk, woodinInsertSeed_at_sourceIndex hk]

theorem woodinSourceCode_threadSplice {θ s f i b : V} [IsOrdinal θ]
    (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i) :
    woodinInsertSeed θ (forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) f i b) ∅ =
      forcingThreadSplice (woodinSourceIndex θ) (forcingCodeπ (woodinSourceCode θ s))
        (forcingCodeL (woodinSourceCode θ s)) (woodinInsertSeed θ f ∅) (woodinSourceIndex i) b := by
  simpa only [woodinSourceCode, forcingCodeπ_code, forcingCodeL_code] using
    woodinInsertSeed_threadSplice (π := forcingCodeπ s) (L := forcingCodeL s) (f := f) hi hb

theorem woodinSourceCode_limit_replacement {θ s C D f i b : V} [IsOrdinal θ]
    (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i) (hf : f ∈ C)
    (hm : woodinInsertSeed θ f ∅ ∈ D)
    (hg : forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) f i b ∈ C) :
    (woodinSeedThreadMap θ C) ‘
        (((forcingLimitLiftColumn C θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeL s)) ‘ i) ‘ ⟨f, b⟩ₖ) =
      ((forcingLimitLiftColumn D (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeL (woodinSourceCode θ s))) ‘
          (woodinSourceIndex i)) ‘ ⟨(woodinSeedThreadMap θ C) ‘ f, b⟩ₖ := by
  let := IsOrdinal.of_mem hi
  have hb' : b ∈ (forcingCodeP (woodinSourceCode θ s)) ‘ (woodinSourceIndex i) := by
    simpa only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_at_sourceIndex hi] using hb
  rw [forcingLimitLiftColumn_value hi, forcingLimitLift_value hf hb,
    forcingLimitLiftColumn_value (woodinSourceIndex_mem_iff.mpr hi),
    woodinSeedThreadMap, value_definableGraph _ _ _ hg, value_definableGraph _ _ _ hf,
    forcingLimitLift_value hm hb']
  exact woodinSourceCode_threadSplice hi hb

theorem woodinSourceCode_inverse_replacement {θ s f i b : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i)
    (hf : f ∈ forcingInverseCodePoset θ s) (hle : ⟨b, f ‘ i⟩ₖ ∈ (forcingCodeR s) ‘ i) :
    let C := forcingInverseCodePoset θ s
    let D := forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ s)
    (woodinSeedThreadMap θ C) ‘
        (((forcingLimitLiftColumn C θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeL s)) ‘ i) ‘ ⟨f, b⟩ₖ) =
      ((forcingLimitLiftColumn D (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeL (woodinSourceCode θ s))) ‘
          (woodinSourceIndex i)) ‘ ⟨(woodinSeedThreadMap θ C) ‘ f, b⟩ₖ := by
  apply woodinSourceCode_limit_replacement hi hb hf
  · have hm := function_value_mem (woodinSourceCode_inverse_isomorphism hs).1 hf
    rwa [woodinSeedThreadMap, value_definableGraph _ _ _ hf] at hm
  · exact forcingThreadSplice_mem hs.system.split hs.system.lifts hf hi hb hle hs.subset_universe

theorem woodinSourceCode_direct_replacement {θ s f i b : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i)
    (hf : f ∈ (forcingCodeP (forcingDirectCode θ s)) ‘ θ)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ (forcingCodeR s) ‘ i) :
    let C := (forcingCodeP (forcingDirectCode θ s)) ‘ θ
    let D := (forcingCodeP (forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ s))) ‘
      (woodinSourceIndex θ)
    (woodinSeedThreadMap θ C) ‘
        (((forcingLimitLiftColumn C θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeL s)) ‘ i) ‘ ⟨f, b⟩ₖ) =
      ((forcingLimitLiftColumn D (woodinSourceIndex θ) (forcingCodeP (woodinSourceCode θ s))
        (forcingCodeπ (woodinSourceCode θ s)) (forcingCodeL (woodinSourceCode θ s))) ‘
          (woodinSourceIndex i)) ‘ ⟨(woodinSeedThreadMap θ C) ‘ f, b⟩ₖ := by
  let := IsOrdinal.of_mem hi
  apply woodinSourceCode_limit_replacement hi hb hf
  · have hz : (∅ : V) ∈ θ := ordinal_mem_of_subset_mem (empty_subset i) hi
    have hm := function_value_mem (woodinSourceCode_direct_isomorphism hs hz).1 hf
    rwa [woodinSeedThreadMap, value_definableGraph _ _ _ hf] at hm
  · simp only [forcingDirectCode, forcingThreadCode_poset] at hf ⊢
    exact forcingThreadSplice_direct_mem hs.system.split hs.system.lifts hf hi hb hle
      hs.subset_universe (fun k hk j hj hik hkj a ha c hc hca ↦
        hs.system.compatible.compatible i hi k hk j hj hik hkj a ha c hc hca)

end ZFVP
