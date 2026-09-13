import ZFVP.ModelTheory.WoodinRecursionHistory

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem iterationTableUnion_eq_max {I k : V} {F : V → V}
    (hF : ℒₛₑₜ-function₁ F) (hk : k ∈ I) (hmax : ∀ i ∈ I, F i ⊆ F k) :
    iterationTableUnion I F hF = F k := by
  apply SetTheory.subset_antisymm
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hy
    exact hmax i hi x hxy
  · intro x hx
    exact mem_sUnion_iff.mpr ⟨F k, (repl_spec hF).mpr ⟨k, hk, rfl⟩, hx⟩

theorem IsForcingIterationHistory.successor_union {k H : V} [IsOrdinal k]
    (h : IsForcingIterationHistory (succ k) H) :
    forcingIterationCodeUnion (succ k) H =
      forcingIterationCode (forcingCodeP (H ‘ k)) (forcingCodeR (H ‘ k))
        (forcingCodeπ (H ‘ k)) (forcingCodeE (H ‘ k)) (forcingCodeL (H ‘ k))
        (forcingCodet (H ‘ k)) := by
  have he (i : V) (hi : i ∈ succ k) : ForcingCodeExtends (H ‘ i) (H ‘ k) := by
    apply h.increasing i hi k (mem_succ_self k)
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  unfold forcingIterationCodeUnion forcingHistoryTable
  rw [iterationTableUnion_eq_max (by definability) (mem_succ_self k) (fun i hi ↦ (he i hi).subP),
    iterationTableUnion_eq_max (by definability) (mem_succ_self k) (fun i hi ↦ (he i hi).subR),
    iterationTableUnion_eq_max (by definability) (mem_succ_self k) (fun i hi ↦ (he i hi).subπ),
    iterationTableUnion_eq_max (by definability) (mem_succ_self k) (fun i hi ↦ (he i hi).subE),
    iterationTableUnion_eq_max (by definability) (mem_succ_self k) (fun i hi ↦ (he i hi).subL),
    iterationTableUnion_eq_max (by definability) (mem_succ_self k) (fun i hi ↦ (he i hi).subt)]

theorem IsWoodinIterationHistory.successor_cardinal_union {δ k H J : V} [IsOrdinal k]
    (h : IsWoodinIterationHistory δ (succ k) H J) :
    woodinHistoryCardinalUnion (succ k) J = J ‘ k := by
  apply iterationTableUnion_eq_max (by definability) (mem_succ_self k)
  intro i hi
  apply h.increasing i hi k (mem_succ_self k)
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact subset_refl _
  · exact IsOrdinal.toIsTransitive.transitive _ hi

theorem woodinIterationRec_code_packed (θ : V) [IsOrdinal θ] :
    forcingIterationCode (forcingCodeP (kpair.π₁ (woodinIterationRec θ)))
      (forcingCodeR (kpair.π₁ (woodinIterationRec θ)))
      (forcingCodeπ (kpair.π₁ (woodinIterationRec θ)))
      (forcingCodeE (kpair.π₁ (woodinIterationRec θ)))
      (forcingCodeL (kpair.π₁ (woodinIterationRec θ)))
      (forcingCodet (kpair.π₁ (woodinIterationRec θ))) = kpair.π₁ (woodinIterationRec θ) := by
  classical
  rw [woodinIterationRec_rule]
  unfold woodinStageRule
  split_ifs <;>
    simp only [kpair.π₁_kpair, woodinInitialCode, forcingInitialCode,
      woodinIterationSuccessor, forcingSuccessorCode, forcingDirectCode, forcingThreadCode,
      woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
      forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingCodeE_code,
      forcingCodeL_code, forcingCodet_code]

theorem woodinIterationPrefix_successor {δ k : V} [IsOrdinal k]
    (h : IsWoodinIterationHistory δ (succ k)
      (woodinHistoryCodes (woodinIterationHistory (succ k)))
      (woodinHistoryCardinals (woodinIterationHistory (succ k)))) :
    woodinIterationPrefix (succ k) = kpair.π₁ (woodinIterationRec k) ∧
      woodinIterationCardinalPrefix (succ k) = kpair.π₂ (woodinIterationRec k) := by
  constructor
  · unfold woodinIterationPrefix
    rw [h.codes.successor_union, woodinIterationHistory_code_value (mem_succ_self k)]
    exact woodinIterationRec_code_packed k
  · unfold woodinIterationCardinalPrefix
    rw [h.successor_cardinal_union, woodinIterationHistory_cardinal_value (mem_succ_self k)]

theorem woodinIterationRec_successor_of_history {δ k : V} [IsOrdinal k]
    (h : IsWoodinIterationHistory δ (succ k)
      (woodinHistoryCodes (woodinIterationHistory (succ k)))
      (woodinHistoryCardinals (woodinIterationHistory (succ k)))) :
    woodinIterationRec (succ k) =
      ⟨woodinIterationSuccessor k (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k)),
        woodinIterationCardinalNext k (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k))⟩ₖ := by
  rw [woodinIterationRec_successor, (woodinIterationPrefix_successor h).1,
    (woodinIterationPrefix_successor h).2]

end ZFVP

