import ZFVP.SetTheory.FixedPrefixCutoffTests
import ZFVP.ModelTheory.WoodinSparseOwnCutoffs
import ZFVP.ModelTheory.WoodinSparseSourceInvariant

/-! The fixed low-complexity tests at the actual sparse successor parameters.
Existence of a successful cutoff is obtained from the constructed iteration. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinPrefixCutoff_least_of_inaccessible {P R one κ : V}
    (hc : IsChoicelessInaccessible (woodinPrefixCutoff P R one κ)) :
    IsLeastOrdinal (IsWoodinPrefixCutoff P R one κ) (woodinPrefixCutoff P R one κ) := by
  have he := (leastOrdinalOrZero_eq_iff (IsWoodinPrefixCutoff P R one) (by definability)
    κ (woodinPrefixCutoff P R one κ)).mp rfl
  rcases he with h | ⟨_, hzero⟩
  · exact h
  · have hw := hc.2.1
    rw [hzero, zero_def] at hw
    exact (not_mem_empty hw).elim

theorem IsWoodinIteration.fixed_successorCutoff_tests {Ω k s K : V} [IsOrdinal k]
    (h : IsWoodinIteration Ω (succ k) s K) (hΩ : IsWoodinSupercompact Ω) :
    let P := (forcingCodeP s) ‘ k
    let R := (forcingCodeR s) ‘ k
    let one := (forcingCodet s) ‘ k
    let κ := K ‘ k
    let δ := woodinPrefixCutoff P R one κ
    fixedPiTwoPrefixCutoffFormula.Evalb ![P, R, one, κ, δ] ∧
      fixedSigmaTwoSmallerPrefixFailuresFormula.Evalb ![P, R, one, κ, δ] := by
  dsimp only
  obtain ⟨hR, ht, hc, _, _, _⟩ := h.normalizationSuccessor_inputs hΩ
  have hκ := h.inaccessible k (mem_succ_self k)
  let := hκ.1
  have hk : (∅ : V) ∈ K ‘ k := IsOrdinal.toIsTransitive.mem_trans (by simp) hκ.2.1
  have hleast := woodinPrefixCutoff_least_of_inaccessible hc
  refine ⟨(eval_fixedPiTwoPrefixCutoffFormula hR ht hk).mpr hleast.2.1, ?_⟩
  exact (eval_fixedSigmaTwoSmallerPrefixFailuresFormula hR ht hk).mpr
    ((isLeastOrdinal_iff_no_smaller _ _).mp hleast).2.2

theorem IsWoodinIteration.fixed_successorSelector_iff {Ω k s K : V} [IsOrdinal k]
    (h : IsWoodinIteration Ω (succ k) s K) (hΩ : IsWoodinSupercompact Ω) (δ : V) :
    fixedSuccessfulPrefixSelectorFormula.Evalb
      ![δ, (forcingCodeP s) ‘ k, (forcingCodeR s) ‘ k, (forcingCodet s) ‘ k, K ‘ k] ↔
      δ = woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k) := by
  obtain ⟨hR, ht, hc, _, _, _⟩ := h.normalizationSuccessor_inputs hΩ
  have hκ := h.inaccessible k (mem_succ_self k)
  let := hκ.1
  have hk : (∅ : V) ∈ K ‘ k := IsOrdinal.toIsTransitive.mem_trans (by simp) hκ.2.1
  exact eval_fixedSuccessfulPrefixSelectorFormula hR ht hk
    ⟨_, (woodinPrefixCutoff_least_of_inaccessible hc).2.1⟩

theorem woodinSparse_fixed_successorCutoff_tests {Ω k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    let c := woodinSparsePrefixCode (succ k)
    let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k
    let δ := (kpair.π₂ (woodinIterationRec (succ k))) ‘ (succ k)
    fixedPiTwoPrefixCutoffFormula.Evalb
      ![(forcingCodeP c) ‘ k, (forcingCodeR c) ‘ k, (forcingCodet c) ‘ k, κ, δ] ∧
    fixedSigmaTwoSmallerPrefixFailuresFormula.Evalb
      ![(forcingCodeP c) ‘ k, (forcingCodeR c) ‘ k, (forcingCodet c) ‘ k, κ, δ] := by
  let := hΩ.inaccessible.1
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have hs := woodinSparsePrefixCode_invariant hΩ hAC hsub
  have h := hs.fixed_successorCutoff_tests hΩ
  dsimp only at h ⊢
  rw [woodinIterationCardinalPrefix_value hΩ hAC hsub (mem_succ_self k),
    woodinSparsePrefix_successor_cutoff hΩ hAC hk] at h
  exact h

theorem woodinSparse_fixed_successorSelector_iff {Ω k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) (δ : V) :
    let c := woodinSparsePrefixCode (succ k)
    fixedSuccessfulPrefixSelectorFormula.Evalb
      ![δ, (forcingCodeP c) ‘ k, (forcingCodeR c) ‘ k, (forcingCodet c) ‘ k,
        (kpair.π₂ (woodinIterationRec k)) ‘ k] ↔
      δ = (kpair.π₂ (woodinIterationRec (succ k))) ‘ (succ k) := by
  let := hΩ.inaccessible.1
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have h := (woodinSparsePrefixCode_invariant hΩ hAC hsub).fixed_successorSelector_iff hΩ δ
  rw [woodinIterationCardinalPrefix_value hΩ hAC hsub (mem_succ_self k),
    woodinSparsePrefix_successor_cutoff hΩ hAC hk] at h
  exact h

end ZFVP
