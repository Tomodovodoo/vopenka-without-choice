import ZFVP.ModelTheory.WoodinCoordinateProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ k : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j))) (hk : succ k ∈ θ)
include hs hk

theorem woodinSuccessor_projection_first {c : V}
    (hc : c ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k)) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, succ k⟩ₖ) ‘ c = kpair.π₁ c := by
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem (mem_succ_self k)
  have hhist := woodinIterationHistory_of_stages
    (fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hk))
  have hrec := woodinIterationRec_successor_of_history hhist
  have hc' := hc
  rw [woodinIterationPrefix_poset_value hs hk (mem_succ_self _), hrec, kpair.π₁_kpair] at hc'
  simp only [woodinIterationSuccessor, forcingSuccessorCode_poset] at hc'
  have hfirst := function_value_mem (twoStepProjection_maps _ _ _ _) hc'
  rw [twoStepProjection_value hc'] at hfirst
  rw [woodinIterationPrefix_projection_value hs hk
    (mem_succ_iff.mpr (Or.inr (mem_succ_self k))) (mem_succ_self _), hrec, kpair.π₁_kpair]
  simp only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeπ_code, forcingMatrixNext_column (mem_succ_self k),
    successorProjectionColumn_value (mem_succ_self k) hc']
  exact (hs k (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk)).code.system.split.projId
    (mem_succ_self k) hfirst

theorem woodinSuccessor_projection_comp {i c : V} (hi : i ∈ succ k)
    (hc : c ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k)) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ c) =
      ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, succ k⟩ₖ) ‘ c := by
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem (mem_succ_self k)
  let := IsOrdinal.of_mem hi
  have h := (woodinIterationPrefix_of_stages hs).code.system.split
  rw [← woodinSuccessor_projection_first hs hk hc]
  exact h.projComp i (IsOrdinal.toIsTransitive.mem_trans hi hk)
    k (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk) (succ k) hk
    (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi))
    (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)) c hc

theorem woodinInverseThread_successor_first {d : V}
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ)) :
    kpair.π₁ (d ‘ (succ k)) = d ‘ k := by
  let := IsOrdinal.of_mem hk
  have hc := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 (succ k) hk
  rw [← woodinSuccessor_projection_first hs hk hc]
  exact woodinInverseThread_project hs
    (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk) hk
    (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)) hd

end ZFVP
