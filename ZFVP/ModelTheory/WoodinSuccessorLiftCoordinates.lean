import ZFVP.ModelTheory.WoodinSuccessorCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j)))
include hs

theorem woodinIterationPrefix_lift_value {j k l : V}
    (hj : j ∈ θ) (hk : k ∈ succ j) (hl : l ∈ succ j) :
    (forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨k, l⟩ₖ =
      (forcingCodeL (kpair.π₁ (woodinIterationRec j))) ‘ ⟨k, l⟩ₖ :=
  ((hs j hj).code.tableL.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableL
    (woodinIterationRec_extends_to_prefix hj).subL (mem_prod_iff.mpr ⟨k, hk, l, hl, rfl⟩)).symm

theorem woodinSuccessor_lift_value {k i a b : V} (hk : succ k ∈ θ) (hi : i ∈ succ k)
    (ha : a ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k))
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i) :
    ((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨a, b⟩ₖ =
      successorForcingLiftValue ((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, k⟩ₖ) a b := by
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem (mem_succ_self k)
  have hkθ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hhist := woodinIterationHistory_of_stages
    (fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hk))
  have hrec := woodinIterationRec_successor_of_history hhist
  have ha' := ha
  rw [woodinIterationPrefix_poset_value hs hk (mem_succ_self _), hrec, kpair.π₁_kpair] at ha'
  simp only [woodinIterationSuccessor, forcingSuccessorCode_poset] at ha'
  have hb' := hb
  rw [woodinIterationPrefix_poset_value hs hkθ hi] at hb'
  rw [woodinIterationPrefix_lift_value hs hk
    (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self _), hrec, kpair.π₁_kpair]
  simp only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeL_code, forcingMatrixNext_column hi, successorLiftColumn_value hi ha' hb']
  rw [woodinIterationPrefix_lift_value hs hkθ hi (mem_succ_self k)]

theorem woodinSuccessor_lift_tail {k i a b : V} (hk : succ k ∈ θ) (hi : i ∈ succ k)
    (ha : a ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k))
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i) :
    kpair.π₂ (((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨a, b⟩ₖ) =
      kpair.π₂ a := by
  rw [woodinSuccessor_lift_value hs hk hi ha hb]
  simp only [successorForcingLiftValue, twoStepStronger, kpair.π₂_kpair]

end ZFVP
