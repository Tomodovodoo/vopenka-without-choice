import ZFVP.ModelTheory.WoodinEarlierRawClosure
import ZFVP.ModelTheory.WoodinInverseStagePreservation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ j : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (h0 : j ≠ ∅)
  (hlim : j ≠ succ (⋃ˢ j))
  (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
  (hclosure : HasWoodinQuotientClosure (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j)))
include hs hj h0 hlim hinac hclosure

theorem woodinEarlierRaw_singular_forced [Countable V] :
    ∀ p ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      p ∈ forcingFormula (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j)) singularLimitStageFormula
        (standardTuple ![checkName (forcingInverseCodeTop j (woodinIterationPrefix j))
          (woodinLimitCardinal (woodinIterationCardinalPrefix j))]) := by
  let := IsOrdinal.of_mem hj
  have h0j : (∅ : V) ∈ j := (IsOrdinal.subset_iff.mp (empty_subset j)).resolve_left (fun he ↦ h0 he.symm)
  have h := woodinIterationPrefix_of_stages
    (fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj))
  exact h.inverse_stage_forced_of_quotient_closure h0j (ordinal_limit_of_not_successor hlim) hinac
    (fun i hi ↦ woodinEarlierRaw_code_quotient_closedBelow hs hj hi hlim hinac hclosure)

theorem woodinEarlierRaw_hartogs_regular [Countable V] :
    ∀ p ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      p ∈ forcingFormula (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j)) regularCardinalFormula
        (standardTuple ![forcingInverseHartogsName j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j))]) := by
  let := IsOrdinal.of_mem hj
  have h0j : (∅ : V) ∈ j := (IsOrdinal.subset_iff.mp (empty_subset j)).resolve_left (fun he ↦ h0 he.symm)
  have h := (woodinIterationPrefix_of_stages
    (fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj))).code
  have col := h.system.inverseColumn h0j h.subset_universe
  let ν : ForcingName (forcingInverseCodePoset j (woodinIterationPrefix j)) :=
    ⟨checkName (forcingInverseCodeTop j (woodinIterationPrefix j))
      (woodinLimitCardinal (woodinIterationCardinalPrefix j)), checkName_isName col.tops.top.1 _⟩
  intro p hp
  have hf := woodinEarlierRaw_singular_forced hs hj h0 hlim hinac hclosure p hp
  apply hartogsNumberName_forces_regular col.order.preorder col.tops.top hp ν ?_ ?_
  · apply forcingFormula_entailment singularLimitStageFormula
      (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_ col.order.preorder col.tops.top hp ![ν] hf
    intro W _ _ _ v hv
    have hh : IsLimitOfRegularCardinals (v 0) ∧ InternalDependentChoiceAt (v 0) := (Defined.eval_iff _).mp hv
    change regularCardinalFormula.Evalb v ∨ limitOfRegularCardinalsFormula.Evalb v
    exact Or.inr ((Defined.eval_iff _).mpr hh.1)
  · rw [singularLimitStageFormula, forcingFormula_and, mem_inter_iff] at hf
    exact hf.2

end ZFVP
