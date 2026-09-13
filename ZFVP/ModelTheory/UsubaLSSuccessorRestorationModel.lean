import ZFVP.ModelTheory.UsubaSuccessorRestorationModel
import ZFVP.ModelTheory.ForcingLSPreservation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace UsubaSuccessorModel
variable {P R one : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
  {H : Set V}
  (hH : IsExternalForcingGeneric
    (twoStepConditions P R (usubaSaturatedPosetName P R) ∅)
    (twoStepOrder P R (usubaSaturatedPosetName P R)
      (reverseInclusionOrderName P R (usubaSaturatedPosetName P R)) ∅) H)

local notation "A" => twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH
local notation "B" => twoStepSecondContext hR ht (usubaSaturated_iterand hR ht) hH
local notation "C" => twoStepTotalContext hR ht (usubaSaturated_iterand hR ht) hH
local notation "J" => twoStepIntermediateEmbedding hR ht (usubaSaturated_iterand hR ht) hH

theorem dependentChoiceAt_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (hAC : ¬InternalChoice (twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH).Model) :
    InternalDependentChoiceAt (J (woodinSeedCardinal : (A).Model)) := by
  have hLSfirst := (A).unbounded_ls_preserved hLS
  have hg := (B).restoration_dependentChoiceAt hLSfirst hAC (second_carrier hR ht hH)
    (second_order hR ht hH) (second_top hR ht hH)
  let e := twoStepQuotientEquiv hR ht (usubaSaturated_iterand hR ht) hH
  let j := ElementaryMap.ofMembershipIso e.symm (fun x y ↦ by
    have hh := twoStepQuotientEquiv_mem_iff hR ht (usubaSaturated_iterand hR ht) hH
      (e.symm x) (e.symm y)
    change e (e.symm x) ∈ e (e.symm y) ↔ e.symm x ∈ e.symm y at hh
    simpa only [Equiv.apply_symm_apply] using hh.symm)
  exact j.dependentChoiceAt hg

theorem enumeration_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (hAC : ¬InternalChoice (twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH).Model)
    {X : (A).Model} (hX : X ⊆ hierarchy (usubaLeastTarget woodinSeedCardinal)) :
    ∃ γ : (C).Model, IsOrdinal γ ∧ γ ⊆ J (woodinSeedCardinal : (A).Model) ∧
      InternalDependentChoiceAt γ ∧ ∃ f ∈ (J X) ^ γ, range f = J X := by
  classical
  by_cases he : X = ∅
  · subst X
    refine ⟨∅, inferInstance, empty_subset _, dependentChoiceAt_zero, ∅, ?_, ?_⟩ <;>
      simp [(J).map_empty]
  · exact ⟨J woodinSeedCardinal, ((J).ordinal_iff _).mpr inferInstance,
      subset_refl _, dependentChoiceAt_of_ls hR ht hH hLS hAC, surjection hR ht hH hAC hX
        (ne_empty_iff_isNonempty.mp he)⟩

theorem successor_step_dependentChoiceAt_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (k : V) [IsOrdinal k]
    (hbelow : ∀ β ∈ (A).check k, InternalDependentChoiceAt β) :
    InternalDependentChoiceAt ((C).check k) := by
  classical
  by_cases hAC : InternalChoice (A).Model
  · have hg := dependentChoiceAt_of_internalChoice ((B).internalChoice_of_ground hAC)
      ((B).check ((A).check k))
    let e := twoStepQuotientEquiv hR ht (usubaSaturated_iterand hR ht) hH
    let j := ElementaryMap.ofMembershipIso e.symm (fun x y ↦ by
      have hh := twoStepQuotientEquiv_mem_iff hR ht (usubaSaturated_iterand hR ht) hH
        (e.symm x) (e.symm y)
      change e (e.symm x) ∈ e (e.symm y) ↔ e.symm x ∈ e.symm y at hh
      simpa only [Equiv.apply_symm_apply] using hh.symm)
    have hh := j.dependentChoiceAt hg
    change InternalDependentChoiceAt (J ((A).check k)) at hh
    simpa only [twoStepIntermediateEmbedding_check] using hh
  · have hle : (A).check k ⊆ (woodinSeedCardinal : (A).Model) := by
      rcases IsOrdinal.mem_trichotomy ((A).check k) (woodinSeedCardinal : (A).Model) with h | he | h
      · exact IsOrdinal.toIsTransitive.transitive _ h
      · exact he ▸ subset_refl _
      · exact False.elim ((woodinSeedCardinal_spec hAC).2.1 (hbelow _ h))
    have hg := dependentChoiceAt_of_ls hR ht hH hLS hAC
    have := ((J).ordinal_iff (woodinSeedCardinal : (A).Model)).mpr inferInstance
    have := ((J).ordinal_iff ((A).check k)).mpr inferInstance
    have hh := hg.downward (((J).subset_iff _ _).mpr hle)
    simpa only [twoStepIntermediateEmbedding_check] using hh

end UsubaSuccessorModel
end ZFVP
