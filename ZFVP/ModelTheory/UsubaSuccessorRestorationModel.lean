import ZFVP.ModelTheory.UsubaRestorationDCGain
import ZFVP.ModelTheory.ForcingPreorderVopenkaLS
import ZFVP.ModelTheory.UsubaIterationStages
import ZFVP.ModelTheory.TwoStepIntermediate
import ZFVP.SetTheory.InjectionRetraction
import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.SetTheory.ElementaryDependentChoice
import ZFVP.ModelTheory.CriticalPointCardinal
import ZFVP.SetTheory.EndExtensionHierarchyAgreement
import ZFVP.ModelTheory.ForcingChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem restoration_surjection (A : ForcingContext V)
    (hAC : ¬InternalChoice V) (hP : (A).P = usubaRestorationPoset)
    (hR : (A).R = reverseInclusionOrder (A).P) (hone : (A).one = ∅)
    {X : V} (hX : X ⊆ hierarchy (usubaLeastTarget woodinSeedCardinal))
    (hne : IsNonempty X) :
    ∃ e ∈ ((A).check X) ^ ((A).check woodinSeedCardinal), range e = (A).check X := by
  have hPc := hP.trans (usubaRestorationPoset_of_not_choice hAC)
  rcases A with ⟨P, R, one, G, order, top, generic⟩
  dsimp only at hPc hR hone ⊢
  subst P R one
  let A := usubaCollapseContext woodinSeedCardinal_regular
    (hierarchy (usubaLeastTarget woodinSeedCardinal)) G generic
  have hS : IsNonempty (hierarchy (usubaLeastTarget (woodinSeedCardinal : V))) := by
    obtain ⟨x, hx⟩ := hne.nonempty
    exact ⟨x, hX x hx⟩
  have hf := UsubaCollapseModel.genericFunction_mem_function woodinSeedCardinal_regular generic hS
  have hr := UsubaCollapseModel.genericFunction_range woodinSeedCardinal_regular generic hS
  apply surjection_of_injection
    ((cardLE_of_subset (((A).checkEmbedding.subset_iff _ _).mpr hX)).trans
      (cardLE_of_surjective_function (ordinal_wellOrderable _) hf hr))
  obtain ⟨x, hx⟩ := hne.nonempty
  exact ⟨(A).check x, ((A).check_mem_iff _ _).mpr hx⟩

end ForcingContext

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

theorem second_carrier : (B).P = usubaRestorationPoset := (A).usubaSaturatedName_value

theorem second_order : (B).R = reverseInclusionOrder (B).P := by
  obtain ⟨p, hp⟩ := (A).generic.1.2.1
  exact (Defined.eval_iff _).mp (((A).formula_truth piOneReverseInclusionOrderFormula
    ![⟨reverseInclusionOrderName P R (usubaSaturatedPosetName P R),
      reverseInclusionOrderName_isName _ _ _⟩, (A).usubaSaturatedName]).mpr
    ⟨p, hp, reverseInclusionOrderName_forces (A).order (A).top ((A).generic.1.1 p hp)
      (A).usubaSaturatedName⟩)

theorem second_top : (B).one = ∅ := by
  change (A).ofName ⟨∅, empty_forcingName P⟩ = ∅
  obtain ⟨p, hp⟩ := (A).generic.1.2.1
  apply isEmpty_iff_eq_empty.mp
  exact (Defined.eval_iff _).mp (((A).formula_truth isEmpty ![⟨∅, empty_forcingName P⟩]).mpr
    ⟨p, hp, emptyName_forces (A).order (A).top ((A).generic.1.1 p hp)⟩)

theorem dependentChoiceAt [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (hAC : ¬InternalChoice (twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH).Model) :
    InternalDependentChoiceAt (J (woodinSeedCardinal : (A).Model)) := by
  have hLS : ∀ β : (A).Model, IsOrdinal β → ∃ lam : (A).Model, β ∈ lam ∧ IsLSCardinal lam := by
    intro β hβ
    let := hβ
    exact (A).lsCardinals_unbounded hVP β
  have hg := (B).restoration_dependentChoiceAt hLS hAC (second_carrier hR ht hH)
    (second_order hR ht hH) (second_top hR ht hH)
  let e := twoStepQuotientEquiv hR ht (usubaSaturated_iterand hR ht) hH
  let j := ElementaryMap.ofMembershipIso e.symm (fun x y ↦ by
    have hh := twoStepQuotientEquiv_mem_iff hR ht (usubaSaturated_iterand hR ht) hH
      (e.symm x) (e.symm y)
    change e (e.symm x) ∈ e (e.symm y) ↔ e.symm x ∈ e.symm y at hh
    simpa only [Equiv.apply_symm_apply] using hh.symm)
  exact j.dependentChoiceAt hg

theorem surjection
    (hAC : ¬InternalChoice (twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH).Model)
    {X : (A).Model} (hX : X ⊆ hierarchy (usubaLeastTarget woodinSeedCardinal))
    (hne : IsNonempty X) :
    ∃ f ∈ (J X) ^ (J (woodinSeedCardinal : (A).Model)), range f = J X := by
  obtain ⟨f, hf, hr⟩ := (B).restoration_surjection hAC (second_carrier hR ht hH)
    (second_order hR ht hH) (second_top hR ht hH) hX hne
  let e := twoStepQuotientEquiv hR ht (usubaSaturated_iterand hR ht) hH
  let j := ElementaryMap.ofMembershipIso e.symm (fun x y ↦ by
    have hh := twoStepQuotientEquiv_mem_iff hR ht (usubaSaturated_iterand hR ht) hH
      (e.symm x) (e.symm y)
    change e (e.symm x) ∈ e (e.symm y) ↔ e.symm x ∈ e.symm y at hh
    simpa only [Equiv.apply_symm_apply] using hh.symm)
  exact ⟨j f, (j.map_defined boundedSurjectionFormula
    (fun v ↦ v 0 ∈ v 2 ^ v 1 ∧ range (v 0) = v 2)
    (fun v ↦ v 0 ∈ v 2 ^ v 1 ∧ range (v 0) = v 2)
    ![f, (B).check woodinSeedCardinal, (B).check X]).mp ⟨hf, hr⟩⟩

theorem enumeration [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
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
      subset_refl _, dependentChoiceAt hR ht hH hVP hAC, surjection hR ht hH hAC hX
        (ne_empty_iff_isNonempty.mp he)⟩

theorem successor_step_dependentChoiceAt [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
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
    have hg := dependentChoiceAt hR ht hH hVP hAC
    have := ((J).ordinal_iff (woodinSeedCardinal : (A).Model)).mpr inferInstance
    have := ((J).ordinal_iff ((A).check k)).mpr inferInstance
    have hh := hg.downward (((J).subset_iff _ _).mpr hle)
    simpa only [twoStepIntermediateEmbedding_check] using hh

end UsubaSuccessorModel
end ZFVP
