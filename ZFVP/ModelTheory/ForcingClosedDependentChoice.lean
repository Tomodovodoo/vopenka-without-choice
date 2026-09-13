import ZFVP.ModelTheory.ForcingDependentChoiceSeriality
import ZFVP.ModelTheory.ForcingSemanticConsequence

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem dependentChoiceForcing_branch_dense [Countable V] {P R one p γ : V} [IsOrdinal γ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (τA τB : ForcingName P) (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt P R α)
    (hf : p ∈ forcingFormula P R dependentChoiceSerialFormula
      (standardTuple ![checkName one γ, τA.val, τB.val])) :
    ForcingDenseBelow P R (forcingFormula P R dependentChoiceBranchFormula
      (standardTuple ![checkName one γ, τA.val, τB.val])) p := by
  refine ⟨(forcingFormula_regular hR dependentChoiceBranchFormula _).1, fun q hq hqp ↦ ?_⟩
  have hqf := (forcingFormula_regular hR dependentChoiceSerialFormula _).2.1 p hf q hq hqp
  have hK := dependentChoiceForcing_candidates_nonempty hR htop hq τA τB hqf
  obtain ⟨s, hs⟩ := dependentChoicePath_of_serial_paths hDC hK
    (fun s hshort hpath ↦ dependentChoiceForcingRelation_serial hR htop hq τA τB hqf hclosed hshort hpath)
  let := IsFunction.of_mem hs.1
  have hb := dependentChoiceForcingPath_bounds hs
  obtain ⟨r, hr, hrq, hbound⟩ := forcingClosedAt_lowerBound_below hR
    (hclosed γ inferInstance (subset_refl _)) hb.1 hq hb.2
  refine ⟨r, ?_, hrq⟩
  let c : ForcingName P := ⟨checkName one γ, checkName_isName htop.1 γ⟩
  apply forcingFormula_of_all_generics hR htop hr dependentChoiceBranchFormula ![c, τA, τB]
  intro G hG hrG
  let S : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hconds (i : V) (hi : i ∈ γ) : kpair.π₁ (s ‘ i) ∈ G := by
    have hci := function_value_mem hb.1.1 hi
    have hh := hbound i hi
    have hiD : i ∈ domain s := (domain_eq_of_mem_function hs.1).symm ▸ hi
    rw [conditionSequence_value hiD] at hci hh
    exact hG.1.2.2.1 r hrG _ hci hh
  exact (eval_dependentChoiceBranchFormula _).mpr
    ⟨_, S.dependentChoiceForcingPath_value τA τB hs hconds⟩

theorem dependentChoiceForcing_serial_forces_branch [Countable V] {P R one p γ : V} [IsOrdinal γ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (τA τB : ForcingName P) (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt P R α)
    (hf : p ∈ forcingFormula P R dependentChoiceSerialFormula
      (standardTuple ![checkName one γ, τA.val, τB.val])) :
    p ∈ forcingFormula P R dependentChoiceBranchFormula
      (standardTuple ![checkName one γ, τA.val, τB.val]) :=
  (forcingFormula_regular hR dependentChoiceBranchFormula _).2.2 p
    ((forcingFormula_regular hR dependentChoiceSerialFormula _).1 p hf)
    (dependentChoiceForcing_branch_dense hR htop τA τB hDC hclosed hf).2

namespace ForcingContext

set_option maxHeartbeats 800000 in
theorem dependentChoiceAt_of_closed_countable [Countable V] (S : ForcingContext V) {γ : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt S.P S.R α) :
    InternalDependentChoiceAt (S.check γ) := by
  intro A B hA hB
  obtain ⟨τA, rfl⟩ := S.ofName_surjective A
  obtain ⟨τB, rfl⟩ := S.ofName_surjective B
  let c : ForcingName S.P := ⟨checkName S.one γ, checkName_isName S.top.1 γ⟩
  have hs := (eval_dependentChoiceSerialFormula
    (fun i ↦ S.ofName (![c, τA, τB] i))).mpr ⟨hA, hB⟩
  obtain ⟨p, hpG, hp⟩ := (S.formula_truth dependentChoiceSerialFormula ![c, τA, τB]).mp hs
  have hb := dependentChoiceForcing_serial_forces_branch S.order S.top τA τB hDC hclosed hp
  have he := (S.formula_truth dependentChoiceBranchFormula ![c, τA, τB]).mpr ⟨p, hpG, hb⟩
  have hout := (eval_dependentChoiceBranchFormula
    (fun i : Fin 3 ↦ S.ofName (![c, τA, τB] i))).mp he
  change ∃ f, IsDependentChoicePath (S.ofName τA) (S.ofName τB) (S.ofName c) f at hout
  rw [show S.ofName c = S.check γ from rfl] at hout
  exact hout

end ForcingContext
end ZFVP
