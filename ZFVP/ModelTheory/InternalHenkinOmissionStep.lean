import ZFVP.ModelTheory.InternalHenkinOmissionDensity

/-! A choice graph on actual sets of unary codes supplies a uniform definable
omission step. The step leaves the name context unchanged and skips a request
whose name has not yet entered the current context. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

noncomputable def nonemptyUnaryCodeSets : V :=
  {A ∈ power (formulaSet (membershipLanguageCode : V) ∅ 1) ; IsNonempty A}

def IsHenkinOmissionSelector (s : V) : Prop :=
  IsFunction s ∧ domain s = nonemptyUnaryCodeSets ∧
    ∀ A : V, A ⊆ formulaSet (membershipLanguageCode : V) ∅ 1 → IsNonempty A → s ‘ A ∈ A

theorem exists_henkinOmissionSelector (hAC : InternalChoice V) :
    ∃ s : V, IsHenkinOmissionSelector s := by
  obtain ⟨s, hs, hchoose⟩ := hAC nonemptyUnaryCodeSets (fun A hA ↦ (mem_sep_iff.mp hA).2)
  refine ⟨s, IsFunction.of_mem hs, domain_eq_of_mem_function hs, ?_⟩
  intro A hA hne
  exact hchoose A (mem_sep_iff.mpr ⟨mem_power_iff.mpr hA, hne⟩)

instance henkinOmissionChoices_definable : Language.DefinableFunction₅ ℒₛₑₜ (henkinOmissionChoices (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun A T P n i χ : V ↦ ∀ ψ, ψ ∈ A ↔ ψ ∈ P ∧
      IsConsistentCodedFormula T n (andCode χ
        (negateFormula membershipLanguageCode ∅ n (unaryCodedInstance n i ψ)))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = henkinOmissionChoices (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [henkinOmissionChoices, mem_sep_iff]

noncomputable def henkinOmissionStep (s T P i p : V) : V := by
  classical
  let n := kpair.π₁ p
  let χ := kpair.π₂ p
  let ψ := s ‘ (henkinOmissionChoices T P n i χ)
  exact if IsNonprincipalCodedType T P ∧ p ∈ henkinConditions T ∧ i ∈ n then
    ⟨n, andCode χ (negateFormula membershipLanguageCode ∅ n (unaryCodedInstance n i ψ))⟩ₖ else p

instance henkinOmissionStep_definable : Language.DefinableFunction₅ ℒₛₑₜ (henkinOmissionStep (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun y s T P i p : V ↦
      ((IsNonprincipalCodedType T P ∧ p ∈ henkinConditions T ∧ i ∈ kpair.π₁ p) ∧
        y = ⟨kpair.π₁ p, andCode (kpair.π₂ p) (negateFormula membershipLanguageCode ∅ (kpair.π₁ p)
          (unaryCodedInstance (kpair.π₁ p) i (s ‘ (henkinOmissionChoices T P (kpair.π₁ p) i (kpair.π₂ p)))))⟩ₖ) ∨
      (¬(IsNonprincipalCodedType T P ∧ p ∈ henkinConditions T ∧ i ∈ kpair.π₁ p) ∧ y = p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = henkinOmissionStep (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  unfold henkinOmissionStep
  dsimp only
  split <;> simp_all

theorem henkinOmissionStep_skip {s T P i p : V} (hi : i ∉ kpair.π₁ p) :
    henkinOmissionStep s T P i p = p := by simp [henkinOmissionStep, hi]

theorem henkinOmissionStep_context (s T P i p : V) :
    kpair.π₁ (henkinOmissionStep s T P i p) = kpair.π₁ p := by
  unfold henkinOmissionStep
  dsimp only
  split <;> simp

theorem henkinOmissionStep_spec (hω : Schmerl.HasStandardOmega V) {s T P n i χ : V}
    (hs : IsHenkinOmissionSelector s) (hP : IsNonprincipalCodedType T P)
    (hp : ⟨n, χ⟩ₖ ∈ henkinConditions T) (hi : i ∈ n) :
    ∃ ψ ∈ P, ∃ χ' : V,
      χ' = andCode χ (negateFormula membershipLanguageCode ∅ n (unaryCodedInstance n i ψ)) ∧
      henkinOmissionStep s T P i ⟨n, χ⟩ₖ = ⟨n, χ'⟩ₖ ∧
      ⟨n, χ'⟩ₖ ∈ henkinConditions T ∧ CodedFormulaImplies T n χ' χ ∧
      CodedFormulaImplies T n χ' (negateFormula membershipLanguageCode ∅ n (unaryCodedInstance n i ψ)) := by
  obtain ⟨hzero, hc⟩ := (pair_mem_henkinConditions_iff _ _ _).mp hp
  have hne := hP.omissionChoices_nonempty hω hc hi
  have hsub : henkinOmissionChoices T P n i χ ⊆ formulaSet (membershipLanguageCode : V) ∅ 1 :=
    fun ψ hψ ↦ hP.1 ψ (mem_sep_iff.mp hψ).1
  have hsel := hs.2.2 (henkinOmissionChoices T P n i χ) hsub hne
  obtain ⟨hψ, hcon⟩ := mem_sep_iff.mp hsel
  have hneg := negateFormula_mem membershipLanguageCode_valid (unaryCodedInstance_valid hc.context hi (hP.1 _ hψ))
  refine ⟨s ‘ (henkinOmissionChoices T P n i χ), hψ, _, rfl, ?_,
    (pair_mem_henkinConditions_iff _ _ _).mpr ⟨hzero, hcon⟩,
    CodedFormulaImplies.conj_left T hc.1 hneg, CodedFormulaImplies.conj_right T hc.1 hneg⟩
  simp only [henkinOmissionStep, kpair.π₁_kpair, kpair.π₂_kpair, hP, hp, hi, and_self, ite_true]

theorem henkinOmissionStep_consistent (hω : Schmerl.HasStandardOmega V) {s T P i p : V}
    (hs : IsHenkinOmissionSelector s) (hp : p ∈ henkinConditions T) :
    henkinOmissionStep s T P i p ∈ henkinConditions T := by
  classical
  obtain ⟨n, χ, rfl, _, _⟩ := henkinConditions_cases hp
  by_cases hg : IsNonprincipalCodedType T P ∧ i ∈ n
  · obtain ⟨ψ, _, χ', _, he, hnext, _⟩ := henkinOmissionStep_spec hω hs hg.1 hp hg.2
    rw [he]
    exact hnext
  · simp only [henkinOmissionStep, kpair.π₁_kpair, kpair.π₂_kpair, hp, true_and, hg, ite_false]

theorem henkinOmissionStep_implies (hω : Schmerl.HasStandardOmega V) {s T P i p : V}
    (hs : IsHenkinOmissionSelector s) (hp : p ∈ henkinConditions T) :
    CodedFormulaImplies T (kpair.π₁ p) (kpair.π₂ (henkinOmissionStep s T P i p)) (kpair.π₂ p) := by
  classical
  obtain ⟨n, χ, rfl, _, hc⟩ := henkinConditions_cases hp
  by_cases hg : IsNonprincipalCodedType T P ∧ i ∈ n
  · obtain ⟨ψ, _, χ', _, he, _, hback, _⟩ := henkinOmissionStep_spec hω hs hg.1 hp hg.2
    simpa only [he, kpair.π₁_kpair, kpair.π₂_kpair] using hback
  · simpa only [henkinOmissionStep, kpair.π₁_kpair, kpair.π₂_kpair, hp, true_and, hg, ite_false]
      using CodedFormulaImplies.refl T hc.1

end ZFVP
