import ZFVP.ModelTheory.ForcingClosedDependentChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingClosedThroughFormula : SetTheorySemisentence 3 :=
  f“P R γ. ∀ α, !IsOrdinal.dfn α → α ⊆ γ →
    ∀ s, (s ∈ !function.dfn P α ∧ ∀ i ∈ α, ∀ j ∈ i,
      !kpair.dfn (!value.dfn s i) (!value.dfn s j) ∈ R) →
      ∃ p ∈ P, ∀ i ∈ α, !kpair.dfn p (!value.dfn s i) ∈ R”

def checkedUnaryForcingFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 5 :=
  f“P R o p a. !(ordinaryForcingTranslation φ) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o a))”

def closedForcingDependentChoiceFormula : SetTheorySemisentence 5 :=
  f“P R o γ p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !IsOrdinal.dfn γ ∧ !dependentChoiceAtFormula γ ∧ !forcingClosedThroughFormula P R γ ∧ p ∈ P →
      !(checkedUnaryForcingFormula dependentChoiceAtFormula) P R o p γ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingClosedThrough (P R γ : V) : Prop :=
  ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt P R α

instance forcingClosedThroughFormula_defined :
    ℒₛₑₜ-relation₃[V] IsForcingClosedThrough via forcingClosedThroughFormula :=
  ⟨fun v ↦ by simp [forcingClosedThroughFormula, IsForcingClosedThrough,
    IsForcingClosedAt, IsForcingDescending]⟩

instance isForcingClosedThrough_definable : ℒₛₑₜ-relation₃[V] IsForcingClosedThrough :=
  forcingClosedThroughFormula_defined.to_definable

instance checkedUnaryForcingFormula_defined (φ : SetTheorySemisentence 1) :
    Defined (fun v : Fin 5 → V ↦ v 3 ∈ forcingFormula (v 0) (v 1) φ
      (standardTuple ![checkName (v 2) (v 4)])) (checkedUnaryForcingFormula φ) :=
  ⟨fun v ↦ by
    simp [checkedUnaryForcingFormula, standardTuple,
      Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
    constructor
    · intro h
      exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
      exact h⟩

theorem eval_closedForcingDependentChoiceFormula (v : Fin 5 → V) :
    closedForcingDependentChoiceFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsOrdinal (v 3) → InternalDependentChoiceAt (v 3) →
      IsForcingClosedThrough (v 0) (v 1) (v 3) → v 4 ∈ v 0 →
      v 4 ∈ forcingFormula (v 0) (v 1) dependentChoiceAtFormula
        (standardTuple ![checkName (v 2) (v 3)])) := by
  simp [closedForcingDependentChoiceFormula]

set_option maxHeartbeats 800000 in
theorem closedForcing_forces_dependentChoice_countable [Countable V] {P R one γ p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hγ : IsOrdinal γ)
    (hDC : InternalDependentChoiceAt γ) (hclosed : IsForcingClosedThrough P R γ) (hp : p ∈ P) :
    p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName one γ]) := by
  let := hγ
  let c : ForcingName P := ⟨checkName one γ, checkName_isName htop.1 γ⟩
  apply forcingFormula_of_all_generics hR htop hp dependentChoiceAtFormula ![c]
  intro G hG _
  let S : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  exact (Defined.eval_iff _).mpr (S.dependentChoiceAt_of_closed_countable hDC hclosed)

set_option maxHeartbeats 800000 in
theorem closedForcing_forces_dependentChoice {P R one γ p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hγ : IsOrdinal γ)
    (hDC : InternalDependentChoiceAt γ) (hclosed : IsForcingClosedThrough P R γ) (hp : p ∈ P) :
    p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName one γ]) := by
  have hh := eval_of_countable_zf closedForcingDependentChoiceFormula (by
    intro W _ _ _ _ v
    exact (eval_closedForcingDependentChoiceFormula v).mpr
      (fun hR htop hγ hDC hclosed hp ↦
        closedForcing_forces_dependentChoice_countable hR htop hγ hDC hclosed hp)) ![P, R, one, γ, p]
  exact (eval_closedForcingDependentChoiceFormula _).mp hh hR htop hγ hDC hclosed hp

namespace ForcingContext

set_option maxHeartbeats 800000 in
theorem dependentChoiceAt_of_closed (S : ForcingContext V) {γ : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ) (hclosed : IsForcingClosedThrough S.P S.R γ) :
    InternalDependentChoiceAt (S.check γ) := by
  let c : ForcingName S.P := ⟨checkName S.one γ, checkName_isName S.top.1 γ⟩
  have hf := closedForcing_forces_dependentChoice S.order S.top (inferInstance : IsOrdinal γ) hDC hclosed S.top.1
  have he := (S.formula_truth dependentChoiceAtFormula ![c]).mpr
    ⟨S.one, externalForcingFilter_top S.generic.1 S.top, hf⟩
  exact (Defined.eval_iff _).mp he

end ForcingContext
end ZFVP
