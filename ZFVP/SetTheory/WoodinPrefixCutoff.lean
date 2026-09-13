import ZFVP.ModelTheory.WoodinRestorationCutoffName
import ZFVP.SetTheory.TwoStepForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def checkedBinaryForcingFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 6 :=
  f“P R o p a b. !(forcingTruthFormula φ) p P R
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o b))
      (!checkNameFormula o a))”

/-- The restoration assertion inside a prefix extension, without imposing
inaccessibility there. The source selects inaccessible cutoffs in the ground. -/
def woodinLocalRestorationFormula : SetTheorySemisentence 2 :=
  f“κ δ. ∃ Q S, !woodinCollapseSetFormula Q κ δ ∧ !piOneReverseInclusionOrderFormula S Q ∧
    ∀ p ∈ Q, !(checkedUnaryForcingFormula dependentChoiceBelowFormula) Q S (!isEmpty) p δ”

def woodinPrefixCutoffFormula : SetTheorySemisentence 5 :=
  f“P R o κ δ. κ ∈ δ ∧ !choicelessInaccessibleFormula δ ∧
    ∀ p ∈ P, !(checkedBinaryForcingFormula woodinLocalRestorationFormula) P R o p κ δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance checkedBinaryForcingFormula_defined (φ : SetTheorySemisentence 2) :
    Defined (fun v : Fin 6 → V ↦ v 3 ∈ forcingFormula (v 0) (v 1) φ
      (standardTuple ![checkName (v 2) (v 4), checkName (v 2) (v 5)])) (checkedBinaryForcingFormula φ) :=
  ⟨fun v ↦ by simp [checkedBinaryForcingFormula, standardTuple]⟩

def IsWoodinLocalRestoration (κ δ : V) : Prop :=
  IsOrdinal δ ∧ ∀ p ∈ woodinCollapse κ δ,
    p ∈ forcingFormula (woodinCollapse κ δ) (woodinCollapseOrder κ δ) dependentChoiceBelowFormula
      (standardTuple ![checkName ∅ δ])

instance woodinLocalRestorationFormula_defined :
    ℒₛₑₜ-relation[V] IsWoodinLocalRestoration via woodinLocalRestorationFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [woodinLocalRestorationFormula, IsWoodinLocalRestoration, woodinCollapseOrder]

instance woodinLocalRestoration_definable : ℒₛₑₜ-relation[V] IsWoodinLocalRestoration :=
  woodinLocalRestorationFormula_defined.to_definable

def IsWoodinPrefixCutoff (P R one κ δ : V) : Prop :=
  κ ∈ δ ∧ IsChoicelessInaccessible δ ∧ ∀ p ∈ P,
    p ∈ forcingFormula P R woodinLocalRestorationFormula
      (standardTuple ![checkName one κ, checkName one δ])

instance woodinPrefixCutoffFormula_defined :
    Defined (fun v : Fin 5 → V ↦ IsWoodinPrefixCutoff (v 0) (v 1) (v 2) (v 3) (v 4))
      woodinPrefixCutoffFormula :=
  ⟨fun v ↦ by
    simp [woodinPrefixCutoffFormula, IsWoodinPrefixCutoff, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Fin.forall_fin_succ]
    intro _ _
    constructor
    · intro h p hp
      exact h p hp _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · intro h p hp a b c d e f ha hb hc hd he hf
      subst a b c d e f
      exact h p hp⟩

instance woodinPrefixCutoff_definable : ℒₛₑₜ-relation₅[V] IsWoodinPrefixCutoff :=
  woodinPrefixCutoffFormula_defined.to_definable

noncomputable def woodinPrefixCutoff (P R one κ : V) : V :=
  leastOrdinalOrZero (IsWoodinPrefixCutoff P R one) (by definability) κ

instance woodinPrefixCutoff_function_definable (P R one : V) :
    ℒₛₑₜ-function₁[V] (woodinPrefixCutoff P R one) := by
  unfold woodinPrefixCutoff
  exact leastOrdinalOrZero_definable (IsWoodinPrefixCutoff P R one) (by definability)

theorem woodinPrefixCutoff_spec {P R one κ δ : V} (hδ : IsWoodinPrefixCutoff P R one κ δ) :
    IsLeastOrdinal (IsWoodinPrefixCutoff P R one κ) (woodinPrefixCutoff P R one κ) :=
  leastOrdinalOrZero_spec _ _ κ ⟨δ, hδ.2.1.1, hδ⟩

theorem woodinPrefixCutoff_le {P R one κ δ : V} (hδ : IsWoodinPrefixCutoff P R one κ δ) :
    woodinPrefixCutoff P R one κ ⊆ δ := (woodinPrefixCutoff_spec hδ).2.2 δ hδ.2.1.1 hδ

theorem IsWoodinRestorationCutoff.localRestoration {κ δ : V} (hδ : IsWoodinRestorationCutoff κ δ) :
    IsWoodinLocalRestoration κ δ := ⟨hδ.2.1.1, hδ.2.2⟩

theorem IsWoodinPrefixCutoff.localRestoration (A : ForcingContext V) {κ δ : V}
    (hδ : IsWoodinPrefixCutoff A.P A.R A.one κ δ) :
    IsWoodinLocalRestoration (A.check κ) (A.check δ) := by
  let cκ : ForcingName A.P := ⟨checkName A.one κ, checkName_isName A.top.1 κ⟩
  let cδ : ForcingName A.P := ⟨checkName A.one δ, checkName_isName A.top.1 δ⟩
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have ht := (A.formula_truth woodinLocalRestorationFormula ![cκ, cδ]).mpr
    ⟨p, hp, hδ.2.2 p (A.generic.1.1 p hp)⟩
  exact (Defined.eval_iff _).mp ht

end ZFVP
