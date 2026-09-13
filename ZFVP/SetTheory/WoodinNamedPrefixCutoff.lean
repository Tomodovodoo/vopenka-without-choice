import ZFVP.SetTheory.WoodinPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- One named argument and one checked argument in the prefix forcing relation. -/
def namedCheckedBinaryForcingFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 6 :=
  f“P R o p τ b. !(forcingTruthFormula φ) p P R
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o b)) τ)”

def woodinNamedPrefixCutoffFormula : SetTheorySemisentence 6 :=
  f“P R o γ τ δ. γ ∈ δ ∧ !choicelessInaccessibleFormula δ ∧
    ∀ p ∈ P, !(namedCheckedBinaryForcingFormula woodinLocalRestorationFormula) P R o p τ δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance namedCheckedBinaryForcingFormula_defined (φ : SetTheorySemisentence 2) :
    Defined (fun v : Fin 6 → V ↦ v 3 ∈ forcingFormula (v 0) (v 1) φ
      (standardTuple ![v 4, checkName (v 2) (v 5)])) (namedCheckedBinaryForcingFormula φ) :=
  ⟨fun v ↦ by simp [namedCheckedBinaryForcingFormula, standardTuple]⟩

/-- The cutoff is selected in the ground model; only the collapse parameter is a name. -/
def IsWoodinNamedPrefixCutoff (P R one γ τ δ : V) : Prop :=
  γ ∈ δ ∧ IsChoicelessInaccessible δ ∧ ∀ p ∈ P,
    p ∈ forcingFormula P R woodinLocalRestorationFormula
      (standardTuple ![τ, checkName one δ])

instance woodinNamedPrefixCutoffFormula_defined :
    Defined (fun v : Fin 6 → V ↦ IsWoodinNamedPrefixCutoff (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
      woodinNamedPrefixCutoffFormula :=
  ⟨fun v ↦ by
    simp [woodinNamedPrefixCutoffFormula, IsWoodinNamedPrefixCutoff, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Fin.forall_fin_succ]
    intro _ _
    constructor
    · intro h p hp
      exact h p hp _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · intro h p hp a b c d e f ha hb hc hd he hf
      subst a b c d e f
      exact h p hp⟩

instance woodinNamedPrefixCutoff_definable : Language.DefinableRel₆ ℒₛₑₜ
    (IsWoodinNamedPrefixCutoff (V := V)) := woodinNamedPrefixCutoffFormula_defined.to_definable

noncomputable def woodinNamedPrefixCutoff (P R one γ τ : V) : V :=
  leastOrdinalOrZero (fun γ δ ↦ IsWoodinNamedPrefixCutoff P R one γ τ δ) (by definability) γ

instance woodinNamedPrefixCutoff_ordinal (P R one γ τ : V) :
    IsOrdinal (woodinNamedPrefixCutoff P R one γ τ) := by
  unfold woodinNamedPrefixCutoff
  exact leastOrdinalOrZero_ordinal _ _ _

theorem woodinNamedPrefixCutoff_spec {P R one γ τ δ : V}
    (hδ : IsWoodinNamedPrefixCutoff P R one γ τ δ) :
    IsLeastOrdinal (IsWoodinNamedPrefixCutoff P R one γ τ) (woodinNamedPrefixCutoff P R one γ τ) :=
  leastOrdinalOrZero_spec _ _ γ ⟨δ, hδ.2.1.1, hδ⟩

theorem woodinNamedPrefixCutoff_le {P R one γ τ δ : V}
    (hδ : IsWoodinNamedPrefixCutoff P R one γ τ δ) :
    woodinNamedPrefixCutoff P R one γ τ ⊆ δ :=
  (woodinNamedPrefixCutoff_spec hδ).2.2 δ hδ.2.1.1 hδ

theorem IsWoodinNamedPrefixCutoff.localRestoration (A : ForcingContext V) {γ δ : V}
    (τ : ForcingName A.P) (hδ : IsWoodinNamedPrefixCutoff A.P A.R A.one γ τ.val δ) :
    IsWoodinLocalRestoration (A.ofName τ) (A.check δ) := by
  let cδ : ForcingName A.P := ⟨checkName A.one δ, checkName_isName A.top.1 δ⟩
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have ht := (A.formula_truth woodinLocalRestorationFormula ![τ, cδ]).mpr
    ⟨p, hp, hδ.2.2 p (A.generic.1.1 p hp)⟩
  exact (Defined.eval_iff _).mp ht

end ZFVP
