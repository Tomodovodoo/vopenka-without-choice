import ZFVP.ModelTheory.SaturatedHartogsSuccessor
import ZFVP.ModelTheory.ForcingHartogsUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def saturatedHartogsPosetNameFormula : SetTheorySemisentence 6 :=
  f“Q P R o γ δ. ∀ U W, !(parameterRecursionFormula forcingNameHierarchyStepFormula) U P δ →
    !(formulaUniqueNameFormula totalWoodinCollapseFormula) W P R
      (!assignmentPrependFormula (!(numeralFormula 1))
        (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o δ))
        (!hartogsNumberNameFormula P R (!checkNameFormula o γ))) →
    !forcingSaturatedNameFormula Q P R U W”

def saturatedHartogsOrderNameFormula : SetTheorySemisentence 6 :=
  f“S P R o γ δ. ∀ Q, !saturatedHartogsPosetNameFormula Q P R o γ δ → !reverseInclusionOrderNameFormula S P R Q”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def saturatedHartogsPosetName (P R one γ δ : V) : V :=
  saturatedWoodinCollapseName P R δ (hartogsNumberName P R (checkName one γ)) (checkName one δ)

noncomputable def saturatedHartogsOrderName (P R one γ δ : V) : V :=
  reverseInclusionOrderName P R (saturatedHartogsPosetName P R one γ δ)

instance saturatedHartogsPosetNameFormula_defined :
    ℒₛₑₜ-function₅[V] saturatedHartogsPosetName via saturatedHartogsPosetNameFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [saturatedHartogsPosetNameFormula, saturatedHartogsPosetName, saturatedWoodinCollapseName,
    woodinCollapseName, standardTuple]

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩
instance saturatedHartogsOrderNameFormula_defined :
    ℒₛₑₜ-function₅[V] saturatedHartogsOrderName via saturatedHartogsOrderNameFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [saturatedHartogsOrderNameFormula, saturatedHartogsOrderName, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]
  constructor
  · intro h
    exact h _ _ _ _ rfl rfl rfl rfl
  · rintro h a b c d rfl rfl rfl rfl
    exact h

end ZFVP


