import ZFVP.ModelTheory.ForcingCheckedTruth
import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.SetTheory.FiniteCofinality
import ZFVP.ModelTheory.WoodinCollapseForcesRestoration
import ZFVP.SetTheory.LeastDependentChoiceFailure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def omegaForcingFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 4 :=
  f“P R o p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧ p ∈ P →
    !(checkedUnaryForcingFormula φ) P R o p (!isω)”

universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

theorem eval_omegaForcingFormula (φ : SetTheorySemisentence 1) (v : Fin 4 → V) :
    (omegaForcingFormula φ).Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) → v 3 ∈ v 0 →
        v 3 ∈ forcingFormula (v 0) (v 1) φ (standardTuple ![checkName (v 2) ω])) := by
  simp [omegaForcingFormula, Semiformula.eval_nestFormulae, Semiformula.eval_nestFormulaeFunc,
    Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ, forall_three_eq, forall_five_eq]

theorem forces_checked_omega (φ : SetTheorySemisentence 1)
    (hφ : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      φ.Evalb (fun _ ↦ (ω : W)))
    {P R one p : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P) :
    p ∈ forcingFormula P R φ (standardTuple ![checkName one ω]) := by
  have hh := eval_of_countable_zf (omegaForcingFormula φ) (by
    intro W _ _ _ _ v
    apply (eval_omegaForcingFormula φ v).mpr
    intro hR ht hp
    apply forces_checkedUnary_of_all_generics hR ht hp φ
    intro G hG _
    let A : ForcingContext W := ⟨v 0, v 1, v 2, G, hR, ht, hG⟩
    change φ.Evalb (fun _ ↦ A.check ω)
    rw [show A.check ω = (ω : A.Model) from A.checkEmbedding.map_omega]
    exact hφ A.Model) ![P, R, one, p]
  exact (eval_omegaForcingFormula φ ![P, R, one, p]).mp hh hR htop hp

theorem forces_omega_regular {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P) :
    p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one ω]) :=
  forces_checked_omega regularCardinalFormula (fun _ _ _ _ ↦ (Defined.eval_iff _).mpr omega_regular)
    hR htop hp

theorem forces_dependentChoiceBelow_omega {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P) :
    p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one ω]) :=
  forces_checked_omega dependentChoiceBelowFormula
    (fun _ _ _ _ ↦ (Defined.eval_iff _).mpr dependentChoiceAt_finite) hR htop hp

end ZFVP
