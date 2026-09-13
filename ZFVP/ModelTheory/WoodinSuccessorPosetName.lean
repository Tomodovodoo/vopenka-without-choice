import ZFVP.ModelTheory.WoodinRestorationCutoffName
import ZFVP.ModelTheory.ForcingFormulaNameSpecification

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def woodinSuccessorPosetFormula : SetTheorySemisentence 2 :=
  f“Q κ. ∃ δ, !woodinRestorationCutoffValueFormula δ κ ∧ !woodinCollapseSetFormula Q κ δ”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinSuccessorPosetFormula_defined :
    ℒₛₑₜ-function₁[V] (fun κ ↦ woodinCollapse κ (woodinRestorationCutoff κ)) via woodinSuccessorPosetFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [woodinSuccessorPosetFormula]
  intro _
  infer_instance

noncomputable def woodinSuccessorPosetName (P R κ : V) : V :=
  formulaUniqueName P R woodinSuccessorPosetFormula (assignmentPrepend (0 : V) ∅ κ)

instance woodinSuccessorPosetName_definable (P R : V) :
    ℒₛₑₜ-function₁[V] (woodinSuccessorPosetName P R) := by
  unfold woodinSuccessorPosetName
  definability

theorem woodinSuccessorPosetName_isName (P R κ : V) :
    IsForcingName P (woodinSuccessorPosetName P R κ) := formulaUniqueName_isName _ _ _ _

/-- This formula is total even at the zero cutoff, so no existence of a
restoration stage is smuggled into the construction of its name. -/
theorem woodinSuccessorPosetName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ : ForcingName P) :
    p ∈ forcingFormula P R woodinSuccessorPosetFormula
      (standardTuple ![woodinSuccessorPosetName P R κ.val, κ.val]) := by
  apply formulaUniqueName_forces woodinSuccessorPosetFormula _ hR htop hp ![κ]
  intro W _ _ _ v
  have ht (x : W) : woodinSuccessorPosetFormula.Evalb (x :> v) ↔
      x = woodinCollapse (v 0) (woodinRestorationCutoff (v 0)) := woodinSuccessorPosetFormula_defined.iff _
  exact ⟨_, (ht _).mpr rfl, fun y hy ↦ (ht y).mp hy⟩

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def successorPosetName (κ : ForcingName A.P) : ForcingName A.P :=
  ⟨woodinSuccessorPosetName A.P A.R κ.val, woodinSuccessorPosetName_isName _ _ _⟩

theorem successorPosetName_value (κ : ForcingName A.P) :
    A.ofName (A.successorPosetName κ) =
      woodinCollapse (A.ofName κ) (woodinRestorationCutoff (A.ofName κ)) := by
  have ht (x : A.Model) : woodinSuccessorPosetFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![κ] : Fin 1 → ForcingName A.P) i))) ↔
        x = woodinCollapse (A.ofName κ) (woodinRestorationCutoff (A.ofName κ)) := woodinSuccessorPosetFormula_defined.iff _
  exact A.formulaName_value woodinSuccessorPosetFormula ![κ]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm) ((ht _).mpr rfl)

end ForcingContext
end ZFVP
