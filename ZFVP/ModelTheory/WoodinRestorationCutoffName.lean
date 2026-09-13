import ZFVP.ModelTheory.ForcingFormulaName
import ZFVP.SetTheory.UniformLeastOrdinalChoice
import ZFVP.SetTheory.WoodinRestorationCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinRestorationCutoffValueFormula : SetTheorySemisentence 2 :=
  leastOrdinalOrZeroFormula woodinRestorationCutoffFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_woodinRestorationCutoffValueFormula (δ κ : V) :
    woodinRestorationCutoffValueFormula.Evalb ![δ, κ] ↔ δ = woodinRestorationCutoff κ :=
  eval_leastOrdinalOrZeroFormula woodinRestorationCutoffFormula IsWoodinRestorationCutoff
    (by definability) eval_woodinRestorationCutoffFormula δ κ

instance woodinRestorationCutoffValueFormula_defined :
    ℒₛₑₜ-function₁[V] woodinRestorationCutoff via woodinRestorationCutoffValueFormula := by
  refine ⟨fun v ↦ ?_⟩
  have hv : ![v 0, v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [← hv]
  exact eval_woodinRestorationCutoffValueFormula _ _

noncomputable def woodinRestorationCutoffName (P R κ : V) : V :=
  formulaUniqueName P R woodinRestorationCutoffValueFormula (assignmentPrepend (0 : V) ∅ κ)

instance woodinRestorationCutoffName_definable (P R : V) :
    ℒₛₑₜ-function₁[V] (woodinRestorationCutoffName P R) := by
  unfold woodinRestorationCutoffName
  definability

theorem woodinRestorationCutoffName_isName (P R κ : V) :
    IsForcingName P (woodinRestorationCutoffName P R κ) := formulaUniqueName_isName _ _ _ _

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def restorationCutoffName (κ : ForcingName A.P) : ForcingName A.P :=
  ⟨woodinRestorationCutoffName A.P A.R κ.val, woodinRestorationCutoffName_isName _ _ _⟩

theorem restorationCutoffName_value (κ : ForcingName A.P) :
    A.ofName (A.restorationCutoffName κ) = woodinRestorationCutoff (A.ofName κ) := by
  have ht (x : A.Model) : woodinRestorationCutoffValueFormula.Evalb
      (x :> (fun i : Fin 1 ↦ A.ofName ((![κ] : Fin 1 → ForcingName A.P) i))) ↔
        x = woodinRestorationCutoff (A.ofName κ) := by
    have hv : (x :> (fun i : Fin 1 ↦ A.ofName ((![κ] : Fin 1 → ForcingName A.P) i))) =
        ![x, A.ofName κ] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    rw [hv]
    exact eval_woodinRestorationCutoffValueFormula _ _
  exact A.formulaName_value woodinRestorationCutoffValueFormula ![κ]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm)
    ((ht _).mpr rfl)

theorem restorationCutoffName_spec (κ : ForcingName A.P) {δ : A.Model}
    (hδ : IsWoodinRestorationCutoff (A.ofName κ) δ) :
    IsWoodinRestorationCutoff (A.ofName κ) (A.ofName (A.restorationCutoffName κ)) ∧
      A.ofName (A.restorationCutoffName κ) ⊆ δ := by
  rw [A.restorationCutoffName_value]
  exact ⟨(woodinRestorationCutoff_spec hδ).2.1, woodinRestorationCutoff_le hδ⟩

end ForcingContext
end ZFVP
