import ZFVP.ModelTheory.WoodinSuccessorIterand
import ZFVP.ModelTheory.WoodinPrefixSemantics

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def totalWoodinCollapseFormula : SetTheorySemisentence 3 :=
  f“Q κ δ. !woodinCollapseSetFormula Q κ δ ∨ (¬!IsOrdinal.dfn δ ∧ !isEmpty Q)”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def totalWoodinCollapse (κ δ : V) : V := by
  classical
  exact if IsOrdinal δ then woodinCollapse κ δ else ∅

instance totalWoodinCollapseFormula_defined :
    ℒₛₑₜ-function₂[V] totalWoodinCollapse via totalWoodinCollapseFormula := by
  refine ⟨fun v ↦ ?_⟩
  classical
  by_cases hd : IsOrdinal (v 2) <;> simp [totalWoodinCollapseFormula, totalWoodinCollapse, hd]

theorem totalWoodinCollapse_eq (κ δ : V) [IsOrdinal δ] : totalWoodinCollapse κ δ = woodinCollapse κ δ := by
  classical
  simp [totalWoodinCollapse, show IsOrdinal δ from inferInstance]

noncomputable def woodinCollapseName (P R κ δ : V) : V :=
  formulaUniqueName P R totalWoodinCollapseFormula (standardTuple ![κ, δ])

instance woodinCollapseName_definable (P R : V) : ℒₛₑₜ-function₂[V] (woodinCollapseName P R) := by
  unfold woodinCollapseName standardTuple
  definability

theorem woodinCollapseName_isName (P R κ δ : V) : IsForcingName P (woodinCollapseName P R κ δ) :=
  formulaUniqueName_isName _ _ _ _

theorem woodinCollapseName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ δ : ForcingName P) :
    p ∈ forcingFormula P R totalWoodinCollapseFormula
      (standardTuple ![woodinCollapseName P R κ.val δ.val, κ.val, δ.val]) := by
  apply formulaUniqueName_forces totalWoodinCollapseFormula _ hR htop hp ![κ, δ]
  intro W _ _ _ v
  have ht (x : W) : totalWoodinCollapseFormula.Evalb (x :> v) ↔
      x = totalWoodinCollapse (v 0) (v 1) := totalWoodinCollapseFormula_defined.iff _
  exact ⟨_, (ht _).mpr rfl, fun y hy ↦ (ht y).mp hy⟩

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def collapseName (κ δ : ForcingName A.P) : ForcingName A.P :=
  ⟨woodinCollapseName A.P A.R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩

theorem collapseName_value (κ δ : ForcingName A.P) :
    A.ofName (A.collapseName κ δ) = totalWoodinCollapse (A.ofName κ) (A.ofName δ) := by
  have ht (x : A.Model) : totalWoodinCollapseFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![κ, δ] : Fin 2 → ForcingName A.P) i))) ↔
        x = totalWoodinCollapse (A.ofName κ) (A.ofName δ) := totalWoodinCollapseFormula_defined.iff _
  exact A.formulaName_value totalWoodinCollapseFormula ![κ, δ]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm) ((ht _).mpr rfl)

theorem collapseName_value_of_ordinal (κ δ : ForcingName A.P) [IsOrdinal (A.ofName δ)] :
    A.ofName (A.collapseName κ δ) = woodinCollapse (A.ofName κ) (A.ofName δ) :=
  (A.collapseName_value κ δ).trans (totalWoodinCollapse_eq _ _)

end ForcingContext
end ZFVP
