import ZFVP.ModelTheory.WoodinRestorationCutoffName
import ZFVP.ModelTheory.ForcingFormulaNameSpecification

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinRestorationCutoffName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ : ForcingName P) :
    p ∈ forcingFormula P R woodinRestorationCutoffValueFormula
      (standardTuple ![woodinRestorationCutoffName P R κ.val, κ.val]) := by
  apply formulaUniqueName_forces woodinRestorationCutoffValueFormula _ hR htop hp ![κ]
  intro W _ _ _ v
  have ht (x : W) : woodinRestorationCutoffValueFormula.Evalb (x :> v) ↔
      x = woodinRestorationCutoff (v 0) := woodinRestorationCutoffValueFormula_defined.iff _
  exact ⟨_, (ht _).mpr rfl, fun y hy ↦ (ht y).mp hy⟩

theorem woodinRestorationCutoffName_forces_ordinal {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ : ForcingName P) :
    p ∈ forcingFormula P R IsOrdinal.dfn
      (standardTuple ![woodinRestorationCutoffName P R κ.val]) := by
  let δ : ForcingName P :=
    ⟨woodinRestorationCutoffName P R κ.val, woodinRestorationCutoffName_isName _ _ _⟩
  let ψ : SetTheorySemisentence 2 := IsOrdinal.dfn.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))
  have hh := forcingFormula_entailment woodinRestorationCutoffValueFormula ψ (by
    intro W _ _ _ v hv
    have he : v 0 = woodinRestorationCutoff (v 1) := (Defined.eval_iff v).mp hv
    have hi : IsOrdinal (v 0) := he.symm ▸ woodinRestorationCutoff_ordinal (v 1)
    simpa [ψ, Semiformula.eval_substs] using hi)
    hR htop hp ![δ, κ] (woodinRestorationCutoffName_forces hR htop hp κ)
  change p ∈ forcingFormula P R (IsOrdinal.dfn.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))) (standardTuple ![δ.val, κ.val]) at hh
  rw [forcingFormula_rename] at hh
  exact hh

end ZFVP
