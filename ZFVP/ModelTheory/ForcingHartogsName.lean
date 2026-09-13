import ZFVP.ModelTheory.ForcingFormulaNameSpecification
import ZFVP.SetTheory.HartogsDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The Hartogs number computed in the forcing extension. -/
noncomputable def hartogsNumberName (P R τ : V) : V :=
  formulaUniqueName P R hartogsNumberFormula (assignmentPrepend (0 : V) ∅ τ)

instance hartogsNumberName_definable (P R : V) : ℒₛₑₜ-function₁[V] (hartogsNumberName P R) := by
  unfold hartogsNumberName
  definability

theorem hartogsNumberName_isName (P R τ : V) : IsForcingName P (hartogsNumberName P R τ) :=
  formulaUniqueName_isName _ _ _ _

theorem hartogsNumberName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (τ : ForcingName P) :
    p ∈ forcingFormula P R hartogsNumberFormula (standardTuple ![hartogsNumberName P R τ.val, τ.val]) := by
  apply formulaUniqueName_forces hartogsNumberFormula _ hR htop hp ![τ]
  intro W _ _ _ v
  have ht (x : W) : hartogsNumberFormula.Evalb (x :> v) ↔ x = hartogsNumber (v 0) :=
    hartogsNumberFormula_defined.iff _
  exact ⟨_, (ht _).mpr rfl, fun y hy ↦ (ht y).mp hy⟩

theorem hartogsNumberName_forces_initial {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (τ : ForcingName P) :
    p ∈ forcingFormula P R initialOrdinalFormula (standardTuple ![hartogsNumberName P R τ.val]) := by
  let κ : ForcingName P := ⟨hartogsNumberName P R τ.val, hartogsNumberName_isName _ _ _⟩
  let ψ : SetTheorySemisentence 2 := initialOrdinalFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))
  have hh := forcingFormula_entailment hartogsNumberFormula ψ (by
    intro W _ _ _ v hv
    have he : v 0 = hartogsNumber (v 1) := (Defined.eval_iff v).mp hv
    have hi : IsInitialOrdinal (v 0) := he.symm ▸ hartogsNumber_initial (v 1)
    simpa [ψ, Semiformula.eval_substs] using hi)
    hR htop hp ![κ, τ] (hartogsNumberName_forces hR htop hp τ)
  change p ∈ forcingFormula P R (initialOrdinalFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))) (standardTuple ![κ.val, τ.val]) at hh
  rw [forcingFormula_rename] at hh
  exact hh

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def hartogsName (τ : ForcingName A.P) : ForcingName A.P :=
  ⟨hartogsNumberName A.P A.R τ.val, hartogsNumberName_isName _ _ _⟩

theorem hartogsName_value (τ : ForcingName A.P) :
    A.ofName (A.hartogsName τ) = hartogsNumber (A.ofName τ) := by
  have ht (x : A.Model) : hartogsNumberFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![τ] : Fin 1 → ForcingName A.P) i))) ↔
        x = hartogsNumber (A.ofName τ) := hartogsNumberFormula_defined.iff _
  exact A.formulaName_value hartogsNumberFormula ![τ]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm) ((ht _).mpr rfl)

end ForcingContext
end ZFVP

