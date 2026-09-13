import ZFVP.ModelTheory.SaturatedWoodinIterand
import ZFVP.ModelTheory.ForcingIsomorphismCanonicalNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def saturatedPrefixSpecificationFormula : SetTheorySemisentence 6 :=
  f“P R o κ δ p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !choicelessInaccessibleFormula δ ∧ P ∈ !hierarchyFormula δ ∧ κ ⊆ δ ∧ p ∈ P →
    !(tripleForcingTruthFormula totalWoodinCollapseFormula) p P R
      (!saturatedWoodinPrefixPosetNameFormula P R o κ δ) (!checkNameFormula o κ) (!checkNameFormula o δ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem saturatedWoodinPrefixPosetName_forces_countable [Countable V] {P R one κ δ p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ) (hp : p ∈ P) :
    p ∈ forcingFormula P R totalWoodinCollapseFormula
      (standardTuple ![saturatedWoodinPrefixPosetName P R one κ δ, checkName one κ, checkName one δ]) := by
  let Q : ForcingName P := ⟨saturatedWoodinPrefixPosetName P R one κ δ,
    saturatedWoodinPrefixPosetName_isName P R one κ δ⟩
  let a : ForcingName P := ⟨checkName one κ, checkName_isName ht.1 κ⟩
  let b : ForcingName P := ⟨checkName one δ, checkName_isName ht.1 δ⟩
  apply forcingFormula_of_all_generics hR ht hp totalWoodinCollapseFormula ![Q, a, b]
  intro G hG _
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  apply (Defined.eval_iff _).mpr
  change A.ofName Q = totalWoodinCollapse (A.check κ) (A.check δ)
  let := hδ.1
  rw [totalWoodinCollapse_eq]
  exact A.saturatedWoodinPosetName_value hδ hP hκ

theorem eval_saturatedPrefixSpecificationFormula (v : Fin 6 → V) :
    saturatedPrefixSpecificationFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsChoicelessInaccessible (v 4) → v 0 ∈ hierarchy (v 4) → v 3 ⊆ v 4 → v 5 ∈ v 0 →
        v 5 ∈ forcingFormula (v 0) (v 1) totalWoodinCollapseFormula
          (standardTuple ![saturatedWoodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4),
            checkName (v 2) (v 3), checkName (v 2) (v 4)])) := by
  simp [saturatedPrefixSpecificationFormula, Semiformula.eval_nestFormulae, Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Fin.forall_fin_succ]
  constructor
  · intro h hR ht hδ hP hκ hp
    exact h hR (by rintro a b c rfl rfl rfl; exact ht) hδ hP hκ hp
      _ _ _ _ _ _ rfl rfl rfl (by rintro a b c d e rfl rfl rfl rfl rfl; rfl) rfl rfl
  · intro h hR ht hδ hP hκ hp a b c d e f ha hb hc hd he hf
    subst a b c e f
    have hd' := hd _ _ _ _ _ rfl rfl rfl rfl rfl
    subst d
    exact h hR (ht _ _ _ rfl rfl rfl) hδ hP hκ hp

theorem saturatedWoodinPrefixPosetName_forces {P R one κ δ p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ) (hp : p ∈ P) :
    p ∈ forcingFormula P R totalWoodinCollapseFormula
      (standardTuple ![saturatedWoodinPrefixPosetName P R one κ δ, checkName one κ, checkName one δ]) := by
  have hh := eval_of_countable_zf saturatedPrefixSpecificationFormula (by
    intro W _ _ _ _ v
    exact (eval_saturatedPrefixSpecificationFormula v).mpr
      (fun hR ht hδ hP hκ hp ↦ saturatedWoodinPrefixPosetName_forces_countable hR ht hδ hP hκ hp))
    ![P, R, one, κ, δ, p]
  exact (eval_saturatedPrefixSpecificationFormula _).mp hh hR ht hδ hP hκ hp

end ZFVP
