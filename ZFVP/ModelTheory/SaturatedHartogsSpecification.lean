import ZFVP.ModelTheory.SaturatedHartogsStage
import ZFVP.ModelTheory.SaturatedPrefixSpecification

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def saturatedHartogsSpecificationFormula : SetTheorySemisentence 6 :=
  f“P R o γ δ p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !choicelessInaccessibleFormula δ ∧ P ∈ !hierarchyFormula δ ∧ γ ∈ δ ∧ p ∈ P →
    !(tripleForcingTruthFormula totalWoodinCollapseFormula) p P R
      (!saturatedHartogsPosetNameFormula P R o γ δ)
      (!hartogsNumberNameFormula P R (!checkNameFormula o γ)) (!checkNameFormula o δ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem saturatedHartogsPosetName_forces_countable [Countable V] {P R one γ δ p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ) (hp : p ∈ P) :
    p ∈ forcingFormula P R totalWoodinCollapseFormula
      (standardTuple ![saturatedHartogsPosetName P R one γ δ,
        hartogsNumberName P R (checkName one γ), checkName one δ]) := by
  let Q : ForcingName P := ⟨saturatedHartogsPosetName P R one γ δ, saturatedHartogsPosetName_isName P R one γ δ⟩
  let H : ForcingName P := ⟨hartogsNumberName P R (checkName one γ), hartogsNumberName_isName _ _ _⟩
  let b : ForcingName P := ⟨checkName one δ, checkName_isName ht.1 δ⟩
  apply forcingFormula_of_all_generics hR ht hp totalWoodinCollapseFormula ![Q, H, b]
  intro G hG _
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  apply (Defined.eval_iff _).mpr
  change A.ofName Q = totalWoodinCollapse (A.ofName H) (A.check δ)
  have he : A.ofName H = hartogsNumber (A.check γ) :=
    A.hartogsName_value ⟨checkName one γ, checkName_isName ht.1 γ⟩
  let := hδ.1
  rw [he, totalWoodinCollapse_eq]
  exact A.saturatedHartogsCollapseName_value hδ hP hγ

set_option maxHeartbeats 800000 in
theorem eval_saturatedHartogsSpecificationFormula (v : Fin 6 → V) :
    saturatedHartogsSpecificationFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsChoicelessInaccessible (v 4) → v 0 ∈ hierarchy (v 4) → v 3 ∈ v 4 → v 5 ∈ v 0 →
        v 5 ∈ forcingFormula (v 0) (v 1) totalWoodinCollapseFormula
          (standardTuple ![saturatedHartogsPosetName (v 0) (v 1) (v 2) (v 3) (v 4),
            hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3)), checkName (v 2) (v 4)])) := by
  simp [saturatedHartogsSpecificationFormula, Semiformula.eval_nestFormulae,
    Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Fin.forall_fin_succ]
  aesop

theorem saturatedHartogsPosetName_forces {P R one γ δ p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ) (hp : p ∈ P) :
    p ∈ forcingFormula P R totalWoodinCollapseFormula
      (standardTuple ![saturatedHartogsPosetName P R one γ δ,
        hartogsNumberName P R (checkName one γ), checkName one δ]) := by
  have hh := eval_of_countable_zf saturatedHartogsSpecificationFormula (by
    intro W _ _ _ _ v
    exact (eval_saturatedHartogsSpecificationFormula v).mpr
      (fun hR ht hδ hP hγ hp ↦ saturatedHartogsPosetName_forces_countable hR ht hδ hP hγ hp))
    ![P, R, one, γ, δ, p]
  exact (eval_saturatedHartogsSpecificationFormula _).mp hh hR ht hδ hP hγ hp

end ZFVP
