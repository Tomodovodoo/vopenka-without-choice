import ZFVP.ModelTheory.ForcingSmallInaccessible
import ZFVP.ModelTheory.ForcingCheckedTruth
import ZFVP.SetTheory.WoodinPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def smallForcingInaccessibleFormula : SetTheorySemisentence 5 :=
  f“P R o δ p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !choicelessInaccessibleFormula δ ∧ P ∈ !hierarchyFormula δ ∧ p ∈ P →
      !(checkedUnaryForcingFormula choicelessInaccessibleFormula) P R o p δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_smallForcingInaccessibleFormula (v : Fin 5 → V) :
    smallForcingInaccessibleFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsChoicelessInaccessible (v 3) → v 0 ∈ hierarchy (v 3) → v 4 ∈ v 0 →
        v 4 ∈ forcingFormula (v 0) (v 1) choicelessInaccessibleFormula
          (standardTuple ![checkName (v 2) (v 3)])) := by
  simp [smallForcingInaccessibleFormula]

theorem smallForcing_forces_inaccessible_countable [Countable V] {P R one δ p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P) :
    p ∈ forcingFormula P R choicelessInaccessibleFormula (standardTuple ![checkName one δ]) := by
  refine forces_checkedUnary_of_all_generics hR htop hp choicelessInaccessibleFormula ?_
  intro G hG _hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  exact (choicelessInaccessibleFormula_defined.iff _).mpr (A.check_inaccessible_of_small hδ hP)

theorem smallForcing_forces_inaccessible {P R one δ p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P) :
    p ∈ forcingFormula P R choicelessInaccessibleFormula (standardTuple ![checkName one δ]) := by
  have hh := eval_of_countable_zf smallForcingInaccessibleFormula (by
    intro W _ _ _ _ v
    exact (eval_smallForcingInaccessibleFormula v).mpr
      (fun hR htop hδ hP hp ↦ smallForcing_forces_inaccessible_countable (P := v 0) (R := v 1) (one := v 2) (δ := v 3) (p := v 4) hR htop hδ hP hp))
    ![P, R, one, δ, p]
  exact (eval_smallForcingInaccessibleFormula ![P, R, one, δ, p]).mp hh hR htop hδ hP hp

theorem IsWoodinPrefixCutoff.localCutoff (A : ForcingContext V) {κ δ : V}
    (hδ : IsWoodinPrefixCutoff A.P A.R A.one κ δ) (hP : A.P ∈ hierarchy δ) :
    IsWoodinRestorationCutoff (A.check κ) (A.check δ) :=
  ⟨(A.check_mem_iff _ _).mpr hδ.1, A.check_inaccessible_of_small hδ.2.1 hP,
    (hδ.localRestoration A).2⟩

end ZFVP
