import ZFVP.ModelTheory.ForcingCheckedTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def checkedBoundedForcingFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 5 :=
  f“P R o a p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧ !φ a ∧ p ∈ P →
    !(checkedUnaryForcingFormula φ) P R o p a”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_checkedBoundedForcingFormula (φ : SetTheorySemisentence 1) (v : Fin 5 → V) :
    (checkedBoundedForcingFormula φ).Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        φ.Evalb (fun _ ↦ v 3) → v 4 ∈ v 0 →
        v 4 ∈ forcingFormula (v 0) (v 1) φ (standardTuple ![checkName (v 2) (v 3)])) := by
  have he : (![v 3] : Fin 1 → V) = (fun _ ↦ v 3) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  simp [checkedBoundedForcingFormula, he, Semiformula.Evalb]

theorem forces_checked_bounded (φ : SetTheorySemisentence 1) (hφ : IsBoundedSetFormula φ)
    {P R one a p : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (ha : φ.Evalb (fun _ ↦ a)) (hp : p ∈ P) :
    p ∈ forcingFormula P R φ (standardTuple ![checkName one a]) := by
  have hh := eval_of_countable_zf (checkedBoundedForcingFormula φ) (by
    intro W _ _ _ _ v
    apply (eval_checkedBoundedForcingFormula φ v).mpr
    intro hR ht ha hp
    apply forces_checkedUnary_of_all_generics hR ht hp φ
    intro G hG _hpG
    exact ((ForcingContext.mk (v 0) (v 1) (v 2) G hR ht hG).check_bounded hφ
      (fun _ ↦ v 3)).mp ha) ![P, R, one, a, p]
  exact (eval_checkedBoundedForcingFormula φ ![P, R, one, a, p]).mp hh hR htop ha hp

theorem forces_checked_ordinal {P R one a p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (ha : IsOrdinal a) (hp : p ∈ P) :
    p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![checkName one a]) :=
  forces_checked_bounded IsOrdinal.dfn isOrdinalFormula_bounded hR htop
    ((Defined.eval_iff (fun _ : Fin 1 ↦ a)).mpr ha) hp

end ZFVP
