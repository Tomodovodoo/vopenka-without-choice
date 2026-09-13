import ZFVP.ModelTheory.WoodinSuccessorPosetName
import ZFVP.ModelTheory.ForcingReverseOrderName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcedEmptyName (P R : V) : V := formulaUniqueName P R isEmpty ∅

theorem forcedEmptyName_isName (P R : V) : IsForcingName P (forcedEmptyName P R) :=
  formulaUniqueName_isName _ _ _ _

theorem forcedEmptyName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) :
    p ∈ forcingFormula P R isEmpty (standardTuple ![forcedEmptyName P R]) := by
  apply formulaUniqueName_forces isEmpty _ hR htop hp (![] : Fin 0 → ForcingName P)
  intro W _ _ _ v
  simp

theorem woodinSuccessor_top_forced {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ : ForcingName P)
    (hκ : p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val])) :
    p ∈ forcingFormula P R forcingTopFormula
      (standardTuple ![woodinSuccessorPosetName P R κ.val,
        reverseInclusionOrderName P R (woodinSuccessorPosetName P R κ.val), forcedEmptyName P R]) := by
  let Q : ForcingName P := ⟨woodinSuccessorPosetName P R κ.val, woodinSuccessorPosetName_isName _ _ _⟩
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let t : ForcingName P := ⟨forcedEmptyName P R, forcedEmptyName_isName _ _⟩
  let φ : SetTheorySemisentence 4 :=
    (woodinSuccessorPosetFormula.subst (fun i ↦ .bvar ((![0, 3] : Fin 2 → Fin 4) i))).and
      ((piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 4) i))).and
        ((isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 4) i))).and
          (regularCardinalFormula.subst (fun i ↦ .bvar ((![3] : Fin 1 → Fin 4) i)))))
  let ψ : SetTheorySemisentence 4 := forcingTopFormula.subst
    (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 4) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, t.val, κ.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_and, mem_inter_iff, forcingFormula_rename, forcingFormula_rename,
      forcingFormula_rename, forcingFormula_rename]
    exact ⟨woodinSuccessorPosetName_forces hR htop hp κ,
      reverseInclusionOrderName_forces hR htop hp Q, forcedEmptyName_forces hR htop hp, hκ⟩
  have hψ := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change (woodinSuccessorPosetFormula.subst (fun i ↦ .bvar ((![0, 3] : Fin 2 → Fin 4) i))).Evalb v ∧
      (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 4) i))).Evalb v ∧
      (isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 4) i))).Evalb v ∧
      (regularCardinalFormula.subst (fun i ↦ .bvar ((![3] : Fin 1 → Fin 4) i))).Evalb v at hv
    have hh : v 0 = woodinCollapse (v 3) (woodinRestorationCutoff (v 3)) ∧
        v 1 = reverseInclusionOrder (v 0) ∧ v 2 = ∅ ∧ IsRegularCardinal (v 3) := by
      simpa [φ, Semiformula.eval_substs] using hv
    have hz : (∅ : W) ∈ v 3 := hh.2.2.2.2.1 ∅ (by simp)
    have htop' := woodinCollapse_top hz (woodinRestorationCutoff (v 3))
    have ht : IsForcingTop (v 0) (v 1) (v 2) := by
      rw [hh.2.1, hh.1, hh.2.2.1]
      exact htop'
    simpa [ψ, Semiformula.eval_substs] using ht)
    hR htop hp ![Q, S, t, κ] hφ
  change p ∈ forcingFormula P R (forcingTopFormula.subst
    (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 4) i)))
    (standardTuple ![Q.val, S.val, t.val, κ.val]) at hψ
  rw [forcingFormula_rename] at hψ
  exact hψ

theorem woodinSuccessor_iterand {P R one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (κ : ForcingName P)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val])) :
    IsForcingIterand P R (woodinSuccessorPosetName P R κ.val)
      (reverseInclusionOrderName P R (woodinSuccessorPosetName P R κ.val)) (forcedEmptyName P R) where
  posetName := woodinSuccessorPosetName_isName _ _ _
  orderName := reverseInclusionOrderName_isName _ _ _
  topName := forcedEmptyName_isName _ _
  preorder := fun p hp ↦ reverseInclusionOrderName_preorder hR htop hp
    ⟨woodinSuccessorPosetName P R κ.val, woodinSuccessorPosetName_isName _ _ _⟩
  top := fun p hp ↦ woodinSuccessor_top_forced hR htop hp κ (hκ p hp)

end ZFVP
