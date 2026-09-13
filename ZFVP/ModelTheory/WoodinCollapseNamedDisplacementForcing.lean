import ZFVP.ModelTheory.WoodinCollapseDisplacementForcing
import ZFVP.SetTheory.ForcingRenaming

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def collapseDisplacementPreInputFormula : SetTheorySemisentence 6 :=
  f“Q S κ δ p q. !regularCardinalFormula κ ∧ !IsOrdinal.dfn δ ∧
    !totalWoodinCollapseFormula Q κ δ ∧ !piOneReverseInclusionOrderFormula S Q ∧ p ∈ Q ∧ q ∈ Q”

def collapseDisplacementJoinedFormula : SetTheorySemisentence 8 :=
  (collapseDisplacementPreInputFormula.subst (fun i ↦ .bvar ((![0, 1, 2, 3, 4, 5] : Fin 6 → Fin 8) i))).and
    ((woodinCollapseDisplacementFormula.subst (fun i ↦ .bvar ((![6, 2, 3, 4, 5] : Fin 5 → Fin 8) i))).and
      (sparseConverseGraphFormula.subst (fun i ↦ .bvar ((![7, 6] : Fin 2 → Fin 8) i))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_collapseDisplacementPreInputFormula (v : Fin 6 → V) :
    collapseDisplacementPreInputFormula.Evalb v ↔
    IsRegularCardinal (v 2) ∧ IsOrdinal (v 3) ∧
      v 0 = totalWoodinCollapse (v 2) (v 3) ∧ v 1 = reverseInclusionOrder (v 0) ∧
      v 4 ∈ v 0 ∧ v 5 ∈ v 0 := by simp [collapseDisplacementPreInputFormula]
theorem collapseDisplacement_joined_input (v : Fin 8 → V)
    (h : collapseDisplacementJoinedFormula.Evalb v) : collapseDisplacementInputFormula.Evalb v := by
  apply (eval_collapseDisplacementInputFormula v).mpr
  change (collapseDisplacementPreInputFormula.subst
      (fun i ↦ .bvar ((![0, 1, 2, 3, 4, 5] : Fin 6 → Fin 8) i))).Evalb v ∧
    (woodinCollapseDisplacementFormula.subst
      (fun i ↦ .bvar ((![6, 2, 3, 4, 5] : Fin 5 → Fin 8) i))).Evalb v ∧
    (sparseConverseGraphFormula.subst
      (fun i ↦ .bvar ((![7, 6] : Fin 2 → Fin 8) i))).Evalb v at h
  simpa [Semiformula.eval_substs, and_assoc] using h

theorem woodinCollapseDisplacementName_forces_output {P R top r : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hr : r ∈ P)
    (Q S κ δ p q : ForcingName P)
    (hpre : r ∈ forcingFormula P R collapseDisplacementPreInputFormula
      (standardTuple ![Q.val, S.val, κ.val, δ.val, p.val, q.val])) :
    let f := woodinCollapseDisplacementName P R κ.val δ.val p.val q.val
    let g := ZFVP.collapseConverseName P R f
    r ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple ![Q.val, S.val, κ.val, δ.val, p.val, q.val, f, g]) := by
  dsimp only
  let f : ForcingName P := ⟨woodinCollapseDisplacementName P R κ.val δ.val p.val q.val,
    woodinCollapseDisplacementName_isName _ _ _ _ _ _⟩
  let g : ForcingName P := ⟨ZFVP.collapseConverseName P R f.val, collapseConverseName_isName _ _ _⟩
  let v : Fin 8 → ForcingName P := ![Q, S, κ, δ, p, q, f, g]
  have hj : r ∈ forcingFormula P R collapseDisplacementJoinedFormula
      (standardTuple (fun i ↦ (v i).val)) := by
    rw [collapseDisplacementJoinedFormula, forcingFormula_and, mem_inter_iff,
      forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename]
    exact ⟨hpre, woodinCollapseDisplacementName_forces hR ht hr κ δ p q,
      ZFVP.collapseConverseName_forces hR ht hr f⟩
  exact collapseDisplacement_forces_output hR ht hr v
    (forcingFormula_entailment collapseDisplacementJoinedFormula collapseDisplacementInputFormula
      (fun _ _ _ _ ↦ collapseDisplacement_joined_input) hR ht hr v hj)

end ZFVP


