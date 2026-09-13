import ZFVP.ModelTheory.ForcingFormulaNameSpecification
import ZFVP.ModelTheory.SuccessorRankSetOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance piOneReverseInclusionOrderFormula_defined :
    ℒₛₑₜ-function₁[V] reverseInclusionOrder via piOneReverseInclusionOrderFormula := by
  refine ⟨fun v ↦ ?_⟩
  have hv : ![v 0, v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [← hv]
  exact eval_piOneReverseInclusionOrderFormula _ _

noncomputable def reverseInclusionOrderName (P R Q : V) : V :=
  formulaUniqueName P R piOneReverseInclusionOrderFormula (assignmentPrepend (0 : V) ∅ Q)

instance reverseInclusionOrderName_definable (P R : V) :
    ℒₛₑₜ-function₁[V] (reverseInclusionOrderName P R) := by
  unfold reverseInclusionOrderName
  definability

theorem reverseInclusionOrderName_isName (P R Q : V) :
    IsForcingName P (reverseInclusionOrderName P R Q) := formulaUniqueName_isName _ _ _ _

theorem reverseInclusionOrderName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (Q : ForcingName P) :
    p ∈ forcingFormula P R piOneReverseInclusionOrderFormula
      (standardTuple ![reverseInclusionOrderName P R Q.val, Q.val]) := by
  apply formulaUniqueName_forces piOneReverseInclusionOrderFormula _ hR htop hp ![Q]
  intro W _ _ _ v
  have ht (x : W) : piOneReverseInclusionOrderFormula.Evalb (x :> v) ↔
      x = reverseInclusionOrder (v 0) := piOneReverseInclusionOrderFormula_defined.iff _
  exact ⟨_, (ht _).mpr rfl, fun y hy ↦ (ht y).mp hy⟩

theorem reverseInclusionOrderName_preorder {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (Q : ForcingName P) :
    p ∈ forcingFormula P R forcingPreorderFormula
      (standardTuple ![Q.val, reverseInclusionOrderName P R Q.val]) := by
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let ψ := forcingPreorderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 2) i))
  have hψ := forcingFormula_entailment piOneReverseInclusionOrderFormula ψ (by
    intro W _ _ _ v hv
    have he : v 0 = reverseInclusionOrder (v 1) := piOneReverseInclusionOrderFormula_defined.iff v |>.mp hv
    have ho : IsForcingPreorder (v 1) (v 0) := he ▸ (reverseInclusionOrder_poset (v 1)).1
    simpa [ψ, Semiformula.eval_substs] using ho)
    hR htop hp ![S, Q] (reverseInclusionOrderName_forces hR htop hp Q)
  change p ∈ forcingFormula P R (forcingPreorderFormula.subst
    (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 2) i))) (standardTuple ![S.val, Q.val]) at hψ
  rw [forcingFormula_rename] at hψ
  exact hψ

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def reverseOrderName (Q : ForcingName A.P) : ForcingName A.P :=
  ⟨reverseInclusionOrderName A.P A.R Q.val, reverseInclusionOrderName_isName _ _ _⟩

theorem reverseOrderName_value (Q : ForcingName A.P) :
    A.ofName (A.reverseOrderName Q) = reverseInclusionOrder (A.ofName Q) := by
  have ht (x : A.Model) : piOneReverseInclusionOrderFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![Q] : Fin 1 → ForcingName A.P) i))) ↔
        x = reverseInclusionOrder (A.ofName Q) := piOneReverseInclusionOrderFormula_defined.iff _
  exact A.formulaName_value piOneReverseInclusionOrderFormula ![Q]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm) ((ht _).mpr rfl)

end ForcingContext
end ZFVP
