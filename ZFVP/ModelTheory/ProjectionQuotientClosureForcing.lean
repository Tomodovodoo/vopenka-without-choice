import ZFVP.ModelTheory.ProjectionClosureComposition
import ZFVP.ModelTheory.ForcingCheckedTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def allProjectionQuotientClosedBelowFormula : SetTheorySemisentence 7 :=
  f“P R o Q S π η. ∀ p ∈ P,
    !(tripleForcingTruthFormula forcingSeparativeClosedBelowFormula) p P R
      (!projectionQuotientNameFormula Q π o) (!projectionQuotientOrderNameFormula S π o)
      (!checkNameFormula o η)”

def forcingSplitProjectionFormula : SetTheorySemisentence 6 :=
  f“P R Q S π E. !forcingProjectionFormula P R Q S π ∧ !boundedFunctionFormula E P Q ∧
    (∀ p ∈ P, !value.dfn π (!value.dfn E p) = p) ∧
    (∀ q ∈ Q, ∀ p ∈ P, !kpair.dfn q (!value.dfn E p) ∈ S ↔ !kpair.dfn (!value.dfn π q) p ∈ R)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ForcesProjectionQuotientClosedBelow (P R one Q S π η : V) : Prop :=
  ∀ p ∈ P, p ∈ forcingFormula P R forcingSeparativeClosedBelowFormula
    (standardTuple ![projectionQuotientName Q π one, projectionQuotientOrderName S π one, checkName one η])

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

instance allProjectionQuotientClosedBelowFormula_defined : Defined
    (fun v : Fin 7 → V ↦ ForcesProjectionQuotientClosedBelow (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    allProjectionQuotientClosedBelowFormula :=
  ⟨fun v ↦ by simp [allProjectionQuotientClosedBelowFormula, ForcesProjectionQuotientClosedBelow, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]⟩

instance forcingSplitProjectionFormula_defined : Defined
    (fun v : Fin 6 → V ↦ IsForcingSplitProjection (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
    forcingSplitProjectionFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [forcingSplitProjectionFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
    fun h ↦ ⟨h.projection, h.maps, h.right_inverse, h.below⟩⟩

theorem ForcingContext.projectionQuotient_closedBelow_of_forced (A : ForcingContext V)
    {Q S π η : V} (hπ : IsForcingProjection A.P A.R Q S π) (hS : IsForcingPreorder Q S)
    (hc : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R forcingSeparativeClosedBelowFormula
      (standardTuple ![projectionQuotientName Q π A.one,
        projectionQuotientOrderName S π A.one, checkName A.one η])) :
    IsForcingClosedBelow (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) (A.check η) := by
  let QN : ForcingName A.P := ⟨projectionQuotientName Q π A.one,
    projectionQuotientName_isName A.top.1 hπ.maps⟩
  let SN : ForcingName A.P := ⟨projectionQuotientOrderName S π A.one,
    projectionQuotientOrderName_isName A.top.1 hπ.maps hS⟩
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have ht := (Defined.eval_iff _).mp ((A.formula_truth forcingSeparativeClosedBelowFormula
    ![QN, SN, ⟨checkName A.one η, checkName_isName A.top.1 η⟩]).mpr
      ⟨p, hp, hc p (A.generic.1.1 p hp)⟩)
  change IsForcingClosedBelow (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN)) (A.check η) at ht
  rwa [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS] at ht

theorem projectionQuotient_closedBelow_forced_of_generics [Countable V]
    {P R one Q S π η : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hc : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      IsForcingClosedBelow (A.projectionQuotient Q π)
        (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) (A.check η)) :
    ∀ p ∈ P, p ∈ forcingFormula P R forcingSeparativeClosedBelowFormula
      (standardTuple ![projectionQuotientName Q π one, projectionQuotientOrderName S π one, checkName one η]) := by
  let QN : ForcingName P := ⟨projectionQuotientName Q π one, projectionQuotientName_isName htop.1 hπ.maps⟩
  let SN : ForcingName P := ⟨projectionQuotientOrderName S π one, projectionQuotientOrderName_isName htop.1 hπ.maps hS⟩
  apply (all_forces_iff_all_generics hR htop forcingSeparativeClosedBelowFormula
    ![QN, SN, ⟨checkName one η, checkName_isName htop.1 η⟩]).mpr
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  apply (Defined.eval_iff _).mpr
  change IsForcingClosedBelow (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN)) (A.check η)
  rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS]
  exact hc G hG

end ZFVP
