import ZFVP.ModelTheory.ProjectionQuotientName
import ZFVP.ModelTheory.TwoStepDenseNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def projectionQuotientNameFormula : SetTheorySemisentence 4 :=
  f“C Q π o. ∀ z, z ∈ C ↔ ∃ q ∈ Q, z = !kpair.dfn (!checkNameFormula o q) (!value.dfn π q)”

def projectionQuotientOrderNameFormula : SetTheorySemisentence 4 :=
  f“C S π o. ∀ z, z ∈ C ↔ ∃ w ∈ S,
    z = !kpair.dfn (!checkNameFormula o w) (!value.dfn π (!kpair.π₁.dfn w))”

def forcingProjectionFormula : SetTheorySemisentence 5 :=
  f“P R Q S π. !boundedFunctionFormula π Q P ∧
    (∀ q ∈ Q, ∀ r ∈ Q, !kpair.dfn q r ∈ S →
      !kpair.dfn (!value.dfn π q) (!value.dfn π r) ∈ R) ∧
    (∀ q ∈ Q, ∀ p ∈ P, !kpair.dfn p (!value.dfn π q) ∈ R →
      ∃ r ∈ Q, !kpair.dfn r q ∈ S ∧ !value.dfn π r = p)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_projectionQuotientNameFormula (v : Fin 4 → V) :
    projectionQuotientNameFormula.Evalb v ↔ v 0 = projectionQuotientName (v 1) (v 2) (v 3) := by
  rw [mem_ext_iff]
  simp [projectionQuotientNameFormula, mem_projectionQuotientName_iff]

instance projectionQuotientName_defined : ℒₛₑₜ-function₃[V] projectionQuotientName
    via projectionQuotientNameFormula := ⟨eval_projectionQuotientNameFormula⟩

theorem eval_projectionQuotientOrderNameFormula (v : Fin 4 → V) :
    projectionQuotientOrderNameFormula.Evalb v ↔ v 0 = projectionQuotientOrderName (v 1) (v 2) (v 3) := by
  rw [mem_ext_iff]
  simp [projectionQuotientOrderNameFormula, mem_projectionQuotientOrderName_iff]

instance projectionQuotientOrderName_defined : ℒₛₑₜ-function₃[V] projectionQuotientOrderName
    via projectionQuotientOrderNameFormula := ⟨eval_projectionQuotientOrderNameFormula⟩

theorem eval_forcingProjectionFormula (v : Fin 5 → V) :
    forcingProjectionFormula.Evalb v ↔ IsForcingProjection (v 0) (v 1) (v 2) (v 3) (v 4) := by
  simp [forcingProjectionFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2⟩, fun h ↦ ⟨h.maps, h.monotone, h.lift⟩⟩

instance forcingProjectionFormula_defined : Defined
    (fun v : Fin 5 → V ↦ IsForcingProjection (v 0) (v 1) (v 2) (v 3) (v 4))
    forcingProjectionFormula := ⟨eval_forcingProjectionFormula⟩

def projectionQuotientDensityFormula : SetTheorySemisentence 9 :=
  f“P R Q S π o D p q. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingPreorderFormula Q S ∧ !forcingProjectionFormula P R Q S π ∧
    !forcingNameFormula P D ∧
    !(tripleForcingTruthFormula forcingDenseFormula) p P R
      (!projectionQuotientNameFormula Q π o) (!projectionQuotientOrderNameFormula S π o) D ∧
    q ∈ Q ∧ !kpair.dfn (!value.dfn π q) p ∈ R →
    ∃ r ∈ Q, ∃ d ∈ Q, !kpair.dfn r q ∈ S ∧ !kpair.dfn r d ∈ S ∧
      !value.dfn π r ∈ !atomicMembershipFormula P R (!checkNameFormula o d) D”

private theorem forall_six_eq {α : Type*} (a b c d e f : α) (F : α → α → α → α → α → α → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    by rintro h u v w x y z rfl rfl rfl rfl rfl rfl; exact h⟩

private theorem forall_three_eq {α : Type*} (a b c : α) (F : α → α → α → Prop) :
    (∀ x y z, x = a → y = b → z = c → F x y z) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, by rintro h x y z rfl rfl rfl; exact h⟩

private theorem forall_five_eq {α : Type*} (a b c d e : α) (F : α → α → α → α → α → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl, by rintro h u v w x y rfl rfl rfl rfl rfl; exact h⟩

theorem eval_projectionQuotientDensityFormula (v : Fin 9 → V) :
    projectionQuotientDensityFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 5) →
        IsForcingPreorder (v 2) (v 3) → IsForcingProjection (v 0) (v 1) (v 2) (v 3) (v 4) →
        IsForcingName (v 0) (v 6) →
        v 7 ∈ forcingFormula (v 0) (v 1) forcingDenseFormula
          (standardTuple ![projectionQuotientName (v 2) (v 4) (v 5),
            projectionQuotientOrderName (v 3) (v 4) (v 5), v 6]) →
        v 8 ∈ v 2 → ⟨(v 4) ‘ (v 8), v 7⟩ₖ ∈ v 1 →
        ∃ r ∈ v 2, ∃ d ∈ v 2, ⟨r, v 8⟩ₖ ∈ v 3 ∧ ⟨r, d⟩ₖ ∈ v 3 ∧
          (v 4) ‘ r ∈ atomicMembership (v 0) (v 1) (checkName (v 5) d) (v 6)) := by
  simp [projectionQuotientDensityFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Fin.forall_fin_succ, forall_six_eq, forall_three_eq, forall_five_eq]

theorem projectionQuotient_dense_lift_countable [Countable V] {P R Q S π one p q : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hS : IsForcingPreorder Q S) (hπ : IsForcingProjection P R Q S π)
    (D : ForcingName P)
    (hD : p ∈ forcingFormula P R forcingDenseFormula
      (standardTuple ![projectionQuotientName Q π one, projectionQuotientOrderName S π one, D.val]))
    (hq : q ∈ Q) (hqp : ⟨π ‘ q, p⟩ₖ ∈ R) :
    ∃ r ∈ Q, ∃ d ∈ Q, ⟨r, q⟩ₖ ∈ S ∧ ⟨r, d⟩ₖ ∈ S ∧
      π ‘ r ∈ atomicMembership P R (checkName one d) D.val := by
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR (function_value_mem hπ.maps hq)
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let QN : ForcingName P := ⟨projectionQuotientName Q π one, projectionQuotientName_isName htop.1 hπ.maps⟩
  let SN : ForcingName P := ⟨projectionQuotientOrderName S π one,
    projectionQuotientOrderName_isName htop.1 hπ.maps hS⟩
  have hqD := (forcingFormula_regular hR forcingDenseFormula _).2.1 p hD (π ‘ q)
    (function_value_mem hπ.maps hq) hqp
  have hdense : ForcingDense (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) (A.ofName D) := by
    have hd : ForcingDense (A.ofName QN) (A.ofName SN) (A.ofName D) :=
      (Defined.eval_iff _).mp ((A.formula_truth forcingDenseFormula ![QN, SN, D]).mpr ⟨π ‘ q, hqG, hqD⟩)
    rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS] at hd
    exact hd
  have hqA : A.check q ∈ A.projectionQuotient Q π :=
    (A.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hq, hqG⟩
  obtain ⟨x, hxD, hxq⟩ := hdense.2 _ hqA
  obtain ⟨d, hd, hdG, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp (hdense.1 x hxD)
  have hdq := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hxq).1
  rw [← A.check_kpair, A.check_mem_iff] at hdq
  let dN : ForcingName P := ⟨checkName one d, checkName_isName htop.1 d⟩
  have he : nameMemberFormula.Evalb (fun i ↦ A.ofName (![dN, D] i)) := by
    change A.ofName dN ∈ A.ofName D
    exact hxD
  obtain ⟨u, huG, hu⟩ := (A.formula_truth nameMemberFormula ![dN, D]).mp he
  change u ∈ forcingFormula P R nameMemberFormula (standardTuple ![checkName one d, D.val]) at hu
  rw [forcingFormula_nameMember] at hu
  obtain ⟨v, hvG, hvu, hvd⟩ := hG.1.2.2.2 u huG (π ‘ d) hdG
  obtain ⟨r, hr, hrd, hrπ⟩ := hπ.lift d hd v (hG.1.1 v hvG) hvd
  refine ⟨r, hr, d, hd, hS.2.2 r hr d hd q hq hrd hdq, hrd, ?_⟩
  rw [hrπ]
  exact atomicMembership_mono hR hu (hG.1.1 v hvG) hvu

theorem projectionQuotient_dense_lift {P R Q S π one p q : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hS : IsForcingPreorder Q S) (hπ : IsForcingProjection P R Q S π)
    (D : ForcingName P)
    (hD : p ∈ forcingFormula P R forcingDenseFormula
      (standardTuple ![projectionQuotientName Q π one, projectionQuotientOrderName S π one, D.val]))
    (hq : q ∈ Q) (hqp : ⟨π ‘ q, p⟩ₖ ∈ R) :
    ∃ r ∈ Q, ∃ d ∈ Q, ⟨r, q⟩ₖ ∈ S ∧ ⟨r, d⟩ₖ ∈ S ∧
      π ‘ r ∈ atomicMembership P R (checkName one d) D.val := by
  have hh := eval_of_countable_zf projectionQuotientDensityFormula (by
    intro W _ _ _ _ v
    apply (eval_projectionQuotientDensityFormula v).mpr
    intro hR ht hS hπ hD hf hq hqp
    exact projectionQuotient_dense_lift_countable hR ht hS hπ ⟨v 6, hD⟩ hf hq hqp)
    ![P, R, Q, S, π, one, D.val, p, q]
  exact (eval_projectionQuotientDensityFormula _).mp hh hR htop hS hπ D.property hD hq hqp

end ZFVP
