import ZFVP.SetTheory.AtomicMembership
import ZFVP.SetTheory.ForcingDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

private theorem forall_five_eq {α : Type*} (a b c d e : α) (Q : α → α → α → α → α → Prop) :
    (∀ x y z u v, x = a → y = b → z = c → u = d → v = e → Q x y z u v) ↔ Q a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl, by rintro h x y z u v rfl rfl rfl rfl rfl; exact h⟩

def atomicEqualityConditionsFormula : SetTheorySemisentence 6 :=
  f“C P R x y f. ∀ p, p ∈ C ↔ p ∈ P ∧
    (∀ u, ∀ s, !kpair.dfn u s ∈ x → ∀ q ∈ P, !kpair.dfn q p ∈ R → !kpair.dfn q s ∈ R →
      ∃ r ∈ P, !kpair.dfn r q ∈ R ∧ ∃ v, ∃ t, !kpair.dfn v t ∈ y ∧ !kpair.dfn r t ∈ R ∧
        r ∈ !value.dfn (!value.dfn f u) v) ∧
    (∀ v, ∀ t, !kpair.dfn v t ∈ y → ∀ q ∈ P, !kpair.dfn q p ∈ R → !kpair.dfn q t ∈ R →
      ∃ r ∈ P, !kpair.dfn r q ∈ R ∧ ∃ u, ∃ s, !kpair.dfn u s ∈ x ∧ !kpair.dfn r s ∈ R ∧
        r ∈ !value.dfn (!value.dfn f u) v)”

def atomicEqualityRowStepFormula : SetTheorySemisentence 6 :=
  f“g P R C x f. ∀ z, z ∈ g ↔ ∃ y ∈ C,
    !kpair.dfn z y (!atomicEqualityConditionsFormula P R x y f)”

def atomicEqualityRowsTableFormula : SetTheorySemisentence 5 :=
  f“f P R C x. !IsFunction.dfn f ∧ !domain.dfn f = !nameClosureFormula x ∧
    ∀ t ∈ !nameClosureFormula x,
      !value.dfn f t = !atomicEqualityRowStepFormula P R C t (!restrict.dfn f (!domain.dfn t))”

def atomicEqualityRowsFormula : SetTheorySemisentence 5 :=
  f“y P R C x. ∃ f, !atomicEqualityRowsTableFormula f P R C x ∧ y = !value.dfn f x”

def atomicEqualityFormula : SetTheorySemisentence 5 :=
  f“C P R x y. C = !value.dfn (!atomicEqualityRowsFormula P R (!nameClosureFormula y) x) y”

def atomicMembershipFormula : SetTheorySemisentence 5 :=
  f“C P R x y. ∀ p, p ∈ C ↔ p ∈ P ∧
    ∀ q ∈ P, !kpair.dfn q p ∈ R → ∃ r ∈ P, !kpair.dfn r q ∈ R ∧
      ∃ v, ∃ s, !kpair.dfn v s ∈ y ∧ !kpair.dfn r s ∈ R ∧ r ∈ !atomicEqualityFormula P R x v”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 800000 in
instance atomicEqualityConditionsFormula_defined :
    ℒₛₑₜ-function₅[V] atomicEqualityConditions via atomicEqualityConditionsFormula :=
  ⟨fun v ↦ by
    change atomicEqualityConditionsFormula.Evalb v ↔
      v 0 = atomicEqualityConditions (v 1) (v 2) (v 3) (v 4) (v 5)
    rw [mem_ext_iff]
    simp [atomicEqualityConditionsFormula, atomicEqualityConditions, AtomicEqualityTest]⟩

instance atomicEqualityRowStepFormula_defined :
    ℒₛₑₜ-function₅[V] atomicEqualityRowStep via atomicEqualityRowStepFormula :=
  ⟨fun v ↦ by
    change atomicEqualityRowStepFormula.Evalb v ↔
      v 0 = atomicEqualityRowStep (v 1) (v 2) (v 3) (v 4) (v 5)
    rw [mem_ext_iff]
    simp [atomicEqualityRowStepFormula, atomicEqualityRowStep, mem_definableGraph_iff,
      Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ,
      forall_five_eq]⟩

instance atomicEqualityRowsTableFormula_defined :
    Defined (L := ℒₛₑₜ) (fun v : Fin 5 → V ↦
      IsSubnameRecursion (nameClosure (v 4)) (atomicEqualityRowStep (v 1) (v 2) (v 3)) (v 0))
      atomicEqualityRowsTableFormula :=
  ⟨fun v ↦ by simp [atomicEqualityRowsTableFormula, IsSubnameRecursion,
    Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ,
    forall_five_eq]⟩

instance atomicEqualityRowsFormula_defined :
    ℒₛₑₜ-function₄[V] atomicEqualityRows via atomicEqualityRowsFormula :=
  ⟨fun v ↦ by
    change atomicEqualityRowsFormula.Evalb v ↔ v 0 = atomicEqualityRows (v 1) (v 2) (v 3) (v 4)
    have he : v 0 = atomicEqualityRows (v 1) (v 2) (v 3) (v 4) ↔
        ∃ f, IsSubnameRecursion (nameClosure (v 4)) (atomicEqualityRowStep (v 1) (v 2) (v 3)) f ∧
          v 0 = f ‘ (v 4) := by
      constructor
      · intro h
        exact ⟨subnameRecursionTable (atomicEqualityRowStep (v 1) (v 2) (v 3)) (by definability) (v 4),
          subnameRecursionTable_spec _ _ _, h⟩
      · rintro ⟨f, hf, hv⟩
        exact hv.trans (congrArg (fun g ↦ g ‘ (v 4))
          ((subnameRecursionTable_eq_iff _ _ _ _).mpr hf))
    rw [he]
    simp [atomicEqualityRowsFormula, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ, forall_five_eq]⟩

instance atomicEqualityFormula_defined :
    ℒₛₑₜ-function₄[V] atomicEquality via atomicEqualityFormula :=
  ⟨fun v ↦ by simp [atomicEqualityFormula, atomicEquality, atomicEqualityAt]⟩

instance atomicMembershipFormula_defined :
    ℒₛₑₜ-function₄[V] atomicMembership via atomicMembershipFormula :=
  ⟨fun v ↦ by
    change atomicMembershipFormula.Evalb v ↔ v 0 = atomicMembership (v 1) (v 2) (v 3) (v 4)
    rw [mem_ext_iff]
    simp [atomicMembershipFormula, mem_atomicMembership_iff, AtomicMembershipTest]⟩

end ZFVP
