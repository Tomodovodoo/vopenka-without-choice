import ZFVP.ModelTheory.TransitiveZFBoundedQuantifiers
import ZFVP.SetTheory.AtomicMembership

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicEqualityTest_iff (P R σ τ p : SetDomain U)
    (e : SetDomain U → SetDomain U → SetDomain U) (E : V → V → V)
    (he : ∀ υ ν, (e υ ν).val = E υ.val ν.val) :
    AtomicEqualityTest P R e σ τ p ↔ AtomicEqualityTest P.val R.val E σ.val τ.val p.val := by
  unfold AtomicEqualityTest
  apply and_congr
  · apply forall_pair_mem_val_iff U σ
    intro υ s
    apply forall_mem_val_iff U P
    intro q
    simp only [← kpair_mem_val_iff U]
    apply imp_congr_right
    intro _
    apply imp_congr_right
    intro _
    apply exists_mem_val_iff U P
    intro r
    simp only [← kpair_mem_val_iff U]
    apply and_congr_right
    intro _
    apply exists_pair_mem_val_iff U τ
    intro ν t
    rw [← he υ ν]
    simp only [← kpair_mem_val_iff U]
    rfl
  · apply forall_pair_mem_val_iff U τ
    intro ν t
    apply forall_mem_val_iff U P
    intro q
    simp only [← kpair_mem_val_iff U]
    apply imp_congr_right
    intro _
    apply imp_congr_right
    intro _
    apply exists_mem_val_iff U P
    intro r
    simp only [← kpair_mem_val_iff U]
    apply and_congr_right
    intro _
    apply exists_pair_mem_val_iff U σ
    intro υ s
    rw [← he υ ν]
    simp only [← kpair_mem_val_iff U]
    rfl

theorem atomicEqualityConditions_val (P R σ τ f : SetDomain U) :
    (atomicEqualityConditions P R σ τ f).val =
      atomicEqualityConditions P.val R.val σ.val τ.val f.val := by
  unfold atomicEqualityConditions
  apply sep_val U
  intro p _
  apply atomicEqualityTest_iff U
  intro υ ν
  rw [value_val_total U, value_val_total U]

theorem atomicEqualityRowStep_val (P R C σ f : SetDomain U) :
    (atomicEqualityRowStep P R C σ f).val =
      atomicEqualityRowStep P.val R.val C.val σ.val f.val := by
  unfold atomicEqualityRowStep definableGraph
  apply repl_val U
  intro τ _
  rw [kpair_val U, atomicEqualityConditions_val U]

theorem atomicEqualityRows_val (P R C σ : SetDomain U) :
    (atomicEqualityRows P R C σ).val = atomicEqualityRows P.val R.val C.val σ.val := by
  unfold atomicEqualityRows
  apply subnameRecursion_val U
  intro τ _ f _
  exact atomicEqualityRowStep_val U P R C τ f

theorem atomicEqualityAt_val (P R C σ τ : SetDomain U) :
    (atomicEqualityAt P R C σ τ).val = atomicEqualityAt P.val R.val C.val σ.val τ.val := by
  unfold atomicEqualityAt
  rw [value_val_total U, atomicEqualityRows_val U]

theorem atomicEquality_val (P R σ τ : SetDomain U) :
    (atomicEquality P R σ τ).val = atomicEquality P.val R.val σ.val τ.val := by
  unfold atomicEquality
  rw [atomicEqualityAt_val U, nameClosure_val U]

theorem atomicMembershipTest_iff (P R σ τ p : SetDomain U) :
    AtomicMembershipTest P R σ τ p ↔ AtomicMembershipTest P.val R.val σ.val τ.val p.val := by
  unfold AtomicMembershipTest
  apply forall_mem_val_iff U P
  intro q
  simp only [← kpair_mem_val_iff U]
  apply imp_congr_right
  intro _
  apply exists_mem_val_iff U P
  intro r
  simp only [← kpair_mem_val_iff U]
  apply and_congr_right
  intro _
  apply exists_pair_mem_val_iff U τ
  intro ν s
  rw [← atomicEquality_val U]
  simp only [← kpair_mem_val_iff U]
  rfl

theorem atomicMembership_val (P R σ τ : SetDomain U) :
    (atomicMembership P R σ τ).val = atomicMembership P.val R.val σ.val τ.val := by
  unfold atomicMembership
  apply sep_val U
  intro p _
  exact atomicMembershipTest_iff U P R σ τ p

end TransitiveZF
end ZFVP
