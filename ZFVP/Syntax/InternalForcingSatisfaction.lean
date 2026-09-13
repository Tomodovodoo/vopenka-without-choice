import ZFVP.Syntax.DirectMembershipAtoms
import ZFVP.Syntax.FormulaRecursion
import ZFVP.SetTheory.AtomicForcingDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def InternalForcingAtomicHolds (P R n b r args p : V) : Prop :=
  ∃ i ∈ n, ∃ j ∈ n, args = boundPairArguments i j ∧
    (((r = equalityToken ∨ r = relationToken (0 : V)) ∧ p ∈ atomicEquality P R (b ‘ i) (b ‘ j)) ∨
      (r = relationToken (1 : V) ∧ p ∈ atomicMembership P R (b ‘ i) (b ‘ j)))

instance internalForcingAtomicHolds_definable (P R : V) :
    ℒₛₑₜ-relation₅ (InternalForcingAtomicHolds P R) := by
  unfold InternalForcingAtomicHolds equalityToken
  definability

def InternalForcingStepHolds (P R D c previous b p : V) : Prop :=
  kpair.π₂ c = truthCode ∨
  (∃ r args, kpair.π₂ c = atomCode r args ∧ InternalForcingAtomicHolds P R (kpair.π₁ c) b r args p) ∨
  (∃ r args, kpair.π₂ c = negAtomCode r args ∧
    ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ¬InternalForcingAtomicHolds P R (kpair.π₁ c) b r args q) ∨
  (∃ φ ψ, kpair.π₂ c = andCode φ ψ ∧
    ⟨b, p⟩ₖ ∈ previous ‘ ⟨kpair.π₁ c, φ⟩ₖ ∧ ⟨b, p⟩ₖ ∈ previous ‘ ⟨kpair.π₁ c, ψ⟩ₖ) ∨
  (∃ φ ψ, kpair.π₂ c = orCode φ ψ ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R →
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
      (⟨b, r⟩ₖ ∈ previous ‘ ⟨kpair.π₁ c, φ⟩ₖ ∨ ⟨b, r⟩ₖ ∈ previous ‘ ⟨kpair.π₁ c, ψ⟩ₖ)) ∨
  (∃ φ, kpair.π₂ c = allCode φ ∧ ∀ x ∈ D,
    ⟨assignmentPrepend (kpair.π₁ c) b x, p⟩ₖ ∈ previous ‘ ⟨succ (kpair.π₁ c), φ⟩ₖ) ∨
  ∃ φ, kpair.π₂ c = existsCode φ ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R →
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ∃ x ∈ D,
      ⟨assignmentPrepend (kpair.π₁ c) b x, r⟩ₖ ∈ previous ‘ ⟨succ (kpair.π₁ c), φ⟩ₖ

instance internalForcingStepHolds_definable (P R D : V) :
    ℒₛₑₜ-relation₄ (InternalForcingStepHolds P R D) := by
  unfold InternalForcingStepHolds truthCode
  repeat' first | apply Language.Definable.or | (solve | definability)

noncomputable def internalForcingStep (P R D c previous : V) : V :=
  {z ∈ (D ^ (kpair.π₁ c)) ×ˢ P ; InternalForcingStepHolds P R D c previous (kpair.π₁ z) (kpair.π₂ z)}

theorem pair_mem_internalForcingStep (P R D c previous b p : V) :
    ⟨b, p⟩ₖ ∈ internalForcingStep P R D c previous ↔
      b ∈ D ^ (kpair.π₁ c) ∧ p ∈ P ∧ InternalForcingStepHolds P R D c previous b p := by
  simp [internalForcingStep, and_assoc]

instance internalForcingStep_definable (P R D : V) : ℒₛₑₜ-function₂ (internalForcingStep P R D) := by
  have h : ℒₛₑₜ-relation₃ (fun S c previous : V ↦ ∀ z, z ∈ S ↔
      z ∈ (D ^ (kpair.π₁ c)) ×ˢ P ∧
        InternalForcingStepHolds P R D c previous (kpair.π₁ z) (kpair.π₂ z)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalForcingStep P R D (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [internalForcingStep, mem_sep_iff]

/-- Values are sets of assignment/condition pairs. The recursion covers every
internal membership-formula code, without assuming standard natural numbers. -/
noncomputable def internalForcingGraph (P R D : V) : V :=
  formulaRecursion membershipLanguageCode ∅ (internalForcingStep P R D) inferInstance

instance internalForcingGraph_isFunction (P R D : V) : IsFunction (internalForcingGraph P R D) :=
  formulaRecursion_isFunction _ _ _ _

@[simp] theorem domain_internalForcingGraph (P R D : V) :
    domain (internalForcingGraph P R D) = formulaFamily membershipLanguageCode ∅ :=
  domain_formulaRecursion _ _ _ _

def InternalForces (P R D n φ b p : V) : Prop := ⟨b, p⟩ₖ ∈ (internalForcingGraph P R D) ‘ ⟨n, φ⟩ₖ

theorem internalForces_iff_step {P R D n φ b p : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    InternalForces P R D n φ b p ↔ b ∈ D ^ n ∧ p ∈ P ∧
      InternalForcingStepHolds P R D ⟨n, φ⟩ₖ ((internalForcingGraph P R D) ↾
        (predecessors (subformulaRelation (formulaFamily membershipLanguageCode ∅))
          (formulaFamily membershipLanguageCode ∅) ⟨n, φ⟩ₖ)) b p := by
  have he := formulaRecursion_value membershipLanguageCode ∅ (internalForcingStep P R D) inferInstance
    ((mem_formulaSet_iff _ _ _ _).mp hφ)
  unfold InternalForces internalForcingGraph
  rw [he, pair_mem_internalForcingStep]
  simp only [kpair.π₁_kpair]

theorem internalForces_assignment {P R D n φ b p : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (h : InternalForces P R D n φ b p) : b ∈ D ^ n :=
  ((internalForces_iff_step hφ).mp h).1

theorem internalForces_condition {P R D n φ b p : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (h : InternalForces P R D n φ b p) : p ∈ P :=
  ((internalForces_iff_step hφ).mp h).2.1

end ZFVP
