import ZFVP.Syntax.FormulaRecursion
import ZFVP.Syntax.AtomicSatisfaction
import ZFVP.Syntax.Assignments

/-! Internal satisfaction: recursion assigns each formula its satisfying bound assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def SatisfactionStepHolds (L Γ M e p previous b : V) : Prop :=
  kpair.π₂ p = truthCode ∨
  (∃ r args, kpair.π₂ p = atomCode r args ∧ AtomicHolds L Γ M e (kpair.π₁ p) b r args) ∨
  (∃ r args, kpair.π₂ p = negAtomCode r args ∧ ¬AtomicHolds L Γ M e (kpair.π₁ p) b r args) ∨
  (∃ φ ψ, kpair.π₂ p = andCode φ ψ ∧
    b ∈ previous ‘ ⟨kpair.π₁ p, φ⟩ₖ ∧ b ∈ previous ‘ ⟨kpair.π₁ p, ψ⟩ₖ) ∨
  (∃ φ ψ, kpair.π₂ p = orCode φ ψ ∧
    (b ∈ previous ‘ ⟨kpair.π₁ p, φ⟩ₖ ∨ b ∈ previous ‘ ⟨kpair.π₁ p, ψ⟩ₖ)) ∨
  (∃ φ, kpair.π₂ p = allCode φ ∧ ∀ x ∈ structureDomain M,
    assignmentPrepend (kpair.π₁ p) b x ∈ previous ‘ ⟨succ (kpair.π₁ p), φ⟩ₖ) ∨
  ∃ φ, kpair.π₂ p = existsCode φ ∧ ∃ x ∈ structureDomain M,
    assignmentPrepend (kpair.π₁ p) b x ∈ previous ‘ ⟨succ (kpair.π₁ p), φ⟩ₖ

instance satisfactionStepHolds_definable (L Γ M e : V) :
    ℒₛₑₜ-relation₃ (SatisfactionStepHolds L Γ M e) := by
  unfold SatisfactionStepHolds truthCode
  definability

noncomputable def satisfactionStep (L Γ M e p previous : V) : V :=
  {b ∈ structureDomain M ^ (kpair.π₁ p) ; SatisfactionStepHolds L Γ M e p previous b}

theorem mem_satisfactionStep_iff (L Γ M e p previous b : V) :
    b ∈ satisfactionStep L Γ M e p previous ↔
      b ∈ structureDomain M ^ (kpair.π₁ p) ∧ SatisfactionStepHolds L Γ M e p previous b := by
  simp [satisfactionStep]

instance satisfactionStep_definable (L Γ M e : V) : ℒₛₑₜ-function₂ (satisfactionStep L Γ M e) := by
  have h : ℒₛₑₜ-relation₃ (fun S p previous : V ↦ ∀ b, b ∈ S ↔
      b ∈ structureDomain M ^ (kpair.π₁ p) ∧ SatisfactionStepHolds L Γ M e p previous b) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = satisfactionStep L Γ M e (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_satisfactionStep_iff]

noncomputable def satisfactionGraph (L Γ M e : V) : V :=
  formulaRecursion L Γ (satisfactionStep L Γ M e) inferInstance

instance satisfactionGraph_isFunction (L Γ M e : V) : IsFunction (satisfactionGraph L Γ M e) :=
  formulaRecursion_isFunction _ _ _ _

@[simp] theorem domain_satisfactionGraph (L Γ M e : V) :
    domain (satisfactionGraph L Γ M e) = formulaFamily L Γ := domain_formulaRecursion _ _ _ _

def Satisfies (L Γ M e n φ b : V) : Prop := b ∈ (satisfactionGraph L Γ M e) ‘ ⟨n, φ⟩ₖ

theorem satisfies_iff_step {L Γ M e n φ b : V} (hφ : φ ∈ formulaSet L Γ n) :
    Satisfies L Γ M e n φ b ↔ b ∈ structureDomain M ^ n ∧
      SatisfactionStepHolds L Γ M e ⟨n, φ⟩ₖ ((satisfactionGraph L Γ M e) ↾
        (predecessors (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) ⟨n, φ⟩ₖ)) b := by
  have h := formulaRecursion_value L Γ (satisfactionStep L Γ M e) inferInstance
    ((mem_formulaSet_iff _ _ _ _).mp hφ)
  unfold Satisfies satisfactionGraph
  rw [h, mem_satisfactionStep_iff]
  simp only [kpair.π₁_kpair]

theorem satisfies_assignment_mem {L Γ M e n φ b : V} (hφ : φ ∈ formulaSet L Γ n)
    (h : Satisfies L Γ M e n φ b) : b ∈ structureDomain M ^ n :=
  ((satisfies_iff_step hφ).mp h).1

end ZFVP
