import ZFVP.Syntax.Satisfaction

/-! Constructor equations for the internal satisfaction step. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem satisfactionStepHolds_truth (L Γ M e n previous b : V) :
    SatisfactionStepHolds L Γ M e ⟨n, truthCode⟩ₖ previous b ↔
      True := by
  simp [SatisfactionStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem satisfactionStepHolds_falsity (L Γ M e n previous b : V) :
    SatisfactionStepHolds L Γ M e ⟨n, falsityCode⟩ₖ previous b ↔
      False := by
  simp [SatisfactionStepHolds, truthCode, falsityCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem satisfactionStepHolds_atom (L Γ M e n previous b r args : V) :
    SatisfactionStepHolds L Γ M e ⟨n, atomCode r args⟩ₖ previous b ↔
      AtomicHolds L Γ M e n b r args := by
  simp [SatisfactionStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem satisfactionStepHolds_negAtom (L Γ M e n previous b r args : V) :
    SatisfactionStepHolds L Γ M e ⟨n, negAtomCode r args⟩ₖ previous b ↔
      ¬AtomicHolds L Γ M e n b r args := by
  simp [SatisfactionStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem satisfactionStepHolds_and (L Γ M e n previous b φ ψ : V) :
    SatisfactionStepHolds L Γ M e ⟨n, andCode φ ψ⟩ₖ previous b ↔
      b ∈ previous ‘ ⟨n, φ⟩ₖ ∧ b ∈ previous ‘ ⟨n, ψ⟩ₖ := by
  simp [SatisfactionStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem satisfactionStepHolds_or (L Γ M e n previous b φ ψ : V) :
    SatisfactionStepHolds L Γ M e ⟨n, orCode φ ψ⟩ₖ previous b ↔
      b ∈ previous ‘ ⟨n, φ⟩ₖ ∨ b ∈ previous ‘ ⟨n, ψ⟩ₖ := by
  simp [SatisfactionStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem satisfactionStepHolds_all (L Γ M e n previous b φ : V) :
    SatisfactionStepHolds L Γ M e ⟨n, allCode φ⟩ₖ previous b ↔
      ∀ x ∈ structureDomain M, assignmentPrepend n b x ∈ previous ‘ ⟨succ n, φ⟩ₖ := by
  simp [SatisfactionStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem satisfactionStepHolds_exists (L Γ M e n previous b φ : V) :
    SatisfactionStepHolds L Γ M e ⟨n, existsCode φ⟩ₖ previous b ↔
      ∃ x ∈ structureDomain M, assignmentPrepend n b x ∈ previous ‘ ⟨succ n, φ⟩ₖ := by
  simp [SatisfactionStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

end ZFVP

