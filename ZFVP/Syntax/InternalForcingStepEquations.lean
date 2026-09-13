import ZFVP.Syntax.InternalForcingSatisfaction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalForcingStepHolds_truth (P R D n previous b p : V) :
    InternalForcingStepHolds P R D ⟨n, truthCode⟩ₖ previous b p ↔
      True := by
  simp [InternalForcingStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem internalForcingStepHolds_falsity (P R D n previous b p : V) :
    InternalForcingStepHolds P R D ⟨n, falsityCode⟩ₖ previous b p ↔
      False := by
  simp [InternalForcingStepHolds, truthCode, falsityCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem internalForcingStepHolds_atom (P R D n previous b p r args : V) :
    InternalForcingStepHolds P R D ⟨n, atomCode r args⟩ₖ previous b p ↔
      InternalForcingAtomicHolds P R n b r args p := by
  simp [InternalForcingStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem internalForcingStepHolds_negAtom (P R D n previous b p r args : V) :
    InternalForcingStepHolds P R D ⟨n, negAtomCode r args⟩ₖ previous b p ↔
      ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ¬InternalForcingAtomicHolds P R n b r args q := by
  simp [InternalForcingStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem internalForcingStepHolds_and (P R D n previous b p φ ψ : V) :
    InternalForcingStepHolds P R D ⟨n, andCode φ ψ⟩ₖ previous b p ↔
      ⟨b, p⟩ₖ ∈ previous ‘ ⟨n, φ⟩ₖ ∧ ⟨b, p⟩ₖ ∈ previous ‘ ⟨n, ψ⟩ₖ := by
  simp [InternalForcingStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem internalForcingStepHolds_or (P R D n previous b p φ ψ : V) :
    InternalForcingStepHolds P R D ⟨n, orCode φ ψ⟩ₖ previous b p ↔
      ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
      (⟨b, r⟩ₖ ∈ previous ‘ ⟨n, φ⟩ₖ ∨ ⟨b, r⟩ₖ ∈ previous ‘ ⟨n, ψ⟩ₖ) := by
  simp [InternalForcingStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem internalForcingStepHolds_all (P R D n previous b p φ : V) :
    InternalForcingStepHolds P R D ⟨n, allCode φ⟩ₖ previous b p ↔
      ∀ x ∈ D, ⟨assignmentPrepend n b x, p⟩ₖ ∈ previous ‘ ⟨succ n, φ⟩ₖ := by
  simp [InternalForcingStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem internalForcingStepHolds_exists (P R D n previous b p φ : V) :
    InternalForcingStepHolds P R D ⟨n, existsCode φ⟩ₖ previous b p ↔
      ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
      ∃ x ∈ D, ⟨assignmentPrepend n b x, r⟩ₖ ∈ previous ‘ ⟨succ n, φ⟩ₖ := by
  simp [InternalForcingStepHolds, truthCode, atomCode, negAtomCode,
    andCode, orCode, allCode, existsCode, OfNat.ofNat, internalNumeral_eq_iff]

end ZFVP
