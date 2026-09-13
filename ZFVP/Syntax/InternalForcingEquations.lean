import ZFVP.Syntax.InternalForcingStepEquations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalForcing_previous_value {P R D s t : V}
    (ht : t ∈ formulaFamily (membershipLanguageCode : V) ∅) (hst : IsImmediateSubformula s t) :
    ((internalForcingGraph P R D) ↾
      (predecessors (subformulaRelation (formulaFamily (membershipLanguageCode : V) ∅))
        (formulaFamily (membershipLanguageCode : V) ∅) t)) ‘ s = (internalForcingGraph P R D) ‘ s :=
  formulaRecursion_previous_value membershipLanguageCode_valid _ _ ht hst

theorem internalForces_truth {P R D n b p : V} (hn : n ∈ (ω : V)) :
    InternalForces P R D n truthCode b p ↔ b ∈ D ^ n ∧ p ∈ P := by
  rw [internalForces_iff_step (formulaSet_constants membershipLanguageCode_valid hn ∅).1,
    internalForcingStepHolds_truth]
  simp

theorem not_internalForces_falsity {P R D n b p : V} (hn : n ∈ (ω : V)) :
    ¬InternalForces P R D n falsityCode b p := by
  rw [internalForces_iff_step (formulaSet_constants membershipLanguageCode_valid hn ∅).2,
    internalForcingStepHolds_falsity]
  simp

theorem internalForces_atom {P R D n b p r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    InternalForces P R D n (atomCode r args) b p ↔ InternalForcingAtomicHolds P R n b r args p := by
  rw [internalForces_iff_step (formulaSet_atoms membershipLanguageCode_valid hn ha).1,
    internalForcingStepHolds_atom, and_iff_right hb, and_iff_right hp]

theorem internalForces_negAtom {P R D n b p r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    InternalForces P R D n (negAtomCode r args) b p ↔ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ¬InternalForcingAtomicHolds P R n b r args q := by
  rw [internalForces_iff_step (formulaSet_atoms membershipLanguageCode_valid hn ha).2,
    internalForcingStepHolds_negAtom, and_iff_right hb, and_iff_right hp]

theorem internalForces_and {P R D n b p φ ψ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hb : b ∈ D ^ n) (hp : p ∈ P) :
    InternalForces P R D n (andCode φ ψ) b p ↔ InternalForces P R D n φ b p ∧ InternalForces P R D n ψ b p := by
  have hc := (formulaSet_binary membershipLanguageCode_valid hn hφ hψ).1
  have hcf := (mem_formulaSet_iff _ _ _ _).mp hc
  have hsφ : IsImmediateSubformula ⟨n, φ⟩ₖ ⟨n, andCode φ ψ⟩ₖ :=
    Or.inl ⟨n, φ, ψ, Or.inl rfl, Or.inl rfl⟩
  have hsψ : IsImmediateSubformula ⟨n, ψ⟩ₖ ⟨n, andCode φ ψ⟩ₖ :=
    Or.inl ⟨n, φ, ψ, Or.inl rfl, Or.inr rfl⟩
  rw [internalForces_iff_step hc, internalForcingStepHolds_and,
    internalForcing_previous_value hcf hsφ, internalForcing_previous_value hcf hsψ,
    and_iff_right hb, and_iff_right hp]
  rfl

theorem internalForces_or {P R D n b p φ ψ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hb : b ∈ D ^ n) (hp : p ∈ P) :
    InternalForces P R D n (orCode φ ψ) b p ↔ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
      (InternalForces P R D n φ b r ∨ InternalForces P R D n ψ b r) := by
  have hc := (formulaSet_binary membershipLanguageCode_valid hn hφ hψ).2
  have hcf := (mem_formulaSet_iff _ _ _ _).mp hc
  have hsφ : IsImmediateSubformula ⟨n, φ⟩ₖ ⟨n, orCode φ ψ⟩ₖ :=
    Or.inl ⟨n, φ, ψ, Or.inr rfl, Or.inl rfl⟩
  have hsψ : IsImmediateSubformula ⟨n, ψ⟩ₖ ⟨n, orCode φ ψ⟩ₖ :=
    Or.inl ⟨n, φ, ψ, Or.inr rfl, Or.inr rfl⟩
  rw [internalForces_iff_step hc, internalForcingStepHolds_or,
    internalForcing_previous_value hcf hsφ, internalForcing_previous_value hcf hsψ,
    and_iff_right hb, and_iff_right hp]
  rfl

theorem internalForces_all {P R D n b p φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    InternalForces P R D n (allCode φ) b p ↔ ∀ x ∈ D, InternalForces P R D (succ n) φ (assignmentPrepend n b x) p := by
  have hc := (formulaSet_quantifiers membershipLanguageCode_valid hn hφ).1
  have hcf := (mem_formulaSet_iff _ _ _ _).mp hc
  have hs : IsImmediateSubformula ⟨succ n, φ⟩ₖ ⟨n, allCode φ⟩ₖ :=
    Or.inr ⟨n, φ, Or.inl rfl, rfl⟩
  rw [internalForces_iff_step hc, internalForcingStepHolds_all,
    internalForcing_previous_value hcf hs, and_iff_right hb, and_iff_right hp]
  rfl

theorem internalForces_exists {P R D n b p φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    InternalForces P R D n (existsCode φ) b p ↔ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
      ∃ x ∈ D, InternalForces P R D (succ n) φ (assignmentPrepend n b x) r := by
  have hc := (formulaSet_quantifiers membershipLanguageCode_valid hn hφ).2
  have hcf := (mem_formulaSet_iff _ _ _ _).mp hc
  have hs : IsImmediateSubformula ⟨succ n, φ⟩ₖ ⟨n, existsCode φ⟩ₖ :=
    Or.inr ⟨n, φ, Or.inr rfl, rfl⟩
  rw [internalForces_iff_step hc, internalForcingStepHolds_exists,
    internalForcing_previous_value hcf hs, and_iff_right hb, and_iff_right hp]
  rfl

end ZFVP
