import ZFVP.Syntax.FormulaCases

/-! Constructor inversion for internal formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem numericTag_pair_eq_iff (i j : ℕ) (x y : V) :
    ⟨(i : V), x⟩ₖ = ⟨(j : V), y⟩ₖ ↔ i = j ∧ x = y := by
  simp only [kpair_iff, natCast_eq_iff]

theorem internalNumeral_eq_iff (i j : ℕ) : (SetTheory.ofNat i : V) = SetTheory.ofNat j ↔ i = j :=
  natCast_eq_iff i j

theorem allCode_mem_iff {L Γ n φ : V} (hL : IsLanguageCode L) :
    allCode φ ∈ formulaSet L Γ n ↔ n ∈ (ω : V) ∧ φ ∈ formulaSet L Γ (succ n) := by
  rw [mem_formulaSet_iff_constructor hL]
  simp [IsFormulaConstructor, allCode, existsCode, truthCode, falsityCode,
    atomCode, negAtomCode, andCode, orCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem existsCode_mem_iff {L Γ n φ : V} (hL : IsLanguageCode L) :
    existsCode φ ∈ formulaSet L Γ n ↔ n ∈ (ω : V) ∧ φ ∈ formulaSet L Γ (succ n) := by
  rw [mem_formulaSet_iff_constructor hL]
  simp [IsFormulaConstructor, allCode, existsCode, truthCode, falsityCode,
    atomCode, negAtomCode, andCode, orCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem andCode_mem_iff {L Γ n φ ψ : V} (hL : IsLanguageCode L) :
    andCode φ ψ ∈ formulaSet L Γ n ↔
      n ∈ (ω : V) ∧ φ ∈ formulaSet L Γ n ∧ ψ ∈ formulaSet L Γ n := by
  rw [mem_formulaSet_iff_constructor hL]
  simp [IsFormulaConstructor, allCode, existsCode, truthCode, falsityCode,
    atomCode, negAtomCode, andCode, orCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem orCode_mem_iff {L Γ n φ ψ : V} (hL : IsLanguageCode L) :
    orCode φ ψ ∈ formulaSet L Γ n ↔
      n ∈ (ω : V) ∧ φ ∈ formulaSet L Γ n ∧ ψ ∈ formulaSet L Γ n := by
  rw [mem_formulaSet_iff_constructor hL]
  simp [IsFormulaConstructor, allCode, existsCode, truthCode, falsityCode,
    atomCode, negAtomCode, andCode, orCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem atomCode_mem_iff {L Γ n r args : V} (hL : IsLanguageCode L) :
    atomCode r args ∈ formulaSet L Γ n ↔ n ∈ (ω : V) ∧ IsAtomicArguments L Γ n r args := by
  rw [mem_formulaSet_iff_constructor hL]
  simp [IsFormulaConstructor, allCode, existsCode, truthCode, falsityCode,
    atomCode, negAtomCode, andCode, orCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem negAtomCode_mem_iff {L Γ n r args : V} (hL : IsLanguageCode L) :
    negAtomCode r args ∈ formulaSet L Γ n ↔ n ∈ (ω : V) ∧ IsAtomicArguments L Γ n r args := by
  rw [mem_formulaSet_iff_constructor hL]
  simp [IsFormulaConstructor, allCode, existsCode, truthCode, falsityCode,
    atomCode, negAtomCode, andCode, orCode, OfNat.ofNat, internalNumeral_eq_iff]

end ZFVP





