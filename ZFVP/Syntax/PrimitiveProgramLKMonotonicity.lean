import ZFVP.Syntax.PrimitiveProgramLKCertificate
import ZFVP.Syntax.PrimitiveProgramListMemberEquations

/-! Syntax validity of sequent lists and monotonicity of checked LK rules. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem arithmeticPair_cases (c : M) : ∃ a b, c = Arithmetic.pair a b :=
  ⟨Arithmetic.pi₁ c, Arithmetic.pi₂ c, (Arithmetic.pair_unpair c).symm⟩

def arithmeticLKSequentsValid (S : M) : Prop :=
  ∀ i < listLength.evalArithmetic S,
    (sequentCheck true).evalArithmetic (Arithmetic.pair 0 (listGet.evalArithmetic (Arithmetic.pair S i))) = 1

instance arithmeticLKSequentsValid_definable : 𝚺₁-Predicate (arithmeticLKSequentsValid : M → Prop) := by
  unfold arithmeticLKSequentsValid
  definability

theorem arithmeticLKSequentsValid_iff (S : M) :
    arithmeticLKSequentsValid S ↔ ∀ C, listMember.evalArithmetic (Arithmetic.pair C S) = 1 →
      (sequentCheck true).evalArithmetic (Arithmetic.pair 0 C) = 1 := by
  constructor
  · intro h C hc
    obtain ⟨i, hi, he⟩ := (evalArithmetic_listMember_eq_one C S).mp hc
    rw [he]
    exact h i hi
  · intro h i hi
    exact h _ ((evalArithmetic_listMember_eq_one _ S).mpr ⟨i, hi, rfl⟩)

@[simp] theorem arithmeticLKSequentsValid_zero : arithmeticLKSequentsValid (0 : M) := by
  simp [arithmeticLKSequentsValid]

theorem arithmeticLKSequentsValid_cons (C S : M) :
    arithmeticLKSequentsValid (Arithmetic.pair C S + 1) ↔
      (sequentCheck true).evalArithmetic (Arithmetic.pair 0 C) = 1 ∧ arithmeticLKSequentsValid S := by
  simp only [arithmeticLKSequentsValid_iff, evalArithmetic_listMember_cons_iff]
  constructor
  · intro h
    exact ⟨h C (Or.inl rfl), fun D hd ↦ h D (Or.inr hd)⟩
  · rintro ⟨hC, hS⟩ D (he | hd)
    · exact he ▸ hC
    · exact hS D hd

theorem arithmeticLKSequentsValid_append (S T : M) :
    arithmeticLKSequentsValid (listAppend.evalArithmetic (Arithmetic.pair T S)) ↔
      arithmeticLKSequentsValid S ∧ arithmeticLKSequentsValid T := by
  simp only [arithmeticLKSequentsValid_iff, evalArithmetic_listMember_append_iff]
  constructor
  · intro h
    exact ⟨fun C hc ↦ h C (Or.inl hc), fun C hc ↦ h C (Or.inr hc)⟩
  · rintro ⟨hS, hT⟩ C (hc | hc)
    · exact hS C hc
    · exact hT C hc

theorem arithmeticLKRuleCore_mono {S T C tag φ ψ θ k Γ Δ : M}
    (hmem : ∀ x, listMember.evalArithmetic (Arithmetic.pair x S) = 1 →
      listMember.evalArithmetic (Arithmetic.pair x T) = 1)
    (h : arithmeticLKRuleCore S C tag φ ψ θ k Γ Δ) : arithmeticLKRuleCore T C tag φ ψ θ k Γ Δ := by
  unfold arithmeticLKRuleCore at h ⊢
  split_ifs at h ⊢ <;> aesop

theorem lkRuleCheck_mono {S T C w : M}
    (hmem : ∀ x, listMember.evalArithmetic (Arithmetic.pair x S) = 1 →
      listMember.evalArithmetic (Arithmetic.pair x T) = 1)
    (hT : arithmeticLKSequentsValid T)
    (h : lkRuleCheck.evalArithmetic (Arithmetic.pair S (Arithmetic.pair C w)) = 1) :
    lkRuleCheck.evalArithmetic (Arithmetic.pair T (Arithmetic.pair C w)) = 1 := by
  obtain ⟨tag, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨φ, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨ψ, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨θ, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨k, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨Γ, Δ, rfl⟩ := arithmeticPair_cases w
  rw [evalArithmetic_lkRuleCheck_eq_one] at h ⊢
  exact ⟨⟨h.1.1, hT, h.1.2.2⟩, arithmeticLKRuleCore_mono hmem h.2⟩

theorem lkRuleCheck_conclusion {S C w : M}
    (h : lkRuleCheck.evalArithmetic (Arithmetic.pair S (Arithmetic.pair C w)) = 1) :
    (sequentCheck true).evalArithmetic (Arithmetic.pair 0 C) = 1 := by
  obtain ⟨tag, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨φ, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨ψ, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨θ, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨k, w, rfl⟩ := arithmeticPair_cases w
  obtain ⟨Γ, Δ, rfl⟩ := arithmeticPair_cases w
  exact ((evalArithmetic_lkRuleCheck_eq_one S C tag φ ψ θ k Γ Δ).mp h).1.1

end PrimitiveProgram
end ZFVP
