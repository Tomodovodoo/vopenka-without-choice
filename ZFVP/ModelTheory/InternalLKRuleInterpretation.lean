import ZFVP.ModelTheory.NaturalSequentQuantifierRules
import ZFVP.Syntax.PrimitiveProgramLKRuleCheck

/-! The explicit local LK program has the stated set-theoretic rule and input checks on all internal values. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def naturalLKInputs (S C φ ψ θ Γ Δ : V) : Prop :=
  naturalSequentFits true 0 C ∧
  (∀ xs ∈ SetTheory.range (decodedNaturalList S), naturalSequentFits true 0 xs) ∧
  requirementFits ((formulaRequirement true).evalSet φ) 0 ∧
  requirementFits ((formulaRequirement true).evalSet ψ) 0 ∧
  requirementFits ((formulaRequirement true).evalSet θ) 1 ∧
  naturalSequentFits true 0 Γ ∧ naturalSequentFits true 0 Δ

def naturalLKRuleCore (S C tag φ ψ θ k Γ Δ : V) : Prop := by
  classical
  exact
    if tag = 0 then C = SetTheory.succ (naturalSquarePair φ (SetTheory.succ (naturalSquarePair (negateCode.evalSet φ) 0))) else
    if tag = 1 then
      listMember.evalSet (naturalSquarePair (SetTheory.succ (naturalSquarePair φ Γ)) S) = 1 ∧
      listMember.evalSet (naturalSquarePair (SetTheory.succ (naturalSquarePair (negateCode.evalSet φ) Δ)) S) = 1 ∧
      C = listAppend.evalSet (naturalSquarePair Δ Γ) else
    if tag = 2 then listMember.evalSet (naturalSquarePair Δ S) = 1 ∧ listSubset.evalSet (naturalSquarePair Δ C) = 1 else
    if tag = 3 then C = SetTheory.succ (naturalSquarePair (SetTheory.succ (naturalSquarePair 2 0)) 0) else
    if tag = 4 then
      listMember.evalSet (naturalSquarePair (SetTheory.succ (naturalSquarePair φ (SetTheory.succ (naturalSquarePair ψ Γ)))) S) = 1 ∧
      C = SetTheory.succ (naturalSquarePair (SetTheory.succ (naturalSquarePair 5 (naturalSquarePair φ ψ))) Γ) else
    if tag = 5 then
      listMember.evalSet (naturalSquarePair (SetTheory.succ (naturalSquarePair φ Γ)) S) = 1 ∧
      listMember.evalSet (naturalSquarePair (SetTheory.succ (naturalSquarePair ψ Γ)) S) = 1 ∧
      C = SetTheory.succ (naturalSquarePair (SetTheory.succ (naturalSquarePair 4 (naturalSquarePair φ ψ))) Γ) else
    if tag = 6 then
      listMember.evalSet (naturalSquarePair (SetTheory.succ (naturalSquarePair
        (proofRewriteCode.evalSet (naturalSquarePair 1 (naturalSquarePair 0 θ)))
        (proofRewriteSequent.evalSet (naturalSquarePair 0 Γ)))) S) = 1 ∧
      C = SetTheory.succ (naturalSquarePair (SetTheory.succ (naturalSquarePair 6 θ)) Γ) else
    if tag = 7 then
      listMember.evalSet (naturalSquarePair (SetTheory.succ (naturalSquarePair
        (proofRewriteCode.evalSet (naturalSquarePair (SetTheory.succ (SetTheory.succ k)) (naturalSquarePair 0 θ))) Γ)) S) = 1 ∧
      C = SetTheory.succ (naturalSquarePair (SetTheory.succ (naturalSquarePair 7 θ)) Γ) else False

theorem arithmeticLKRuleCore_agreement (S C tag φ ψ θ k Γ Δ : InternalArithmetic V) :
    arithmeticLKRuleCore S C tag φ ψ θ k Γ Δ ↔
      naturalLKRuleCore (internalArithmeticVal S) (internalArithmeticVal C) (internalArithmeticVal tag)
        (internalArithmeticVal φ) (internalArithmeticVal ψ) (internalArithmeticVal θ) (internalArithmeticVal k)
        (internalArithmeticVal Γ) (internalArithmeticVal Δ) := by
  have hite (p a b : Prop) [Decidable p] : (if p then a else b) ↔ (p ∧ a) ∨ (¬p ∧ b) := by
    split <;> simp_all
  unfold arithmeticLKRuleCore naturalLKRuleCore
  simp only [hite]
  simp only [internalArithmetic_eq, evalArithmetic_agreement, internalArithmeticVal_succ,
    internalArithmeticVal_pair, internalArithmeticVal_zero, internalArithmeticVal_one]
  simp only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat]

theorem arithmeticLKInputs_agreement (S C φ ψ θ Γ Δ : InternalArithmetic V) :
    arithmeticLKInputs S C φ ψ θ Γ Δ ↔
      naturalLKInputs (internalArithmeticVal S) (internalArithmeticVal C) (internalArithmeticVal φ)
        (internalArithmeticVal ψ) (internalArithmeticVal θ) (internalArithmeticVal Γ) (internalArithmeticVal Δ) := by
  have hF (n c : InternalArithmetic V) :
      (formulaCheck true).evalArithmetic (Arithmetic.pair n c) = 1 ↔
        requirementFits ((formulaRequirement true).evalSet (internalArithmeticVal c)) (internalArithmeticVal n) := by
    have h := evalSet_formulaCheck_eq_one true (internalArithmeticVal_mem n) (internalArithmeticVal_mem c)
    rw [evalSet_pair_val, ← internalArithmeticVal_one, ← internalArithmetic_eq] at h
    exact h
  have hQ (c : InternalArithmetic V) : (sequentCheck true).evalArithmetic (Arithmetic.pair 0 c) = 1 ↔
      naturalSequentFits true 0 (internalArithmeticVal c) := by
    have h := evalSet_sequentCheck_eq_one true (internalArithmeticVal_mem (0 : InternalArithmetic V)) (internalArithmeticVal_mem c)
    rw [evalSet_pair_val, ← internalArithmeticVal_one, ← internalArithmetic_eq, internalArithmeticVal_zero] at h
    exact h
  have hS : (∀ i < listLength.evalArithmetic S,
      (sequentCheck true).evalArithmetic (Arithmetic.pair 0 (listGet.evalArithmetic (Arithmetic.pair S i))) = 1) ↔
      ∀ xs ∈ SetTheory.range (decodedNaturalList (internalArithmeticVal S)), naturalSequentFits true 0 xs := by
    constructor
    · intro h xs hxs
      obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective
        (mem_decodedNaturalList_range_natural (internalArithmeticVal_mem S) hxs)
      obtain ⟨i, hi, he⟩ := (mem_range_decodedNaturalList_val v S).mp hxs
      exact (hQ v).mp (he.symm ▸ h i hi)
    · intro h i hi
      apply (hQ _).mpr
      exact h _ ((mem_range_decodedNaturalList_val (listGet.evalArithmetic (Arithmetic.pair S i)) S).mpr ⟨i, hi, rfl⟩)
  rw [arithmeticLKInputs, naturalLKInputs, hS]
  simp only [hF, hQ, internalArithmeticVal_zero, internalArithmeticVal_one]

theorem evalSet_lkRuleCheck_eq_one {S C tag φ ψ θ k Γ Δ : V}
    (hS : S ∈ (ω : V)) (hC : C ∈ (ω : V)) (ht : tag ∈ (ω : V))
    (hφ : φ ∈ (ω : V)) (hψ : ψ ∈ (ω : V)) (hθ : θ ∈ (ω : V)) (hk : k ∈ (ω : V))
    (hΓ : Γ ∈ (ω : V)) (hΔ : Δ ∈ (ω : V)) :
    lkRuleCheck.evalSet (naturalSquarePair S (naturalSquarePair C (naturalSquarePair tag
      (naturalSquarePair φ (naturalSquarePair ψ (naturalSquarePair θ (naturalSquarePair k (naturalSquarePair Γ Δ)))))))) = 1 ↔
      naturalLKInputs S C φ ψ θ Γ Δ ∧ naturalLKRuleCore S C tag φ ψ θ k Γ Δ := by
  obtain ⟨S₀, rfl⟩ := internalArithmeticVal_surjective hS
  obtain ⟨C₀, rfl⟩ := internalArithmeticVal_surjective hC
  obtain ⟨t₀, rfl⟩ := internalArithmeticVal_surjective ht
  obtain ⟨φ₀, rfl⟩ := internalArithmeticVal_surjective hφ
  obtain ⟨ψ₀, rfl⟩ := internalArithmeticVal_surjective hψ
  obtain ⟨θ₀, rfl⟩ := internalArithmeticVal_surjective hθ
  obtain ⟨k₀, rfl⟩ := internalArithmeticVal_surjective hk
  obtain ⟨Γ₀, rfl⟩ := internalArithmeticVal_surjective hΓ
  obtain ⟨Δ₀, rfl⟩ := internalArithmeticVal_surjective hΔ
  have h := evalArithmetic_lkRuleCheck_eq_one S₀ C₀ t₀ φ₀ ψ₀ θ₀ k₀ Γ₀ Δ₀
  rw [arithmeticLKInputs_agreement, arithmeticLKRuleCore_agreement] at h
  simpa only [internalArithmetic_eq, evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_one] using h

end ZFVP
