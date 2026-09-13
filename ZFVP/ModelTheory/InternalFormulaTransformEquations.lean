import ZFVP.ModelTheory.InternalNegationProgramEquations
import ZFVP.Syntax.PrimitiveProgramFormulaTransformEquations

/-! The common formula transformer satisfies its equations on every internal natural input. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem evalSet_formulaTransformCode_rel (arguments : PrimitiveProgram) {s d k r v : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hv : v ∈ (ω : V)) :
    (formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 0 (naturalSquarePair k (naturalSquarePair r v)))))) =
      SetTheory.succ (naturalSquarePair 0 (naturalSquarePair 2 (naturalSquarePair r (arguments.evalSet (naturalSquarePair s (naturalSquarePair d v)))))) := by
  obtain ⟨s₀, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨k₀, rfl⟩ := internalArithmeticVal_surjective hk
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨v₀, rfl⟩ := internalArithmeticVal_surjective hv
  have h := congrArg internalArithmeticVal (evalArithmetic_formulaTransformCode_rel arguments s₀ d₀ (Arithmetic.pair k₀ (Arithmetic.pair r₀ v₀)))
  simp only [Arithmetic.pi₁_pair, Arithmetic.pi₂_pair] at h
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_formulaTransformCode_nrel (arguments : PrimitiveProgram) {s d k r v : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hv : v ∈ (ω : V)) :
    (formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 1 (naturalSquarePair k (naturalSquarePair r v)))))) =
      SetTheory.succ (naturalSquarePair 1 (naturalSquarePair 2 (naturalSquarePair r (arguments.evalSet (naturalSquarePair s (naturalSquarePair d v)))))) := by
  obtain ⟨s₀, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨k₀, rfl⟩ := internalArithmeticVal_surjective hk
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨v₀, rfl⟩ := internalArithmeticVal_surjective hv
  have h := congrArg internalArithmeticVal (evalArithmetic_formulaTransformCode_nrel arguments s₀ d₀ (Arithmetic.pair k₀ (Arithmetic.pair r₀ v₀)))
  simp only [Arithmetic.pi₁_pair, Arithmetic.pi₂_pair] at h
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_one] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_formulaTransformCode_verum (arguments : PrimitiveProgram) {s d c : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    (formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 2 c)))) =
      SetTheory.succ (naturalSquarePair 2 0) := by
  obtain ⟨s₀, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨c₀, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_formulaTransformCode_verum arguments s₀ d₀ c₀)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_formulaTransformCode_falsum (arguments : PrimitiveProgram) {s d c : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    (formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 3 c)))) =
      SetTheory.succ (naturalSquarePair 3 0) := by
  obtain ⟨s₀, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨c₀, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_formulaTransformCode_falsum arguments s₀ d₀ c₀)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_formulaTransformCode_and (arguments : PrimitiveProgram) {s d a b : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    (formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 4 (naturalSquarePair a b))))) =
      SetTheory.succ (naturalSquarePair 4 (naturalSquarePair ((formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d a))) ((formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d b))))) := by
  obtain ⟨s₀, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨a₀, rfl⟩ := internalArithmeticVal_surjective ha
  obtain ⟨b₀, rfl⟩ := internalArithmeticVal_surjective hb
  have h := congrArg internalArithmeticVal (evalArithmetic_formulaTransformCode_and arguments s₀ d₀ a₀ b₀)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_formulaTransformCode_or (arguments : PrimitiveProgram) {s d a b : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    (formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 5 (naturalSquarePair a b))))) =
      SetTheory.succ (naturalSquarePair 5 (naturalSquarePair ((formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d a))) ((formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d b))))) := by
  obtain ⟨s₀, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨a₀, rfl⟩ := internalArithmeticVal_surjective ha
  obtain ⟨b₀, rfl⟩ := internalArithmeticVal_surjective hb
  have h := congrArg internalArithmeticVal (evalArithmetic_formulaTransformCode_or arguments s₀ d₀ a₀ b₀)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_formulaTransformCode_all (arguments : PrimitiveProgram) {s d a : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (ha : a ∈ (ω : V)) :
    (formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 6 a)))) =
      SetTheory.succ (naturalSquarePair 6 ((formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair (SetTheory.succ d) a)))) := by
  obtain ⟨s₀, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨a₀, rfl⟩ := internalArithmeticVal_surjective ha
  have h := congrArg internalArithmeticVal (evalArithmetic_formulaTransformCode_all arguments s₀ d₀ a₀)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_formulaTransformCode_exs (arguments : PrimitiveProgram) {s d a : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (ha : a ∈ (ω : V)) :
    (formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d (SetTheory.succ (naturalSquarePair 7 a)))) =
      SetTheory.succ (naturalSquarePair 7 ((formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair (SetTheory.succ d) a)))) := by
  obtain ⟨s₀, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨a₀, rfl⟩ := internalArithmeticVal_surjective ha
  have h := congrArg internalArithmeticVal (evalArithmetic_formulaTransformCode_exs arguments s₀ d₀ a₀)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

end ZFVP

