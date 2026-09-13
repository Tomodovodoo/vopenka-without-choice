import ZFVP.Syntax.PrimitiveProgramGeneratedStandard
import ZFVP.SetTheory.BoundedNaturals

/-! Relational numerals and an explicit program for substituting a numeral into a sentence. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def numeralSuccessorTemplate : MembershipTemplate 1 1 :=
  .exs (.conj (.fixed “y x. y ∈ x”)
    (.conj (.hole ![0]) (.fixed “y x. !boundedSuccFormula x y”)))

def iterateUnaryTemplate (t : MembershipTemplate 1 1) (φ : SetTheorySemisentence 1) :
    ℕ → SetTheorySemisentence 1
  | 0 => φ
  | n + 1 => t.instantiate (iterateUnaryTemplate t φ n)

def quoteNumeralFormula (n : ℕ) : SetTheorySemisentence 1 :=
  iterateUnaryTemplate numeralSuccessorTemplate boundedEmptyFormula n

def setNumeralSubstitution (θ : SetTheorySemisentence 1) (n : ℕ) : SetTheorySentence :=
  ∃¹ (quoteNumeralFormula n ⋏ θ)

namespace PrimitiveProgram

def unaryTemplateIter (t : MembershipTemplate 1 1) (φ : SetTheorySemisentence 1) : PrimitiveProgram :=
  .prec (constant (Encodable.encode φ))
    (.comp t.compileTailProgram (.pair .zero (.comp .right .right)))

def quoteNumeralIter : PrimitiveProgram := unaryTemplateIter numeralSuccessorTemplate boundedEmptyFormula

def quoteNumeralCode : PrimitiveProgram := .comp quoteNumeralIter (.pair .zero identity)

/-- The two input components are the unary formula code and the numeral value. -/
def setNumeralSubstitutionCode : PrimitiveProgram :=
  tagged 7 (tagged 4 (.pair (.comp quoteNumeralCode .right) .left))

def setDiagonalCode : PrimitiveProgram := .comp setNumeralSubstitutionCode (.pair identity identity)

@[simp] theorem evalNat_prec_zero (a b : PrimitiveProgram) (z : ℕ) :
    (prec a b).eval (Nat.pair z 0) = a.eval z := by
  simp only [eval, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero]

@[simp] theorem evalNat_prec_succ (a b : PrimitiveProgram) (z n : ℕ) :
    (prec a b).eval (Nat.pair z (n + 1)) =
      b.eval (Nat.pair z (Nat.pair n ((prec a b).eval (Nat.pair z n)))) := by
  simp only [eval, Nat.unpaired, Nat.unpair_pair]

theorem unaryTemplateIter_encode (t : MembershipTemplate 1 1) (φ : SetTheorySemisentence 1) (z n : ℕ) :
    (unaryTemplateIter t φ).eval (Nat.pair z n) = Encodable.encode (iterateUnaryTemplate t φ n) := by
  induction n with
  | zero => simp [unaryTemplateIter, iterateUnaryTemplate]
  | succ n ih =>
    rw [unaryTemplateIter, evalNat_prec_succ]
    simp only [evalNat_comp, evalNat_pair, evalNat_zero, evalNat_right, Nat.unpair_pair]
    change t.compileTailProgram.eval (Nat.pair 0 ((unaryTemplateIter t φ).eval (Nat.pair z n))) = _
    rw [ih, MembershipTemplate.compileTailProgram_zero_encode]
    rfl

theorem quoteNumeralIter_encode (z n : ℕ) :
    quoteNumeralIter.eval (Nat.pair z n) = Encodable.encode (quoteNumeralFormula n) :=
  unaryTemplateIter_encode numeralSuccessorTemplate boundedEmptyFormula z n

@[simp] theorem quoteNumeralCode_encode (n : ℕ) :
    quoteNumeralCode.eval n = Encodable.encode (quoteNumeralFormula n) := by
  simp only [quoteNumeralCode, evalNat_comp, evalNat_pair, evalNat_zero, evalNat_identity,
    quoteNumeralIter_encode]

theorem setNumeralSubstitutionCode_encode (θ : SetTheorySemisentence 1) (n : ℕ) :
    setNumeralSubstitutionCode.eval (Nat.pair (Encodable.encode θ) n) =
      Encodable.encode (setNumeralSubstitution θ n) := by
  simp only [setNumeralSubstitutionCode, evalNat_tagged, evalNat_pair, evalNat_comp,
    evalNat_right, evalNat_left, Nat.unpair_pair, quoteNumeralCode_encode]
  rfl

theorem setDiagonalCode_encode (θ : SetTheorySemisentence 1) :
    setDiagonalCode.eval (Encodable.encode θ) =
      Encodable.encode (setNumeralSubstitution θ (Encodable.encode θ)) := by
  simp only [setDiagonalCode, evalNat_comp, evalNat_pair, evalNat_identity,
    setNumeralSubstitutionCode_encode]

end PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_quoteNumeralFormula (n : ℕ) (v : Fin 1 → V) :
    (quoteNumeralFormula n).Evalb v ↔ v 0 = (n : V) := by
  induction n generalizing v with
  | zero => simp [quoteNumeralFormula, iterateUnaryTemplate, zero_def]
  | succ n ih =>
    change (numeralSuccessorTemplate.instantiate (quoteNumeralFormula n)).Evalb v ↔ _
    rw [MembershipTemplate.eval_instantiate]
    simp [numeralSuccessorTemplate, MembershipTemplate.Eval, ih, num_succ_def]
    intro h
    rw [h]
    simp

theorem eval_setNumeralSubstitution (θ : SetTheorySemisentence 1) (n : ℕ) :
    V↓[ℒₛₑₜ] ⊧ setNumeralSubstitution θ n ↔ θ.Evalb ![(n : V)] := by
  change (∃ x : V, (quoteNumeralFormula n).Evalb ![x] ∧ θ.Evalb ![x]) ↔ _
  simp only [eval_quoteNumeralFormula, Matrix.cons_val_zero, exists_eq_left]

end ZFVP
