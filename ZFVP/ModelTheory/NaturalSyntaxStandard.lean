import ZFVP.ModelTheory.NaturalFormulaDecoderEquations
import ZFVP.Syntax.MembershipSatisfaction
import Foundation.FirstOrder.Basic.Coding

/-! The uniform natural syntax decoder agrees with Foundation's finite membership syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem naturalCons_natCast (x y : ℕ) :
    SetTheory.succ (naturalSquarePair (x : V) (y : V)) = ((Nat.pair x y + 1 : ℕ) : V) := by
  rw [naturalSquarePair_natCast, ← num_succ_def]

@[simp] theorem decodedNaturalTerm_encode {ξ : Type*} [Encodable ξ] {n : ℕ}
    (t : Semiterm ℒₛₑₜ ξ n) :
    decodedNaturalTerm (Encodable.encode t : V) =
      encodeSemiterm (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k))
        (fun x ↦ (Encodable.encode x : V)) t := by
  cases t with
  | bvar i =>
    change decodedNaturalTerm ((Nat.pair 0 i.val + 1 : ℕ) : V) = boundVarCode (i.val : V)
    rw [← naturalCons_natCast]
    exact decodedNaturalTerm_bound (by simp)
  | fvar x =>
    change decodedNaturalTerm ((Nat.pair 1 (Encodable.encode x) + 1 : ℕ) : V) =
      freeVarCode (Encodable.encode x : V)
    rw [← naturalCons_natCast]
    exact decodedNaturalTerm_free (by simp)
  | func f _ => exact Empty.elim f

theorem decodedNaturalArguments_vec (v : Fin 2 → ℕ) :
    decodedNaturalArguments (Matrix.vecToNat v : V) =
      standardTuple (fun i ↦ decodedNaturalTerm (v i : V)) := by
  have hv : Matrix.vecToNat v = Nat.pair (v 0) (Nat.pair (v 1) 0 + 1) + 1 := rfl
  rw [hv]
  unfold decodedNaturalArguments
  simp only [← naturalCons_natCast]
  rw [evalSet_listHead_cons (by simp) (ω_succ_closed (naturalSquarePair_natural (by simp) (by simp))),
    evalSet_listTail_cons (by simp) (ω_succ_closed (naturalSquarePair_natural (by simp) (by simp))),
    evalSet_listHead_cons (by simp) (by simp)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem decodedNaturalArguments_encode {ξ : Type*} [Encodable ξ] {n : ℕ}
    (ts : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    decodedNaturalArguments (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)) : V) =
      standardTuple (fun i ↦ encodeSemiterm
        (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k))
        (fun x ↦ (Encodable.encode x : V)) (ts i)) := by
  rw [decodedNaturalArguments_vec]
  simp only [decodedNaturalTerm_encode]

@[simp] theorem naturalSquareLeft_natCast (n : ℕ) :
    naturalSquareLeft (n : V) = (n.unpair.1 : V) := by
  simp [naturalSquareLeft, naturalSquareUnpair_natCast]

@[simp] theorem naturalSquareRight_natCast (n : ℕ) :
    naturalSquareRight (n : V) = (n.unpair.2 : V) := by
  simp [naturalSquareRight, naturalSquareUnpair_natCast]

@[simp] theorem membershipSymbol_encode {k : ℕ} (r : Language.Set.Rel k) :
    (Encodable.encode r : V) = membershipSymbol r := by
  cases r <;> rfl

@[simp] theorem decodedNaturalFormula_encode {ξ : Type*} [Encodable ξ] {n : ℕ}
    (φ : Semiformula ℒₛₑₜ ξ n) :
    decodedNaturalFormula (Encodable.encode φ : V) =
      encodeSemiformula (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k))
        membershipSymbol (fun x ↦ (Encodable.encode x : V)) φ := by
  induction φ with
  | verum =>
    change decodedNaturalFormula ((Nat.pair 2 0 + 1 : ℕ) : V) = truthCode
    rw [← naturalCons_natCast]
    exact decodedNaturalFormula_verum (by simp)
  | falsum =>
    change decodedNaturalFormula ((Nat.pair 3 0 + 1 : ℕ) : V) = falsityCode
    rw [← naturalCons_natCast]
    exact decodedNaturalFormula_falsum (by simp)
  | rel r ts =>
    rw [Semiformula.encode_rel, ← naturalCons_natCast, cast_zero_def, decodedNaturalFormula_rel (by simp)]
    cases r <;>
      simp only [naturalSquareRight_natCast, naturalSquareLeft_natCast, Nat.unpair_pair,
        decodedNaturalArguments_encode, membershipSymbol_encode, encodeSemiformula]
  | nrel r ts =>
    rw [Semiformula.encode_nrel, ← naturalCons_natCast, cast_one_def, decodedNaturalFormula_nrel (by simp)]
    cases r <;>
      simp only [naturalSquareRight_natCast, naturalSquareLeft_natCast, Nat.unpair_pair,
        decodedNaturalArguments_encode, membershipSymbol_encode, encodeSemiformula]
  | and φ ψ ihφ ihψ =>
    change decodedNaturalFormula ((Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1 : ℕ) : V) = _
    rw [← naturalCons_natCast, ← naturalSquarePair_natCast,
      show ((4 : ℕ) : V) = (4 : V) from rfl, decodedNaturalFormula_and (by simp) (by simp)]
    exact congrArg₂ andCode ihφ ihψ
  | or φ ψ ihφ ihψ =>
    change decodedNaturalFormula ((Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1 : ℕ) : V) = _
    rw [← naturalCons_natCast, ← naturalSquarePair_natCast,
      show ((5 : ℕ) : V) = (5 : V) from rfl, decodedNaturalFormula_or (by simp) (by simp)]
    exact congrArg₂ orCode ihφ ihψ
  | all φ ih =>
    change decodedNaturalFormula ((Nat.pair 6 (Encodable.encode φ) + 1 : ℕ) : V) = _
    rw [← naturalCons_natCast]
    rw [show ((6 : ℕ) : V) = (6 : V) from rfl, decodedNaturalFormula_all (by simp)]
    exact congrArg allCode ih
  | exs φ ih =>
    change decodedNaturalFormula ((Nat.pair 7 (Encodable.encode φ) + 1 : ℕ) : V) = _
    rw [← naturalCons_natCast]
    rw [show ((7 : ℕ) : V) = (7 : V) from rfl, decodedNaturalFormula_exs (by simp)]
    exact congrArg existsCode ih

@[simp] theorem decodedNaturalFormula_membership {n : ℕ} (φ : SetTheorySemisentence n) :
    decodedNaturalFormula (Encodable.encode φ : V) = encodeMembershipFormula φ := by
  rw [decodedNaturalFormula_encode]
  unfold encodeMembershipFormula
  congr 1
  funext x
  exact Empty.elim x
end ZFVP