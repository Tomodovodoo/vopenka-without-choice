import ZFVP.Syntax.PrimitiveProgramRawFormulas
import ZFVP.Syntax.PrimitiveProgramRawTransform

/-! Total standard decoding for raw formula and sequent codes, with exact list operations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

def rawFormula (n c : ℕ) : Semiproposition ℒₛₑₜ n := (Semiformula.ofNat n c).getD ⊥

theorem RawFormulaCode.decode_raw {n c : ℕ} {φ : Semiproposition ℒₛₑₜ n} (h : RawFormulaCode c φ) :
    rawFormula n c = φ := by simp only [rawFormula, h.ofNat, Option.getD_some]

@[simp] theorem rawFormula_encode {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) :
    rawFormula n (Encodable.encode φ) = φ := (RawFormulaCode.encode φ).decode_raw

theorem rawFormula_code {n c : ℕ} (hv : (formulaCheck true).eval (Nat.pair n c) = 1) :
    RawFormulaCode c (rawFormula n c) := by
  obtain ⟨φ, hφ⟩ := formulaCheck_raw_open hv
  rw [hφ.decode_raw]
  exact hφ

theorem encode_natToList (c : ℕ) : Encodable.encode (Nat.natToList c) = c := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    cases c with
    | zero => simp [Nat.natToList]
    | succ c =>
      rw [Nat.natToList, Encodable.encode_list_cons, Encodable.encode_nat,
        ih c.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le c)), Nat.pair_unpair]

@[simp] theorem natToList_encode (xs : List ℕ) : Nat.natToList (Encodable.encode xs) = xs :=
  Encodable.encode_injective (encode_natToList (Encodable.encode xs))

def rawSequent (c : ℕ) : Sequent ℒₛₑₜ := (Nat.natToList c).map (rawFormula 0)

@[simp] theorem rawSequent_zero : rawSequent 0 = [] := by simp [rawSequent, Nat.natToList]

@[simp] theorem rawSequent_cons (c cs : ℕ) :
    rawSequent (Nat.pair c cs + 1) = rawFormula 0 c :: rawSequent cs := by
  simp [rawSequent, Nat.natToList]

@[simp] theorem rawSequent_encode (Γ : Sequent ℒₛₑₜ) : rawSequent (Encodable.encode Γ) = Γ := by
  rw [← encode_list_map_encode Γ]
  simp [rawSequent, List.map_map, Function.comp_def]

theorem listMember_natToList (c cs : ℕ) :
    listMember.eval (Nat.pair c cs) = 1 ↔ c ∈ Nat.natToList cs := by
  have h := listMember_encode (α := ℕ) c (Nat.natToList cs)
  simpa only [encode_natToList, Encodable.encode_nat] using h

theorem listSubset_natToList (xs ys : ℕ) :
    listSubset.eval (Nat.pair xs ys) = 1 ↔ Nat.natToList xs ⊆ Nat.natToList ys := by
  simpa only [encode_natToList] using listSubset_encode (Nat.natToList xs) (Nat.natToList ys)

theorem listAll_natToList (f : PrimitiveProgram) (z cs : ℕ) :
    (listAll f).eval (Nat.pair z cs) = 1 ↔
      ∀ c ∈ Nat.natToList cs, f.eval (Nat.pair z c) ≠ 0 := by
  simpa only [encode_natToList, Encodable.encode_nat] using listAll_encode_iff f z (Nat.natToList cs)

theorem sequentCheck_natToList (allowFree : Bool) (n cs : ℕ) :
    (sequentCheck allowFree).eval (Nat.pair n cs) = 1 ↔
      ∀ c ∈ Nat.natToList cs, (formulaCheck allowFree).eval (Nat.pair n c) = 1 := by
  rw [sequentCheck, listAll_natToList]
  simp only [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_formulaCheck_eq_one,
    evalArithmetic_formulaCheck_ne_zero]

theorem rawSequent_append (xs ys : ℕ) :
    rawSequent (listAppend.eval (Nat.pair ys xs)) = rawSequent xs ++ rawSequent ys := by
  have h := listAppend_encode (Nat.natToList xs) (Nat.natToList ys)
  simp only [encode_natToList] at h
  simp only [h, rawSequent, natToList_encode, List.map_append]

theorem rawSequent_subset {xs ys : ℕ} (h : listSubset.eval (Nat.pair xs ys) = 1) :
    rawSequent xs ⊆ rawSequent ys := by
  exact List.map_subset _ ((listSubset_natToList xs ys).mp h)

theorem natToList_listMap (f : PrimitiveProgram) (z cs : ℕ) :
    Nat.natToList ((listMap f).eval (Nat.pair z cs)) =
      (Nat.natToList cs).map (fun c ↦ f.eval (Nat.pair z c)) := by
  have h := listMap_encode f (fun c : ℕ ↦ f.eval (Nat.pair z c)) z
    (fun c ↦ by simp only [Encodable.encode_nat]) (Nat.natToList cs)
  simp only [encode_natToList] at h
  rw [h, natToList_encode]

theorem rawSequent_listMap (f : PrimitiveProgram) (z cs : ℕ) :
    rawSequent ((listMap f).eval (Nat.pair z cs)) =
      (Nat.natToList cs).map (fun c ↦ rawFormula 0 (f.eval (Nat.pair z c))) := by
  simp only [rawSequent, natToList_listMap, List.map_map]
  rfl

end ZFVP
