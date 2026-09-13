import ZFVP.Syntax.MembershipPrimcoding

/-! Primitive recursive negation on the natural-number formula encoding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def negateNatFormula : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
    let t := e.unpair.1
    let c := e.unpair.2
    if t = 0 then Nat.pair 1 c + 1
    else if t = 1 then Nat.pair 0 c + 1
    else if t = 2 then Nat.pair 3 0 + 1
    else if t = 3 then Nat.pair 2 0 + 1
    else if t = 4 then
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _))
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))
      Nat.pair 5 (Nat.pair (negateNatFormula c.unpair.1) (negateNatFormula c.unpair.2)) + 1
    else if t = 5 then
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _))
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))
      Nat.pair 4 (Nat.pair (negateNatFormula c.unpair.1) (negateNatFormula c.unpair.2)) + 1
    else if t = 6 then
      have : c < e + 1 := Nat.lt_succ_iff.mpr (Nat.unpair_right_le _)
      Nat.pair 7 (negateNatFormula c) + 1
    else if t = 7 then
      have : c < e + 1 := Nat.lt_succ_iff.mpr (Nat.unpair_right_le _)
      Nat.pair 6 (negateNatFormula c) + 1
    else 0

theorem negateNatFormula_encode {ξ : Type*} [Encodable ξ] {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) :
    negateNatFormula (Encodable.encode φ) = Encodable.encode (∼φ) := by
  induction φ with
  | verum => change negateNatFormula (Nat.pair 2 0 + 1) = Nat.pair 3 0 + 1; simp [negateNatFormula]
  | falsum => change negateNatFormula (Nat.pair 3 0 + 1) = Nat.pair 2 0 + 1; simp [negateNatFormula]
  | rel r ts => simp [Semiformula.encode_rel, Semiformula.encode_nrel, negateNatFormula]
  | nrel r ts => simp [Semiformula.encode_rel, Semiformula.encode_nrel, negateNatFormula]
  | and φ ψ ihφ ihψ =>
    change negateNatFormula (Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) =
      Nat.pair 5 (Nat.pair (Encodable.encode (∼φ)) (Encodable.encode (∼ψ))) + 1
    simp [negateNatFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    change negateNatFormula (Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) =
      Nat.pair 4 (Nat.pair (Encodable.encode (∼φ)) (Encodable.encode (∼ψ))) + 1
    simp [negateNatFormula, ihφ, ihψ]
  | all φ ih =>
    change negateNatFormula (Nat.pair 6 (Encodable.encode φ) + 1) = Nat.pair 7 (Encodable.encode (∼φ)) + 1
    simp [negateNatFormula, ih]
  | exs φ ih =>
    change negateNatFormula (Nat.pair 7 (Encodable.encode φ) + 1) = Nat.pair 6 (Encodable.encode (∼φ)) + 1
    simp [negateNatFormula, ih]

def negateNatFormulaStep (e : ℕ) (T : List ℕ) : ℕ :=
  let t := (e - 1).unpair.1
  let c := (e - 1).unpair.2
  if e = 0 then 0
  else if t = 0 then Nat.pair 1 c + 1
  else if t = 1 then Nat.pair 0 c + 1
  else if t = 2 then Nat.pair 3 0 + 1
  else if t = 3 then Nat.pair 2 0 + 1
  else if t = 4 then Nat.pair 5 (Nat.pair (T.getD c.unpair.1 0) (T.getD c.unpair.2 0)) + 1
  else if t = 5 then Nat.pair 4 (Nat.pair (T.getD c.unpair.1 0) (T.getD c.unpair.2 0)) + 1
  else if t = 6 then Nat.pair 7 (T.getD c 0) + 1
  else if t = 7 then Nat.pair 6 (T.getD c 0) + 1
  else 0

theorem negateNatFormulaStep_primrec : Primrec₂ negateNatFormulaStep := by
  have ht : Primrec (fun p : ℕ × List ℕ ↦ (p.1 - 1).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)))
  have hc : Primrec (fun p : ℕ × List ℕ ↦ (p.1 - 1).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)))
  have hleft := (Primrec.list_getD 0).comp Primrec.snd (Primrec.fst.comp (Primrec.unpair.comp hc))
  have hright := (Primrec.list_getD 0).comp Primrec.snd (Primrec.snd.comp (Primrec.unpair.comp hc))
  have hun := (Primrec.list_getD 0).comp Primrec.snd hc
  have hbin := Primrec₂.natPair.comp hleft hright
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hc))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) hc))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) (Primrec.const (Nat.pair 3 0 + 1))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) (Primrec.const (Nat.pair 2 0 + 1))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 4)) (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 5) hbin))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 5)) (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 4) hbin))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 6)) (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 7) hun))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 7)) (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 6) hun))
      (Primrec.const 0)))))))))

theorem negateNatFormulaStep_table (e : ℕ) :
    negateNatFormulaStep e ((List.range e).map negateNatFormula) = negateNatFormula e := by
  have hget {e j : ℕ} (h : j < e) : ((List.range e).map negateNatFormula).getD j 0 = negateNatFormula j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
    rfl
  cases e with
  | zero => simp [negateNatFormulaStep, negateNatFormula]
  | succ e =>
    have h1 : e.unpair.2.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _))
    have h2 : e.unpair.2.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))
    have hc : e.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr (Nat.unpair_right_le _)
    simp only [negateNatFormulaStep, negateNatFormula, Nat.add_sub_cancel, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte, hget h1, hget h2, hget hc]

theorem negateNatFormula_primrec : Primrec negateNatFormula := by
  have h : Primrec₂ (fun (_ : ℕ) e ↦ negateNatFormula e) :=
    Primrec.nat_strong_rec _ (g := fun (_ : ℕ) T ↦ some (negateNatFormulaStep T.length T))
      (Primrec.option_some.comp (negateNatFormulaStep_primrec.comp
        (Primrec.list_length.comp Primrec.snd) Primrec.snd))
      (fun _ e ↦ by simpa using congrArg some (negateNatFormulaStep_table e))
  exact h.comp (Primrec.const 0) Primrec.id

theorem membershipFormula_neg_primrec (n : ℕ) : Primrec (fun φ : SetTheorySemisentence n ↦ ∼φ) :=
  Primrec.encode_iff.mp ((negateNatFormula_primrec.comp Primrec.encode).of_eq negateNatFormula_encode)

end ZFVP
