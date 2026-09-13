import ZFVP.Syntax.NaturalProofRewriting

/-! Primitive recursion for the natural-code LK rewriting operations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Primrec

theorem proofRewNatTerm_primrec :
    Primrec (fun p : ℕ × (ℕ × ℕ) ↦ proofRewNatTerm p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ p.2.1) := fst.comp snd
  have he : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ (p.2.2 - 1).unpair) :=
    Primrec.unpair.comp (nat_sub.comp (snd.comp snd) (const 1))
  have ht := fst.comp he
  have hi := snd.comp he
  have hb := succ.comp (Primrec₂.natPair.comp (const 0) hi)
  have hf : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ Nat.pair 1 (if p.1 = 1 then 0 else p.1 - 2) + 1) := succ.comp (Primrec₂.natPair.comp (const 1)
    (ite (Primrec.eq.comp fst (const 1)) (const 0) (nat_sub.comp fst (const 2))))
  have hp := succ.comp (Primrec₂.natPair.comp (const 0) (nat_sub.comp hi (const 1)))
  have hs := succ.comp (Primrec₂.natPair.comp (const 1)
    (ite (nat_lt.comp fst (const 2)) (succ.comp hi) hi))
  exact (ite (Primrec.eq.comp ht (const 0))
    (ite ((Primrec.eq.comp fst (const 0)).or (nat_lt.comp hi hd)) hb
      (ite (Primrec.eq.comp hi hd) hf hp)) hs).of_eq (fun _ ↦ rfl)


theorem proofRewNatArguments_primrec :
    Primrec (fun p : ℕ × (ℕ × ℕ) ↦ proofRewNatArguments p.1 p.2.1 p.2.2) := by
  have he : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ (p.2.2 - 1).unpair) :=
    Primrec.unpair.comp (nat_sub.comp (snd.comp snd) (const 1))
  have h0 : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ (p.2.2 - 1).unpair.1) := fst.comp he
  have h1 : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ ((p.2.2 - 1).unpair.2 - 1).unpair.1) :=
    fst.comp (Primrec.unpair.comp (nat_sub.comp (snd.comp he) (const 1)))
  have hmap0 : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ (p.1, (p.2.1, (p.2.2 - 1).unpair.1))) :=
    Primrec₂.pair.comp fst (Primrec₂.pair.comp (fst.comp snd) h0)
  have hmap1 : Primrec (fun p : ℕ × (ℕ × ℕ) ↦ (p.1, (p.2.1, ((p.2.2 - 1).unpair.2 - 1).unpair.1))) :=
    Primrec₂.pair.comp fst (Primrec₂.pair.comp (fst.comp snd) h1)
  exact (natVectorTwo_primrec.comp (proofRewNatTerm_primrec.comp hmap0)
    (proofRewNatTerm_primrec.comp hmap1)).of_eq (fun _ ↦ rfl)

def proofRewNatFormulaStep (r : ℕ) (d e : ℕ) (vs : List ℕ) : ℕ :=
  let t := (e - 1).unpair.1
  let c := (e - 1).unpair.2
  if e = 0 then 0
  else if t = 0 ∨ t = 1 then
    Nat.pair t (Nat.pair 2 (Nat.pair c.unpair.2.unpair.1 (proofRewNatArguments r d c.unpair.2.unpair.2))) + 1
  else if t = 2 then Nat.pair 2 0 + 1
  else if t = 3 then Nat.pair 3 0 + 1
  else if t = 4 ∨ t = 5 then Nat.pair t (Nat.pair (vs.getD 0 0) (vs.getD 1 0)) + 1
  else if t = 6 ∨ t = 7 then Nat.pair t (vs.getD 0 0) + 1
  else 0

theorem proofRewNatFormulaStep_primrec :
    Primrec (fun p : ℕ × ((ℕ × ℕ) × List ℕ) ↦ proofRewNatFormulaStep p.1 p.2.1.1 p.2.1.2 p.2.2) := by
  have hd : Primrec (fun p : ℕ × ((ℕ × ℕ) × List ℕ) ↦ p.2.1.1) := fst.comp (fst.comp snd)
  have he : Primrec (fun p : ℕ × ((ℕ × ℕ) × List ℕ) ↦ p.2.1.2) := snd.comp (fst.comp snd)
  have hv : Primrec (fun p : ℕ × ((ℕ × ℕ) × List ℕ) ↦ p.2.2) := snd.comp snd
  have ht := fst.comp (Primrec.unpair.comp (nat_sub.comp he (const 1)))
  have hc := snd.comp (Primrec.unpair.comp (nat_sub.comp he (const 1)))
  have hrest := snd.comp (Primrec.unpair.comp hc)
  have hsym := fst.comp (Primrec.unpair.comp hrest)
  have hargs := snd.comp (Primrec.unpair.comp hrest)
  have hra := proofRewNatArguments_primrec.comp (Primrec₂.pair.comp fst (Primrec₂.pair.comp hd hargs))
  have h0 := (list_getD 0).comp hv (const 0)
  have h1 := (list_getD 0).comp hv (const 1)
  exact ite (Primrec.eq.comp he (const 0)) (const 0)
    (ite (PrimrecPred.or (Primrec.eq.comp ht (const 0)) (Primrec.eq.comp ht (const 1)))
      (succ.comp (Primrec₂.natPair.comp ht
        (Primrec₂.natPair.comp (const 2) (Primrec₂.natPair.comp hsym hra))))
    (ite (Primrec.eq.comp ht (const 2)) (const (Nat.pair 2 0 + 1))
    (ite (Primrec.eq.comp ht (const 3)) (const (Nat.pair 3 0 + 1))
    (ite (PrimrecPred.or (Primrec.eq.comp ht (const 4)) (Primrec.eq.comp ht (const 5)))
      (succ.comp (Primrec₂.natPair.comp ht (Primrec₂.natPair.comp h0 h1)))
    (ite (PrimrecPred.or (Primrec.eq.comp ht (const 6)) (Primrec.eq.comp ht (const 7)))
      (succ.comp (Primrec₂.natPair.comp ht h0)) (const 0))))))

theorem proofRewNatFormulaStep_correct (r : ℕ) (d e : ℕ) :
    proofRewNatFormulaStep r d e ((Semiformula.subArgs (d, e)).map (fun b ↦ proofRewNatFormula r b.1 b.2)) =
      proofRewNatFormula r d e := by
  cases e with
  | zero => simp [proofRewNatFormulaStep, proofRewNatFormula]
  | succ e =>
    rw [proofRewNatFormula]
    simp only [proofRewNatFormulaStep, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte, Semiformula.subArgs_succ]
    split_ifs <;> simp_all

theorem proofRewNatFormula_primrec :
    Primrec₂ (fun (r : ℕ) (b : ℕ × ℕ) ↦ proofRewNatFormula r b.1 b.2) :=
  Primrec.nat_omega_rec _ (m := fun (_ : ℕ) (b : ℕ × ℕ) ↦ b.2)
    (l := fun (_ : ℕ) b ↦ Semiformula.subArgs b)
    (g := fun r q ↦ some (proofRewNatFormulaStep r q.1.1 q.1.2 q.2))
    (snd.comp snd) (Semiformula.primrec_subArgs.comp snd)
    (option_some.comp proofRewNatFormulaStep_primrec)
    (fun _ b ↦ Semiformula.subArgs_ord b)
    (fun r b ↦ congrArg some (proofRewNatFormulaStep_correct r b.1 b.2))

end ZFVP
