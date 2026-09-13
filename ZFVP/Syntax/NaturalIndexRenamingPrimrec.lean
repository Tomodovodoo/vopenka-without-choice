import ZFVP.Syntax.NaturalIndexRenaming

/-! Uniform primitive recursion for capture-avoiding index renaming. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Primrec

theorem reindexNatVariable_primrec :
    Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ reindexNatVariable p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ p.2.1) := fst.comp snd
  have hi : Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ p.2.2) := snd.comp snd
  have hk := nat_sub.comp hi hd
  have hg : Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ p.1.getD (p.2.2 - p.2.1) (p.2.2 - p.2.1)) :=
    (option_getD.comp (list_getElem?.comp fst hk) hk).of_eq (fun _ ↦ rfl)
  exact ite (nat_lt.comp hi hd) hi (nat_add.comp hg hd)

theorem reindexNatTerm_primrec :
    Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ reindexNatTerm p.1 p.2.1 p.2.2) := by
  have hi : Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ (p.2.2 - 1).unpair.2) :=
    snd.comp (Primrec.unpair.comp (nat_sub.comp (snd.comp snd) (const 1)))
  exact succ.comp (Primrec₂.natPair.comp (const 0)
    (reindexNatVariable_primrec.comp (Primrec₂.pair.comp fst (Primrec₂.pair.comp (fst.comp snd) hi))))

theorem natVectorTwo_primrec : Primrec₂ natVectorTwo :=
  succ.comp (Primrec₂.natPair.comp fst (succ.comp (Primrec₂.natPair.comp snd (const 0))))

theorem reindexNatArguments_primrec :
    Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ reindexNatArguments p.1 p.2.1 p.2.2) := by
  have he : Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ (p.2.2 - 1).unpair) :=
    Primrec.unpair.comp (nat_sub.comp (snd.comp snd) (const 1))
  have h0 : Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ (p.2.2 - 1).unpair.1) := fst.comp he
  have h1 : Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ ((p.2.2 - 1).unpair.2 - 1).unpair.1) :=
    fst.comp (Primrec.unpair.comp (nat_sub.comp (snd.comp he) (const 1)))
  have hmap0 : Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ (p.1, (p.2.1, (p.2.2 - 1).unpair.1))) :=
    Primrec₂.pair.comp fst (Primrec₂.pair.comp (fst.comp snd) h0)
  have hmap1 : Primrec (fun p : List ℕ × (ℕ × ℕ) ↦ (p.1, (p.2.1, ((p.2.2 - 1).unpair.2 - 1).unpair.1))) :=
    Primrec₂.pair.comp fst (Primrec₂.pair.comp (fst.comp snd) h1)
  exact (natVectorTwo_primrec.comp (reindexNatTerm_primrec.comp hmap0)
    (reindexNatTerm_primrec.comp hmap1)).of_eq (fun _ ↦ rfl)

def reindexNatFormulaStep (r : List ℕ) (d e : ℕ) (vs : List ℕ) : ℕ :=
  let t := (e - 1).unpair.1
  let c := (e - 1).unpair.2
  if e = 0 then 0
  else if t = 0 ∨ t = 1 then
    Nat.pair t (Nat.pair 2 (Nat.pair c.unpair.2.unpair.1 (reindexNatArguments r d c.unpair.2.unpair.2))) + 1
  else if t = 2 then Nat.pair 2 0 + 1
  else if t = 3 then Nat.pair 3 0 + 1
  else if t = 4 ∨ t = 5 then Nat.pair t (Nat.pair (vs.getD 0 0) (vs.getD 1 0)) + 1
  else if t = 6 ∨ t = 7 then Nat.pair t (vs.getD 0 0) + 1
  else 0

theorem reindexNatFormulaStep_primrec :
    Primrec (fun p : List ℕ × ((ℕ × ℕ) × List ℕ) ↦ reindexNatFormulaStep p.1 p.2.1.1 p.2.1.2 p.2.2) := by
  have hd : Primrec (fun p : List ℕ × ((ℕ × ℕ) × List ℕ) ↦ p.2.1.1) := fst.comp (fst.comp snd)
  have he : Primrec (fun p : List ℕ × ((ℕ × ℕ) × List ℕ) ↦ p.2.1.2) := snd.comp (fst.comp snd)
  have hv : Primrec (fun p : List ℕ × ((ℕ × ℕ) × List ℕ) ↦ p.2.2) := snd.comp snd
  have ht := fst.comp (Primrec.unpair.comp (nat_sub.comp he (const 1)))
  have hc := snd.comp (Primrec.unpair.comp (nat_sub.comp he (const 1)))
  have hrest := snd.comp (Primrec.unpair.comp hc)
  have hsym := fst.comp (Primrec.unpair.comp hrest)
  have hargs := snd.comp (Primrec.unpair.comp hrest)
  have hra := reindexNatArguments_primrec.comp (Primrec₂.pair.comp fst (Primrec₂.pair.comp hd hargs))
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

theorem reindexNatFormulaStep_correct (r : List ℕ) (d e : ℕ) :
    reindexNatFormulaStep r d e ((Semiformula.subArgs (d, e)).map (fun b ↦ reindexNatFormula r b.1 b.2)) =
      reindexNatFormula r d e := by
  cases e with
  | zero => simp [reindexNatFormulaStep, reindexNatFormula]
  | succ e =>
    rw [reindexNatFormula]
    simp only [reindexNatFormulaStep, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte, Semiformula.subArgs_succ]
    split_ifs <;> simp_all

theorem reindexNatFormula_primrec :
    Primrec₂ (fun (r : List ℕ) (b : ℕ × ℕ) ↦ reindexNatFormula r b.1 b.2) :=
  Primrec.nat_omega_rec _ (m := fun (_ : List ℕ) (b : ℕ × ℕ) ↦ b.2)
    (l := fun (_ : List ℕ) b ↦ Semiformula.subArgs b)
    (g := fun r q ↦ some (reindexNatFormulaStep r q.1.1 q.1.2 q.2))
    (snd.comp snd) (Semiformula.primrec_subArgs.comp snd)
    (option_some.comp reindexNatFormulaStep_primrec)
    (fun _ b ↦ Semiformula.subArgs_ord b)
    (fun r b ↦ congrArg some (reindexNatFormulaStep_correct r b.1 b.2))

end ZFVP
