import ZFVP.Syntax.NaturalIndexRenamingPrimrec

/-! Natural-code rewriting for the eigenvariable and witness rules of LK. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Mode zero shifts free variables, mode one opens a binder with a fresh
variable, and mode `k + 2` substitutes free variable `k` for that binder. -/
def proofRewNatTerm (s d e : ℕ) : ℕ :=
  let t := (e - 1).unpair.1
  let i := (e - 1).unpair.2
  if t = 0 then
    if s = 0 ∨ i < d then Nat.pair 0 i + 1
    else if i = d then Nat.pair 1 (if s = 1 then 0 else s - 2) + 1
    else Nat.pair 0 (i - 1) + 1
  else Nat.pair 1 (if s < 2 then i + 1 else i) + 1

def liftNatTerm (e : ℕ) : ℕ :=
  let t := (e - 1).unpair.1
  let i := (e - 1).unpair.2
  if t = 0 then Nat.pair 0 (i + 1) + 1 else Nat.pair 1 i + 1

theorem liftNatTerm_encode {n : ℕ} (t : Semiterm ℒₛₑₜ ℕ n) :
    liftNatTerm (Encodable.encode t) = Encodable.encode (Rew.bShift t) := by
  cases t with
  | bvar i => change liftNatTerm (Nat.pair 0 i.val + 1) = Nat.pair 0 (i.val + 1) + 1; simp [liftNatTerm]
  | fvar i => change liftNatTerm (Nat.pair 1 i + 1) = Nat.pair 1 i + 1; simp [liftNatTerm]
  | func f _ => exact Empty.elim f

theorem proofRewNatTerm_lift {n : ℕ} (s d : ℕ) (t : Semiterm ℒₛₑₜ ℕ n) :
    proofRewNatTerm s (d + 1) (Encodable.encode (Rew.bShift t)) =
      liftNatTerm (proofRewNatTerm s d (Encodable.encode t)) := by
  cases t with
  | bvar i =>
    change proofRewNatTerm s (d + 1) (Nat.pair 0 (i.val + 1) + 1) =
      liftNatTerm (proofRewNatTerm s d (Nat.pair 0 i.val + 1))
    simp only [proofRewNatTerm, Nat.add_sub_cancel, Nat.unpair_pair, ↓reduceIte,
      Nat.add_lt_add_iff_right, Nat.add_left_inj]
    split_ifs <;> simp_all [liftNatTerm]
    omega
  | fvar i =>
    change proofRewNatTerm s (d + 1) (Nat.pair 1 i + 1) =
      liftNatTerm (proofRewNatTerm s d (Nat.pair 1 i + 1))
    simp [proofRewNatTerm, liftNatTerm]
  | func f _ => exact Empty.elim f

theorem proofRewNatTerm_q {n m : ℕ} (s d : ℕ) (σ : Rew ℒₛₑₜ ℕ n ℕ m)
    (hσ : ∀ t, proofRewNatTerm s d (Encodable.encode t) = Encodable.encode (σ t)) :
    ∀ t, proofRewNatTerm s (d + 1) (Encodable.encode t) = Encodable.encode (σ.q t) := by
  intro t
  cases t with
  | bvar i =>
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · change proofRewNatTerm s (d + 1) (Nat.pair 0 0 + 1) = Nat.pair 0 0 + 1
      simp [proofRewNatTerm]
    · rw [Rew.q_bvar_succ]
      exact (proofRewNatTerm_lift s d (.bvar i)).trans ((congrArg liftNatTerm (hσ (.bvar i))).trans (liftNatTerm_encode _))
  | fvar i =>
    rw [Rew.q_fvar]
    exact (proofRewNatTerm_lift s d (.fvar i)).trans ((congrArg liftNatTerm (hσ (.fvar i))).trans (liftNatTerm_encode _))
  | func f _ => exact Empty.elim f


def proofRewNatArguments (r : ℕ) (d c : ℕ) : ℕ :=
  natVectorTwo (proofRewNatTerm r d (c - 1).unpair.1)
    (proofRewNatTerm r d ((c - 1).unpair.2 - 1).unpair.1)

def proofRewNatFormula (r : ℕ) (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
    let t := e.unpair.1
    let c := e.unpair.2
    if t = 0 ∨ t = 1 then
      Nat.pair t (Nat.pair 2 (Nat.pair c.unpair.2.unpair.1 (proofRewNatArguments r d c.unpair.2.unpair.2))) + 1
    else if t = 2 then Nat.pair 2 0 + 1
    else if t = 3 then Nat.pair 3 0 + 1
    else if t = 4 ∨ t = 5 then
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _))
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))
      Nat.pair t (Nat.pair (proofRewNatFormula r d c.unpair.1) (proofRewNatFormula r d c.unpair.2)) + 1
    else if t = 6 ∨ t = 7 then
      have : c < e + 1 := Nat.lt_succ_iff.mpr (Nat.unpair_right_le _)
      Nat.pair t (proofRewNatFormula r (d + 1) c) + 1
    else 0
  termination_by e => e

theorem proofRewNatArguments_encode {n m : ℕ} (r : ℕ) (d : ℕ) (σ : Rew ℒₛₑₜ ℕ n ℕ m)
    (hσ : ∀ t, proofRewNatTerm r d (Encodable.encode t) = Encodable.encode (σ t))
    (ts : Fin 2 → Semiterm ℒₛₑₜ ℕ n) :
    proofRewNatArguments r d (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i))) =
      Matrix.vecToNat (fun i ↦ Encodable.encode (σ (ts i))) := by
  simp only [vecToNat_two, proofRewNatArguments, natVectorTwo, Nat.add_sub_cancel, Nat.unpair_pair,
    hσ]

theorem proofRewNatFormula_encode {n m : ℕ} (r : ℕ) (d : ℕ) (σ : Rew ℒₛₑₜ ℕ n ℕ m)
    (hσ : ∀ t, proofRewNatTerm r d (Encodable.encode t) = Encodable.encode (σ t))
    (φ : Semiproposition ℒₛₑₜ n) :
    proofRewNatFormula r d (Encodable.encode φ) = Encodable.encode (σ ▹ φ) := by
  induction φ generalizing m d with
  | verum => change proofRewNatFormula r d (Nat.pair 2 0 + 1) = Nat.pair 2 0 + 1; simp [proofRewNatFormula]
  | falsum => change proofRewNatFormula r d (Nat.pair 3 0 + 1) = Nat.pair 3 0 + 1; simp [proofRewNatFormula]
  | rel R ts =>
    cases R <;> simp [Semiformula.encode_rel, proofRewNatFormula,
      proofRewNatArguments_encode r d σ hσ]
  | nrel R ts =>
    cases R <;> simp [Semiformula.encode_nrel, proofRewNatFormula,
      proofRewNatArguments_encode r d σ hσ]
  | and φ ψ ihφ ihψ =>
    change proofRewNatFormula r d (Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) =
      Nat.pair 4 (Nat.pair (Encodable.encode (σ ▹ φ)) (Encodable.encode (σ ▹ ψ))) + 1
    simp [proofRewNatFormula, ihφ d σ hσ, ihψ d σ hσ]
  | or φ ψ ihφ ihψ =>
    change proofRewNatFormula r d (Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) =
      Nat.pair 5 (Nat.pair (Encodable.encode (σ ▹ φ)) (Encodable.encode (σ ▹ ψ))) + 1
    simp [proofRewNatFormula, ihφ d σ hσ, ihψ d σ hσ]
  | all φ ih =>
    change proofRewNatFormula r d (Nat.pair 6 (Encodable.encode φ) + 1) = Nat.pair 6 (Encodable.encode (σ.q ▹ φ)) + 1
    simp [proofRewNatFormula, ih (d + 1) σ.q (proofRewNatTerm_q r d σ hσ)]
  | exs φ ih =>
    change proofRewNatFormula r d (Nat.pair 7 (Encodable.encode φ) + 1) = Nat.pair 7 (Encodable.encode (σ.q ▹ φ)) + 1
    simp [proofRewNatFormula, ih (d + 1) σ.q (proofRewNatTerm_q r d σ hσ)]

end ZFVP
