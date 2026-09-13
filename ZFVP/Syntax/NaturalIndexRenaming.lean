import ZFVP.Syntax.NaturalFormulaClosure

/-! Capture-avoiding bound-variable renaming on natural-number formula codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def reindexNatVariable (r : List ℕ) (d i : ℕ) : ℕ :=
  if i < d then i else r.getD (i - d) (i - d) + d

@[simp] theorem reindexNatVariable_zero (r : List ℕ) (d : ℕ) : reindexNatVariable r (d + 1) 0 = 0 := by
  simp [reindexNatVariable]

@[simp] theorem reindexNatVariable_succ (r : List ℕ) (d i : ℕ) :
    reindexNatVariable r (d + 1) (i + 1) = reindexNatVariable r d i + 1 := by
  simp only [reindexNatVariable, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]
  split <;> simp [Nat.add_assoc]

def reindexNatTerm (r : List ℕ) (d e : ℕ) : ℕ :=
  Nat.pair 0 (reindexNatVariable r d (e - 1).unpair.2) + 1

def natVectorTwo (x y : ℕ) : ℕ := Nat.pair x (Nat.pair y 0 + 1) + 1

theorem vecToNat_two (v : Fin 2 → ℕ) : Matrix.vecToNat v = natVectorTwo (v 0) (v 1) := rfl

def reindexNatArguments (r : List ℕ) (d c : ℕ) : ℕ :=
  natVectorTwo (reindexNatTerm r d (c - 1).unpair.1)
    (reindexNatTerm r d ((c - 1).unpair.2 - 1).unpair.1)

def reindexNatFormula (r : List ℕ) (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
    let t := e.unpair.1
    let c := e.unpair.2
    if t = 0 ∨ t = 1 then
      Nat.pair t (Nat.pair 2 (Nat.pair c.unpair.2.unpair.1 (reindexNatArguments r d c.unpair.2.unpair.2))) + 1
    else if t = 2 then Nat.pair 2 0 + 1
    else if t = 3 then Nat.pair 3 0 + 1
    else if t = 4 ∨ t = 5 then
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _))
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))
      Nat.pair t (Nat.pair (reindexNatFormula r d c.unpair.1) (reindexNatFormula r d c.unpair.2)) + 1
    else if t = 6 ∨ t = 7 then
      have : c < e + 1 := Nat.lt_succ_iff.mpr (Nat.unpair_right_le _)
      Nat.pair t (reindexNatFormula r (d + 1) c) + 1
    else 0
  termination_by e => e

theorem reindexNatVariable_q {n m : ℕ} (r : List ℕ) (d : ℕ) (σ : Rew ℒₛₑₜ Empty n Empty m)
    (hσ : ∀ i, ∃ j, σ (.bvar i) = .bvar j ∧ j.val = reindexNatVariable r d i.val) :
    ∀ i, ∃ j, σ.q (.bvar i) = .bvar j ∧ j.val = reindexNatVariable r (d + 1) i.val := by
  intro i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · exact ⟨0, rfl, by simp⟩
  · obtain ⟨j, hj, he⟩ := hσ i
    exact ⟨j.succ, by simp [Rew.q_bvar_succ, hj], by simpa using he⟩

theorem reindexNatTerm_encode {n m : ℕ} (r : List ℕ) (d : ℕ) (σ : Rew ℒₛₑₜ Empty n Empty m)
    (hσ : ∀ i, ∃ j, σ (.bvar i) = .bvar j ∧ j.val = reindexNatVariable r d i.val)
    (t : Semiterm ℒₛₑₜ Empty n) :
    reindexNatTerm r d (Encodable.encode t) = Encodable.encode (σ t) := by
  cases t with
  | bvar i =>
    obtain ⟨j, hj, he⟩ := hσ i
    rw [hj]
    change reindexNatTerm r d (Nat.pair 0 i.val + 1) = Nat.pair 0 j.val + 1
    simp [reindexNatTerm, he]
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem reindexNatArguments_encode {n m : ℕ} (r : List ℕ) (d : ℕ) (σ : Rew ℒₛₑₜ Empty n Empty m)
    (hσ : ∀ i, ∃ j, σ (.bvar i) = .bvar j ∧ j.val = reindexNatVariable r d i.val)
    (ts : Fin 2 → Semiterm ℒₛₑₜ Empty n) :
    reindexNatArguments r d (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i))) =
      Matrix.vecToNat (fun i ↦ Encodable.encode (σ (ts i))) := by
  simp only [vecToNat_two, reindexNatArguments, natVectorTwo, Nat.add_sub_cancel, Nat.unpair_pair,
    reindexNatTerm_encode r d σ hσ]

theorem reindexNatFormula_encode {n m : ℕ} (r : List ℕ) (d : ℕ) (σ : Rew ℒₛₑₜ Empty n Empty m)
    (hσ : ∀ i, ∃ j, σ (.bvar i) = .bvar j ∧ j.val = reindexNatVariable r d i.val)
    (φ : SetTheorySemisentence n) :
    reindexNatFormula r d (Encodable.encode φ) = Encodable.encode (σ ▹ φ) := by
  induction φ generalizing m d with
  | verum => change reindexNatFormula r d (Nat.pair 2 0 + 1) = Nat.pair 2 0 + 1; simp [reindexNatFormula]
  | falsum => change reindexNatFormula r d (Nat.pair 3 0 + 1) = Nat.pair 3 0 + 1; simp [reindexNatFormula]
  | rel R ts =>
    cases R <;> simp [Semiformula.encode_rel, reindexNatFormula,
      reindexNatArguments_encode r d σ hσ]
  | nrel R ts =>
    cases R <;> simp [Semiformula.encode_nrel, reindexNatFormula,
      reindexNatArguments_encode r d σ hσ]
  | and φ ψ ihφ ihψ =>
    change reindexNatFormula r d (Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) =
      Nat.pair 4 (Nat.pair (Encodable.encode (σ ▹ φ)) (Encodable.encode (σ ▹ ψ))) + 1
    simp [reindexNatFormula, ihφ d σ hσ, ihψ d σ hσ]
  | or φ ψ ihφ ihψ =>
    change reindexNatFormula r d (Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) =
      Nat.pair 5 (Nat.pair (Encodable.encode (σ ▹ φ)) (Encodable.encode (σ ▹ ψ))) + 1
    simp [reindexNatFormula, ihφ d σ hσ, ihψ d σ hσ]
  | all φ ih =>
    change reindexNatFormula r d (Nat.pair 6 (Encodable.encode φ) + 1) = Nat.pair 6 (Encodable.encode (σ.q ▹ φ)) + 1
    simp [reindexNatFormula, ih (d + 1) σ.q (reindexNatVariable_q r d σ hσ)]
  | exs φ ih =>
    change reindexNatFormula r d (Nat.pair 7 (Encodable.encode φ) + 1) = Nat.pair 7 (Encodable.encode (σ.q ▹ φ)) + 1
    simp [reindexNatFormula, ih (d + 1) σ.q (reindexNatVariable_q r d σ hσ)]

end ZFVP
