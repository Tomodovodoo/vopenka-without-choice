import ZFVP.ModelTheory.InfinitaryKeislerSoundness

/-! Infinitary semantics with an extensional generalized quantifier. Variable
operations and first-order schemas are independent of the choice of Q. -/

namespace ZFVP.Infinitary

open LO LO.FirstOrder

namespace Formula

variable {L : Language} {M : Type*} [Structure L M]

def EvalWithQ (Q : Set M → Prop) : {n : ℕ} → Formula L n → (Fin n → M) → Prop
  | _, .fo φ, b => φ.Evalb b
  | _, .neg φ, b => ¬EvalWithQ Q φ b
  | _, .conj φ, b => ∀ i, EvalWithQ Q (φ i) b
  | _, .exs φ, b => ∃ x, EvalWithQ Q φ (x :> b)
  | _, .q φ, b => Q {x | EvalWithQ Q φ (x :> b)}

variable (Q : Set M → Prop)

@[simp] theorem evalWithQ_fo {n} (φ : Semisentence L n) (b : Fin n → M) :
    EvalWithQ Q (.fo φ) b ↔ φ.Evalb b := Iff.rfl
@[simp] theorem evalWithQ_neg {n} (φ : Formula L n) (b : Fin n → M) :
    EvalWithQ Q (.neg φ) b ↔ ¬EvalWithQ Q φ b := Iff.rfl
@[simp] theorem evalWithQ_conj {n} (φ : ℕ → Formula L n) (b : Fin n → M) :
    EvalWithQ Q (.conj φ) b ↔ ∀ i, EvalWithQ Q (φ i) b := Iff.rfl
@[simp] theorem evalWithQ_exs {n} (φ : Formula L (n + 1)) (b : Fin n → M) :
    EvalWithQ Q (.exs φ) b ↔ ∃ x, EvalWithQ Q φ (x :> b) := Iff.rfl
@[simp] theorem evalWithQ_q {n} (φ : Formula L (n + 1)) (b : Fin n → M) :
    EvalWithQ Q (.q φ) b ↔ Q {x | EvalWithQ Q φ (x :> b)} := Iff.rfl

@[simp] theorem evalWithQ_disj {n} (φ : ℕ → Formula L n) (b : Fin n → M) :
    EvalWithQ Q (disj φ) b ↔ ∃ i, EvalWithQ Q (φ i) b := by
  classical
  simp [disj]
@[simp] theorem evalWithQ_all {n} (φ : Formula L (n + 1)) (b : Fin n → M) :
    EvalWithQ Q (all φ) b ↔ ∀ x, EvalWithQ Q φ (x :> b) := by
  classical
  simp [all]
@[simp] theorem evalWithQ_and {n} (φ ψ : Formula L n) (b : Fin n → M) :
    EvalWithQ Q (and φ ψ) b ↔ EvalWithQ Q φ b ∧ EvalWithQ Q ψ b := by
  classical
  simp only [and, evalWithQ_conj]
  constructor
  · intro h; exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨hφ, hψ⟩ i; split_ifs <;> assumption
@[simp] theorem evalWithQ_or {n} (φ ψ : Formula L n) (b : Fin n → M) :
    EvalWithQ Q (or φ ψ) b ↔ EvalWithQ Q φ b ∨ EvalWithQ Q ψ b := by
  classical
  simp [or]
  tauto
@[simp] theorem evalWithQ_imp {n} (φ ψ : Formula L n) (b : Fin n → M) :
    EvalWithQ Q (imp φ ψ) b ↔ (EvalWithQ Q φ b → EvalWithQ Q ψ b) := by
  classical
  simp [imp]
  tauto
@[simp] theorem evalWithQ_iff {n} (φ ψ : Formula L n) (b : Fin n → M) :
    EvalWithQ Q (iff φ ψ) b ↔ (EvalWithQ Q φ b ↔ EvalWithQ Q ψ b) := by simp [iff, iff_def]

@[simp] theorem evalWithQ_rename {n m} (ρ : Fin n → Fin m) (φ : Formula L n) (b : Fin m → M) :
    EvalWithQ Q (rename ρ φ) b ↔ EvalWithQ Q φ (b ∘ ρ) := by
  induction φ generalizing m with
  | fo φ => exact Semiformula.eval_map ρ id b Empty.elim φ
  | neg φ ih => exact not_congr (ih ρ b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i ρ b
  | exs φ ih =>
    exact exists_congr fun x ↦ (ih (liftRenaming ρ) (x :> b)).trans (by rw [compose_liftRenaming])
  | q φ ih =>
    change Q {x | EvalWithQ Q (rename (liftRenaming ρ) φ) (x :> b)} ↔ _
    have he : {x | EvalWithQ Q (rename (liftRenaming ρ) φ) (x :> b)} =
        {x | EvalWithQ Q φ (x :> (b ∘ ρ))} := by
      ext x
      exact (ih (liftRenaming ρ) (x :> b)).trans (by rw [compose_liftRenaming]; rfl)
    rw [he]
    rfl

@[simp] theorem evalWithQ_subst {n m} (σ : Fin n → Semiterm L Empty m) (φ : Formula L n) (b : Fin m → M) :
    EvalWithQ Q (subst σ φ) b ↔ EvalWithQ Q φ (fun i ↦ (σ i).val b Empty.elim) := by
  induction φ generalizing m with
  | fo φ => exact Semiformula.eval_substs σ φ
  | neg φ ih => exact not_congr (ih σ b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i σ b
  | exs φ ih =>
    exact exists_congr fun x ↦ (ih (liftSubstitution σ) (x :> b)).trans (by rw [val_liftSubstitution])
  | q φ ih =>
    change Q {x | EvalWithQ Q (subst (liftSubstitution σ) φ) (x :> b)} ↔ _
    have he : {x | EvalWithQ Q (subst (liftSubstitution σ) φ) (x :> b)} =
        {x | EvalWithQ Q φ (x :> fun i ↦ (σ i).val b Empty.elim)} := by
      ext x
      exact (ih (liftSubstitution σ) (x :> b)).trans (by rw [val_liftSubstitution]; rfl)
    rw [he]
    rfl

@[simp] theorem evalWithQ_substFirst {n} (t : Semiterm L Empty n) (φ : Formula L (n + 1)) (b : Fin n → M) :
    EvalWithQ Q (substFirst t φ) b ↔ EvalWithQ Q φ (t.val b Empty.elim :> b) := by
  rw [substFirst, evalWithQ_subst]
  have he : (fun i : Fin (n + 1) ↦
      (Fin.cases t Semiterm.bvar i : Semiterm L Empty n).val b Empty.elim) = t.val b Empty.elim :> b := by
    funext i; cases i using Fin.cases <;> rfl
  rw [he]

@[simp] theorem evalWithQ_swapFirstTwo {n} (φ : Formula L (n + 2)) (b : Fin n → M) (x y : M) :
    EvalWithQ Q (swapFirstTwo φ) (x :> y :> b) ↔ EvalWithQ Q φ (y :> x :> b) := by
  rw [swapFirstTwo, evalWithQ_rename]
  have he : (x :> y :> b) ∘ Fin.cases 1 (Fin.cases 0 (fun i ↦ i.succ.succ)) = y :> x :> b := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases <;> rfl
  rw [he]

@[simp] theorem evalWithQ_expandFirstOrder {n} (φ : Semisentence L n) (b : Fin n → M) :
    EvalWithQ Q (expandFirstOrder φ) b ↔ φ.Evalb b := by
  induction φ with
  | verum => rfl
  | falsum => exact iff_of_eq (propext not_true)
  | rel r ts => rfl
  | nrel r ts => rfl
  | and φ ψ ihφ ihψ => rw [expandFirstOrder, evalWithQ_and]; exact and_congr (ihφ b) (ihψ b)
  | or φ ψ ihφ ihψ => rw [expandFirstOrder, evalWithQ_or]; exact or_congr (ihφ b) (ihψ b)
  | all φ ih => rw [expandFirstOrder, evalWithQ_all]; exact forall_congr' fun x ↦ ih (x :> b)
  | exs φ ih => rw [expandFirstOrder, evalWithQ_exs]; exact exists_congr fun x ↦ ih (x :> b)

@[simp] theorem evalWithQ_equal [L.Eq] [Structure.Eq L M] {n} (i j : Fin n) (b : Fin n → M) :
    EvalWithQ Q (equal (L := L) i j) b ↔ b i = b j := by simp [equal, Semiformula.eval_rel]

@[simp] theorem evalWithQ_termEqual [L.Eq] [Structure.Eq L M] {n}
    (s t : Semiterm L Empty n) (b : Fin n → M) :
    EvalWithQ Q (termEqual s t) b ↔ s.val b Empty.elim = t.val b Empty.elim := by
  simp [termEqual, Semiformula.eval_rel]

end Formula
end ZFVP.Infinitary
