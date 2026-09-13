import ZFVP.ModelTheory.InfinitarySyntax

/-! Capture-avoiding term substitution for formulas with countable operations and Q. -/

namespace ZFVP.Infinitary

open LO LO.FirstOrder

def liftSubstitution {L : Language} {n m : ℕ} (σ : Fin n → Semiterm L Empty m) :
    Fin (n + 1) → Semiterm L Empty (m + 1) :=
  Fin.cases (Semiterm.bvar 0) (fun i ↦ Rew.bShift (σ i))

theorem val_liftSubstitution {L : Language} {M : Type*} [Structure L M] {n m : ℕ}
    (σ : Fin n → Semiterm L Empty m) (b : Fin m → M) (x : M) :
    (fun i ↦ (liftSubstitution σ i).val (x :> b) Empty.elim) =
      x :> (fun i ↦ (σ i).val b Empty.elim) := by
  funext i
  cases i using Fin.cases <;> simp [liftSubstitution]

namespace Formula

variable {L : Language}

def subst : {n m : ℕ} → (Fin n → Semiterm L Empty m) → Formula L n → Formula L m
  | _, _, σ, .fo φ => .fo (φ ⇜ σ)
  | _, _, σ, .neg φ => .neg (subst σ φ)
  | _, _, σ, .conj φ => .conj fun i ↦ subst σ (φ i)
  | _, _, σ, .exs φ => .exs (subst (liftSubstitution σ) φ)
  | _, _, σ, .q φ => .q (subst (liftSubstitution σ) φ)

@[simp] theorem eval_subst {M : Type*} [Structure L M] {n m : ℕ}
    (σ : Fin n → Semiterm L Empty m) (φ : Formula L n) (b : Fin m → M) :
    Eval (subst σ φ) b ↔ Eval φ (fun i ↦ (σ i).val b Empty.elim) := by
  induction φ generalizing m with
  | fo φ => exact Semiformula.eval_substs σ φ
  | neg φ ih => exact not_congr (ih σ b)
  | conj φ ih => exact forall_congr' (fun i ↦ ih i σ b)
  | exs φ ih =>
      change (∃ x, Eval (subst (liftSubstitution σ) φ) (x :> b)) ↔ _
      exact exists_congr (fun x ↦ (ih (liftSubstitution σ) (x :> b)).trans
        (by rw [val_liftSubstitution]))
  | q φ ih =>
      change ¬Set.Countable {x | Eval (subst (liftSubstitution σ) φ) (x :> b)} ↔ _
      have he : {x | Eval (subst (liftSubstitution σ) φ) (x :> b)} =
          {x | Eval φ (x :> (fun i ↦ (σ i).val b Empty.elim))} := by
        ext x
        exact (ih (liftSubstitution σ) (x :> b)).trans (by rw [val_liftSubstitution]; rfl)
      rw [he]
      rfl

/-- Replace the first variable by a term, leaving the other variables in order. -/
def substFirst {n : ℕ} (t : Semiterm L Empty n) (φ : Formula L (n + 1)) : Formula L n :=
  subst (Fin.cases t Semiterm.bvar) φ

@[simp] theorem eval_substFirst {M : Type*} [Structure L M] {n : ℕ}
    (t : Semiterm L Empty n) (φ : Formula L (n + 1)) (b : Fin n → M) :
    Eval (substFirst t φ) b ↔ Eval φ (t.val b Empty.elim :> b) := by
  rw [substFirst, eval_subst]
  have he : (fun i : Fin (n + 1) ↦
      (Fin.cases t Semiterm.bvar i : Semiterm L Empty n).val b Empty.elim) =
      t.val b Empty.elim :> b := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [he]

end Formula

end ZFVP.Infinitary
