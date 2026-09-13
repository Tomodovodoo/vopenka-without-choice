import ZFVP.ModelTheory.InfinitarySyntax

/-! Renaming free variable positions, including below first-order and uncountability binders. -/

namespace ZFVP.Infinitary

open LO LO.FirstOrder

def liftRenaming {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i ↦ (ρ i).succ)

theorem compose_liftRenaming {M : Type*} {n m : ℕ} (ρ : Fin n → Fin m)
    (b : Fin m → M) (x : M) :
    (x :> b) ∘ liftRenaming ρ = x :> (b ∘ ρ) := by
  funext i
  cases i using Fin.cases <;> simp [liftRenaming, Function.comp_def]

namespace Formula

variable {L : Language}

def rename : {n m : ℕ} → (Fin n → Fin m) → Formula L n → Formula L m
  | _, _, ρ, .fo φ => .fo (Rew.map ρ id ▹ φ)
  | _, _, ρ, .neg φ => .neg (rename ρ φ)
  | _, _, ρ, .conj φ => .conj fun i ↦ rename ρ (φ i)
  | _, _, ρ, .exs φ => .exs (rename (liftRenaming ρ) φ)
  | _, _, ρ, .q φ => .q (rename (liftRenaming ρ) φ)

@[simp] theorem eval_rename {M : Type*} [Structure L M] {n m : ℕ}
    (ρ : Fin n → Fin m) (φ : Formula L n) (b : Fin m → M) :
    Eval (rename ρ φ) b ↔ Eval φ (b ∘ ρ) := by
  induction φ generalizing m with
  | fo φ =>
      exact Semiformula.eval_map ρ id b Empty.elim φ
  | neg φ ih => exact not_congr (ih ρ b)
  | conj φ ih => exact forall_congr' (fun i ↦ ih i ρ b)
  | exs φ ih =>
      change (∃ x, Eval (rename (liftRenaming ρ) φ) (x :> b)) ↔ _
      exact exists_congr (fun x ↦ (ih (liftRenaming ρ) (x :> b)).trans
        (by rw [compose_liftRenaming]))
  | q φ ih =>
      change ¬Set.Countable {x | Eval (rename (liftRenaming ρ) φ) (x :> b)} ↔ _
      have he : {x | Eval (rename (liftRenaming ρ) φ) (x :> b)} =
          {x | Eval φ (x :> (b ∘ ρ))} := by
        ext x
        exact (ih (liftRenaming ρ) (x :> b)).trans (by rw [compose_liftRenaming]; rfl)
      rw [he]
      rfl

def swapFirstTwo {n : ℕ} (φ : Formula L (n + 2)) : Formula L (n + 2) :=
  rename (Fin.cases 1 (Fin.cases 0 (fun i ↦ i.succ.succ))) φ

@[simp] theorem eval_swapFirstTwo {M : Type*} [Structure L M] {n : ℕ}
    (φ : Formula L (n + 2)) (b : Fin n → M) (x y : M) :
    Eval (swapFirstTwo φ) (x :> y :> b) ↔ Eval φ (y :> x :> b) := by
  rw [swapFirstTwo, eval_rename]
  have he : (x :> y :> b) ∘ Fin.cases 1 (Fin.cases 0 (fun i ↦ i.succ.succ)) =
      y :> x :> b := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases <;> rfl
  rw [he]

end Formula

end ZFVP.Infinitary
