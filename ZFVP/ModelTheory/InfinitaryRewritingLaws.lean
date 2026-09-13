import ZFVP.ModelTheory.InfinitaryTermSubstitution
import ZFVP.ModelTheory.InfinitaryRenaming

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language}

/-- One rewriting operation handles both renaming and capture-avoiding term substitution. -/
def rewrite : {n m : ℕ} → Rew L Empty n Empty m → Formula L n → Formula L m
  | _, _, w, .fo φ => .fo (w ▹ φ)
  | _, _, w, .neg φ => .neg (rewrite w φ)
  | _, _, w, .conj φ => .conj fun i ↦ rewrite w (φ i)
  | _, _, w, .exs φ => .exs (rewrite w.q φ)
  | _, _, w, .q φ => .q (rewrite w.q φ)

@[simp]theorem rewrite_id {n} (φ : Formula L n) : rewrite Rew.id φ = φ := by
  induction φ with
  | fo φ => simp [rewrite]
  | neg φ ih => exact congrArg Formula.neg ih
  | conj φ ih => exact congrArg Formula.conj (funext ih)
  | exs φ ih => simpa [rewrite] using congrArg Formula.exs ih
  | q φ ih => simpa [rewrite] using congrArg Formula.q ih

@[simp]theorem rewrite_comp {n m k} (v : Rew L Empty n Empty m)
    (w : Rew L Empty m Empty k) (φ : Formula L n) :
    rewrite w (rewrite v φ) = rewrite (w.comp v) φ := by
  induction φ generalizing m k with
  | fo φ => exact congrArg Formula.fo (TransitiveRewriting.comp_app v w φ).symm
  | neg φ ih => exact congrArg Formula.neg (ih v w)
  | conj φ ih => exact congrArg Formula.conj (funext fun i ↦ ih i v w)
  | exs φ ih => simpa [rewrite, Rew.q_comp] using congrArg Formula.exs (ih v.q w.q)
  | q φ ih => simpa [rewrite, Rew.q_comp] using congrArg Formula.q (ih v.q w.q)

theorem q_subst_eq {n m} (σ : Fin n → Semiterm L Empty m) :
    (Rew.subst σ).q = Rew.subst (liftSubstitution σ) := by
  apply Rew.ext
  · intro i; cases i using Fin.cases <;> simp [Rew.q, liftSubstitution]
  · intro i; exact i.elim

theorem q_map_eq {n m} (ρ : Fin n → Fin m) :
    (Rew.map (L := L) ρ (id : Empty → Empty)).q = Rew.map (liftRenaming ρ) id := by
  apply Rew.ext
  · intro i; cases i using Fin.cases <;> simp [Rew.q, liftRenaming]
  · intro i; exact i.elim

@[simp]theorem rewrite_subst {n m} (σ : Fin n → Semiterm L Empty m) (φ : Formula L n) :
    rewrite (Rew.subst σ) φ = subst σ φ := by
  induction φ generalizing m with
  | fo φ => rfl
  | neg φ ih => exact congrArg Formula.neg (ih σ)
  | conj φ ih => exact congrArg Formula.conj (funext fun i ↦ ih i σ)
  | exs φ ih => simpa [rewrite, subst, q_subst_eq] using congrArg Formula.exs (ih (liftSubstitution σ))
  | q φ ih => simpa [rewrite, subst, q_subst_eq] using congrArg Formula.q (ih (liftSubstitution σ))

@[simp]theorem rewrite_map {n m} (ρ : Fin n → Fin m) (φ : Formula L n) :
    rewrite (Rew.map ρ id) φ = rename ρ φ := by
  induction φ generalizing m with
  | fo φ => rfl
  | neg φ ih => exact congrArg Formula.neg (ih ρ)
  | conj φ ih => exact congrArg Formula.conj (funext fun i ↦ ih i ρ)
  | exs φ ih => simpa [rewrite, rename, q_map_eq] using congrArg Formula.exs (ih (liftRenaming ρ))
  | q φ ih => simpa [rewrite, rename, q_map_eq] using congrArg Formula.q (ih (liftRenaming ρ))

@[simp]theorem subst_bvar_eq_rename {n m} (ρ : Fin n → Fin m) (φ : Formula L n) :
    subst (fun i ↦ .bvar (ρ i)) φ = rename ρ φ := by
  rw [← rewrite_subst, ← rewrite_map]
  rfl

@[simp]theorem rename_id {n} (φ : Formula L n) : rename id φ = φ := by
  rw [← rewrite_map, Rew.map_id, rewrite_id]

@[simp]theorem subst_closed_rename {n m} (σ : Fin n → Semiterm L Empty m) (φ : Sentence L) :
    subst σ (rename (Fin.elim0 : Fin 0 → Fin n) φ) = rename (Fin.elim0 : Fin 0 → Fin m) φ := by
  rw [← rewrite_subst, ← rewrite_map, rewrite_comp, ← rewrite_map]
  congr 1
  apply Rew.ext
  · intro i; exact i.elim0
  · intro i; exact i.elim

@[simp] theorem rename_closed_rename {n m} (ρ : Fin n → Fin m) (φ : Sentence L) :
    rename ρ (rename (Fin.elim0 : Fin 0 → Fin n) φ) = rename (Fin.elim0 : Fin 0 → Fin m) φ := by
  rw [← subst_bvar_eq_rename, subst_closed_rename]

@[simp] theorem subst_imp {n m} (σ : Fin n → Semiterm L Empty m) (φ ψ : Formula L n) :
    subst σ (imp φ ψ) = imp (subst σ φ) (subst σ ψ) := by
  simp [imp, or, and, subst, apply_ite]

end Formula
end ZFVP.Infinitary
