import ZFVP.ModelTheory.InfinitaryWeakSemantics
import ZFVP.ModelTheory.InfinitaryTermSubstitution
import ZFVP.ModelTheory.InfinitaryRenaming

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language} {M : Type*} [Structure L M] (Q : Set M → Prop)

@[simp] theorem weakEval_fo {n} (φ : Semisentence L n) (b : Fin n → M) :
    WeakEval Q (.fo φ) b ↔ φ.Evalb b := Iff.rfl
@[simp] theorem weakEval_neg {n} (φ : Formula L n) (b : Fin n → M) :
    WeakEval Q (.neg φ) b ↔ ¬WeakEval Q φ b := Iff.rfl
@[simp] theorem weakEval_conj {n} (φ : ℕ → Formula L n) (b : Fin n → M) :
    WeakEval Q (.conj φ) b ↔ ∀ i, WeakEval Q (φ i) b := Iff.rfl
@[simp] theorem weakEval_exs {n} (φ : Formula L (n + 1)) (b : Fin n → M) :
    WeakEval Q (.exs φ) b ↔ ∃ x, WeakEval Q φ (x :> b) := Iff.rfl
@[simp] theorem weakEval_q {n} (φ : Formula L (n + 1)) (b : Fin n → M) :
    WeakEval Q (.q φ) b ↔ Q {x | WeakEval Q φ (x :> b)} := Iff.rfl

@[simp] theorem weakEval_subst {n m} (σ : Fin n → Semiterm L Empty m)
    (φ : Formula L n) (b : Fin m → M) :
    WeakEval Q (φ.subst σ) b ↔ WeakEval Q φ (fun i ↦ (σ i).val b Empty.elim) := by
  induction φ generalizing m with
  | fo φ => exact Semiformula.eval_substs σ φ
  | neg φ ih => exact not_congr (ih σ b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i σ b
  | exs φ ih =>
    change (∃ x, WeakEval Q (φ.subst (liftSubstitution σ)) (x :> b)) ↔ _
    exact exists_congr fun x ↦ (ih (liftSubstitution σ) (x :> b)).trans
      (by rw [val_liftSubstitution])
  | q φ ih =>
    have he : {x : M | WeakEval Q (φ.subst (liftSubstitution σ)) (x :> b)} =
        {x : M | WeakEval Q φ (x :> (fun i ↦ (σ i).val b Empty.elim))} := by
      ext x
      exact (ih (liftSubstitution σ) (x :> b)).trans (by rw [val_liftSubstitution]; rfl)
    change Q _ ↔ Q _
    rw [he]

@[simp] theorem weakEval_substFirst {n} (t : Semiterm L Empty n)
    (φ : Formula L (n + 1)) (b : Fin n → M) :
    WeakEval Q (φ.substFirst t) b ↔ WeakEval Q φ (t.val b Empty.elim :> b) := by
  rw [substFirst, weakEval_subst]
  have he : (fun i : Fin (n + 1) ↦ (Fin.cases t Semiterm.bvar i : Semiterm L Empty n).val b Empty.elim) = t.val b Empty.elim :> b := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [he]

@[simp] theorem weakEval_rename {n m} (ρ : Fin n → Fin m)
    (φ : Formula L n) (b : Fin m → M) :
    WeakEval Q (φ.rename ρ) b ↔ WeakEval Q φ (b ∘ ρ) := by
  rw [← subst_bvar_eq_rename, weakEval_subst]
  rfl

end Formula
end ZFVP.Infinitary


