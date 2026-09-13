import ZFVP.ModelTheory.InfinitaryRenaming
import ZFVP.ModelTheory.UncountableQuantifierLaws
import Foundation.FirstOrder.Basic.Operator

/-! Equality and the two-point smallness axiom in standard Q semantics. -/

namespace ZFVP.Infinitary
open LO LO.FirstOrder

namespace Formula
variable {L : Language} [L.Eq]

def equal {n : ℕ} (i j : Fin n) : Formula L n :=
  .fo (.rel Language.Eq.eq ![.bvar i, .bvar j])

@[simp] theorem eval_equal {M : Type*} [Structure L M] [Structure.Eq L M]
    {n : ℕ} (i j : Fin n) (b : Fin n → M) : Eval (equal (L := L) i j) b ↔ b i = b j := by
  simp [equal, Semiformula.eval_rel]

def qTwoPoints {n : ℕ} (i j : Fin n) : Formula L n :=
  .neg (.q (or (equal 0 i.succ) (equal 0 j.succ)))

theorem eval_qTwoPoints {M : Type*} [Structure L M] [Structure.Eq L M]
    {n : ℕ} (i j : Fin n) (b : Fin n → M) : Eval (qTwoPoints (L := L) i j) b := by
  classical
  simp only [qTwoPoints, eval_neg, eval_q, eval_or, eval_equal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, not_not]
  exact UncountableQuantifierLaws.countable_two_points (b i) (b j)

end Formula
end ZFVP.Infinitary

