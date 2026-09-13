import ZFVP.ModelTheory.InfinitaryRenaming
import ZFVP.ModelTheory.InfinitaryQuantifierAxioms

/-! The standard Q quantifier interchange axiom, with variable exchange explicit. -/

namespace ZFVP.Infinitary
open LO LO.FirstOrder

namespace Formula
variable {L : Language} {M : Type*} [Structure L M] {n : ℕ}

/-- With the innermost variables ordered x,y, this expresses
Q y (exists x, φ) → (exists x, Q y φ) ∨ Q x (exists y, φ). -/
def qInterchange (φ : Formula L (n + 1 + 1)) : Formula L n :=
  imp (.q (.exs φ)) (or (.exs (.q (swapFirstTwo φ))) (.q (.exs (swapFirstTwo φ))))

theorem eval_qInterchange (φ : Formula L (n + 1 + 1)) (b : Fin n → M) :
    Eval (qInterchange φ) b := by
  simp only [qInterchange, eval_imp, eval_or, eval_q, eval_exs, eval_swapFirstTwo]
  exact UncountableQuantifierLaws.interchange (fun x y ↦ Eval φ (x :> y :> b))

end Formula
end ZFVP.Infinitary
