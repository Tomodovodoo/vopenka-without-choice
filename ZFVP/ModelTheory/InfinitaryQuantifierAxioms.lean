import ZFVP.ModelTheory.InfinitarySyntax
import ZFVP.ModelTheory.UncountableQuantifierLaws

/-! Explicit countable conjunction and uncountability axiom schemas, interpreted
in the standard semantics. These lemmas do not assume a completeness theorem. -/

namespace ZFVP.Infinitary
open LO LO.FirstOrder

namespace Formula
variable {L : Language} {M : Type*} [Structure L M] {n : ℕ}

def countableProjection (φ : ℕ → Formula L n) (i : ℕ) : Formula L n :=
  imp (.conj φ) (φ i)

def countableDistribution (φ : Formula L n) (ψ : ℕ → Formula L n) : Formula L n :=
  imp (.conj fun i ↦ imp φ (ψ i)) (imp φ (.conj ψ))

def qMonotonicity (φ ψ : Formula L (n + 1)) : Formula L n :=
  imp (all (imp φ ψ)) (imp (.q φ) (.q ψ))

def qCountableUnion (φ : ℕ → Formula L (n + 1)) : Formula L n :=
  imp (.q (disj φ)) (disj fun i ↦ .q (φ i))

theorem eval_countableProjection (φ : ℕ → Formula L n) (i : ℕ) (b : Fin n → M) :
    Eval (countableProjection φ i) b := by
  simpa only [countableProjection, eval_imp, eval_conj] using
    (fun h : ∀ j, Eval (φ j) b ↦ h i)

theorem eval_countableDistribution (φ : Formula L n) (ψ : ℕ → Formula L n)
    (b : Fin n → M) : Eval (countableDistribution φ ψ) b := by
  simp only [countableDistribution, eval_imp, eval_conj]
  exact fun h hφ i ↦ h i hφ

theorem eval_qMonotonicity (φ ψ : Formula L (n + 1)) (b : Fin n → M) :
    Eval (qMonotonicity φ ψ) b := by
  simp only [qMonotonicity, eval_imp, eval_all, eval_q]
  exact UncountableQuantifierLaws.uncountable_predicate_mono

theorem eval_qCountableUnion (φ : ℕ → Formula L (n + 1)) (b : Fin n → M) :
    Eval (qCountableUnion φ) b := by
  simp only [qCountableUnion, eval_imp, eval_disj, eval_q]
  exact (UncountableQuantifierLaws.uncountable_exists_nat_iff
    (fun i x ↦ Eval (φ i) (x :> b))).mp

end Formula
end ZFVP.Infinitary
