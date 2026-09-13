import ZFVP.ModelTheory.SchmerlInfinitaryDeadEndSentence

/-! The additional standard-Q clause needed to recover arbitrary maximal
finite-function filters from selected branches. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula)

variable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Every internally finite set has countably many external members. -/
def FinSmall : Prop := ∀ a : V, IsInternallyFinite a → ({x : V | x ∈ a} : Set V).Countable

/-- `∀ a, Finite(a) → ¬Q x, x ∈ a`, with Q interpreted as uncountability. -/
def finiteSmallSentence : Formula deadEndLanguage 0 :=
  .all (.imp (functionOriginal deadEndSetEmbedding internallyFiniteFormula)
    (.neg (.q (functionOriginal deadEndSetEmbedding
      (“x a. x ∈ a” : SetTheorySemisentence 2)))))

/-- The strengthened fixed sentence Φ⁺ from the finite-domain coverage repair. -/
noncomputable def weaklyRubinSentence : Formula deadEndLanguage 0 :=
  .and deadEndSentence finiteSmallSentence

variable {V}

theorem eval_finiteSmallSentence (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V)) :
    @Formula.Eval deadEndLanguage V S 0 finiteSmallSentence ![] ↔ FinSmall V := by
  classical
  let : Structure deadEndLanguage V := S
  have hfin (a : V) :
      (functionOriginal deadEndSetEmbedding internallyFiniteFormula).Eval ![a] ↔
        IsInternallyFinite a := by
    rw [eval_functionOriginal_of_reduct deadEndSetEmbedding S hS]
    simp
  have hmem (x a : V) :
      (functionOriginal deadEndSetEmbedding (“x a. x ∈ a” : SetTheorySemisentence 2)).Eval
        ![x, a] ↔ x ∈ a := by
    rw [eval_functionOriginal_of_reduct deadEndSetEmbedding S hS]
    simp
  simp only [finiteSmallSentence, Formula.eval_all, Formula.eval_imp,
    Formula.eval_neg, Formula.eval_q, hfin, FinSmall]
  simp only [hmem, not_not]

theorem eval_weaklyRubinSentence (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V)) :
    @Formula.Eval deadEndLanguage V S 0 weaklyRubinSentence ![] ↔
      @Formula.Eval deadEndLanguage V S 0 deadEndSentence ![] ∧ FinSmall V := by
  rw [weaklyRubinSentence, Formula.eval_and, eval_finiteSmallSentence S hS]

end ZFVP.Schmerl
