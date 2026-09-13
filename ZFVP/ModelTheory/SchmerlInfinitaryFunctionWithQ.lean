import ZFVP.ModelTheory.SchmerlInfinitaryFunctionSentence
import ZFVP.ModelTheory.SchmerlInfinitaryClassWithQ
import ZFVP.ModelTheory.SchmerlInfinitaryExpansion
import ZFVP.ModelTheory.SchmerlInfinitaryFiniteSmall

/-! The function-tree clauses with the actual ambient countability quantifier. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula)

variable {L : Language.{0}}

@[simp] theorem qFree_functionOriginal (η : ℒₛₑₜ →ᵥ L) {n : ℕ} (φ : SetTheorySemisentence n) :
    Formula.QFree (functionOriginal η φ) := True.intro

theorem qFree_functionColorTotal (η : ℒₛₑₜ →ᵥ L) {F : Formula L 3} (hF : Formula.QFree F) :
    Formula.QFree (functionColorTotal η F) := by simp [functionColorTotal, hF]

theorem qFree_functionWeakClause (η : ℒₛₑₜ →ᵥ L) {D : Formula L 2} {F : Formula L 3}
    (hD : Formula.QFree D) (hF : Formula.QFree F) :
    Formula.QFree (functionWeakClause η D F) := by
  simp [functionWeakClause, functionNodeClause, functionColorEquality, hD, hF]

theorem qFree_functionCodesClause (η : ℒₛₑₜ →ᵥ L) {D : Formula L 2} {F : Formula L 3}
    (hD : Formula.QFree D) (hF : Formula.QFree F) :
    Formula.QFree (functionCodesClause η D F) := by
  simp [functionCodesClause, functionCandidateCofinality, functionCandidateClause,
    functionNodeClause, functionColorEquality, hD, hF]

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure SelectedDomainClausesWithQ (Q : Set W → Prop) (s : W) (D : W → Prop) : Prop where
  finite : ∀ d, D d → IsInternallyFinite d ∧ d ⊆ s
  linear : ∀ d e, D d → D e → d ⊆ e ∨ e ⊆ d
  cofinal : ∀ a, IsInternallyFinite a → a ⊆ s → ∃ d, D d ∧ a ⊆ d
  large : Q {d | D d}
  initial : ∀ d, D d → ¬Q {e | D e ∧ e ⊆ d}

variable (η : ℒₛₑₜ →ᵥ L) (S : Structure L W)
  (hS : S.lMap η = (inferInstance : Structure ℒₛₑₜ W)) (Q : Set W → Prop)

include hS

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem evalWithQ_functionOriginal_of_reduct {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → W) :
    @Formula.EvalWithQ L W S Q n (functionOriginal η φ) b ↔ φ.Evalb b :=
  eval_functionOriginal_of_reduct η S hS φ b

theorem evalWithQ_selectedDomainClause {D : Formula L 2} (hD : Formula.QFree D) (s : W) :
    @Formula.EvalWithQ L W S Q 1 (selectedDomainClause η D) ![s] ↔
      SelectedDomainClausesWithQ Q s (fun d ↦ @Formula.Eval L W S 2 D ![s, d]) := by
  let : Structure L W := S
  have hf (a : W) : Formula.EvalWithQ Q (functionOriginal η internallyFiniteFormula) ![a] ↔
      IsInternallyFinite a := by rw [evalWithQ_functionOriginal_of_reduct η S hS]; simp
  have hsub (a b : W) :
      Formula.EvalWithQ Q (functionOriginal η (“x y. x ⊆ y” : SetTheorySemisentence 2)) ![a, b] ↔ a ⊆ b := by
    rw [evalWithQ_functionOriginal_of_reduct η S hS]; simp
  simp [selectedDomainClause, Formula.evalWithQ_and, Formula.evalWithQ_all, Formula.evalWithQ_imp,
    Formula.evalWithQ_or, Formula.evalWithQ_exs, Formula.evalWithQ_q, Formula.evalWithQ_neg,
    Formula.evalWithQ_rename, hf, hsub, hD.evalWithQ_iff Q, and_imp]
  constructor
  · rintro ⟨hfin, hlin, hcof, hlarge, hini⟩
    exact ⟨hfin, fun d e hd he ↦ hlin d e hd he, hcof, hlarge, hini⟩
  · intro h
    exact ⟨h.finite, h.linear, h.cofinal, h.large, h.initial⟩

theorem functionTreeDataClause_of_semanticDataWithQ {D : Formula L 2} {F : Formula L 3}
    (hDq : Formula.QFree D) (hFq : Formula.QFree F) (s : W) (f : W → W)
    (hF : ∀ c x : W, @Formula.Eval L W S 3 F ![s, c, x] ↔ c = f x)
    (hD : SelectedDomainClausesWithQ Q s (fun d ↦ @Formula.Eval L W S 2 D ![s, d]))
    (hcount : ¬Q (Set.range f))
    (hweak : ∀ x y z : W,
      x ∈ finitePartialFunctions s ((2 : ℕ) : W) → @Formula.Eval L W S 2 D ![s, domain x] →
      y ∈ finitePartialFunctions s ((2 : ℕ) : W) → @Formula.Eval L W S 2 D ![s, domain y] →
      z ∈ finitePartialFunctions s ((2 : ℕ) : W) → @Formula.Eval L W S 2 D ![s, domain z] →
      x ⊆ y → x ⊆ z → f x = f y → f x = f z → y ⊆ z ∨ z ⊆ y)
    (hcodes : ∀ b : W, b ∈ finitePartialFunctions s ((2 : ℕ) : W) →
      @Formula.Eval L W S 2 D ![s, domain b] →
      (∀ d : W, @Formula.Eval L W S 2 D ![s, d] → ∃ p : W,
        functionFilterCandidate s (fun d ↦ @Formula.Eval L W S 2 D ![s, d])
          (fun x y ↦ f x = f y) b p ∧ d ⊆ domain p) →
      ∃ m : W, ∀ p : W, p ∈ m ↔ functionFilterCandidate s
        (fun d ↦ @Formula.Eval L W S 2 D ![s, d]) (fun x y ↦ f x = f y) b p) :
    @Formula.EvalWithQ L W S Q 1 (functionTreeDataClause η D F) ![s] := by
  let : Structure L W := S
  have htotal : (functionColorTotal η F).Eval ![s] := by
    apply (eval_functionColorTotal η S hS F s).mpr
    exact fun x ↦ ⟨f x, (hF _ _).mpr rfl, fun c hc ↦ (hF _ _).mp hc⟩
  have hcountClause : Formula.EvalWithQ Q (functionColorCountable F) ![s] := by
    simp only [functionColorCountable, Formula.evalWithQ_neg, Formula.evalWithQ_q,
      Formula.evalWithQ_exs, Formula.evalWithQ_rename]
    have he : {c : W | ∃ x : W, Formula.EvalWithQ Q F ((x :> c :> ![s]) ∘ ![2, 1, 0])} =
        Set.range f := by
      ext c
      simp [hFq.evalWithQ_iff Q, hF, Set.mem_range, eq_comm]
    rwa [he]
  have hweakClause := (eval_functionWeakClause η S hS D F f s hF).mpr hweak
  have hcodesClause := (eval_functionCodesClause η S hS D F f s hF).mpr hcodes
  simp only [functionTreeDataClause, Formula.evalWithQ_and]
  exact ⟨(evalWithQ_selectedDomainClause η S hS Q hDq s).mpr hD,
    ((qFree_functionColorTotal η hFq).evalWithQ_iff Q ![s]).mpr htotal, hcountClause,
    ((qFree_functionWeakClause η hDq hFq).evalWithQ_iff Q ![s]).mpr hweakClause,
    ((qFree_functionCodesClause η hDq hFq).evalWithQ_iff Q ![s]).mpr hcodesClause⟩

theorem evalWithQ_functionTreeFamilySentence (D : Formula L 2) (F : Formula L 3) :
    @Formula.EvalWithQ L W S Q 0 (functionTreeFamilySentence η D F) ![] ↔
      ∀ s : W, IsInternallyInfinite s →
        @Formula.EvalWithQ L W S Q 1 (functionTreeDataClause η D F) ![s] := by
  let : Structure L W := S
  have hi (s : W) : Formula.EvalWithQ Q (functionOriginal η internallyInfiniteFormula) ![s] ↔
      IsInternallyInfinite s := by rw [evalWithQ_functionOriginal_of_reduct η S hS]; simp
  simp only [functionTreeFamilySentence, Formula.evalWithQ_all, Formula.evalWithQ_imp, hi]

omit hS in
theorem evalWithQ_finiteSmallSentence (S : Structure deadEndLanguage W)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ W)) (Q : Set W → Prop) :
    @Formula.EvalWithQ deadEndLanguage W S Q 0 finiteSmallSentence ![] ↔
      ∀ a : W, IsInternallyFinite a → ¬Q {x | x ∈ a} := by
  let : Structure deadEndLanguage W := S
  have hfin (a : W) :
      Formula.EvalWithQ Q (functionOriginal deadEndSetEmbedding internallyFiniteFormula) ![a] ↔
        IsInternallyFinite a := by rw [evalWithQ_functionOriginal_of_reduct deadEndSetEmbedding S hS]; simp
  have hmem (x a : W) : Formula.EvalWithQ Q
      (functionOriginal deadEndSetEmbedding (“x a. x ∈ a” : SetTheorySemisentence 2)) ![x, a] ↔ x ∈ a := by
    rw [evalWithQ_functionOriginal_of_reduct deadEndSetEmbedding S hS]; simp
  simp only [finiteSmallSentence, Formula.evalWithQ_all, Formula.evalWithQ_imp,
    Formula.evalWithQ_neg, Formula.evalWithQ_q, hfin, hmem]

end ZFVP.Schmerl
