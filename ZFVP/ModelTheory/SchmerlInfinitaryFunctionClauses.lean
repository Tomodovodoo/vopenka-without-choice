import ZFVP.ModelTheory.SchmerlSelectedDomains
import ZFVP.ModelTheory.SchmerlInfinitaryBranches
import ZFVP.SetTheory.FiniteDictionary

/-! Uniform syntax for the finite-function tree clauses. The ambient set is a
bound variable, so this uses one countable language for all internally infinite
sets, without a family of named constants. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory Set Order
open ZFVP.Infinitary (Formula)

universe u v

def finiteBinaryFunctionFormula : SetTheorySemisentence 2 :=
  f“p s. p ⊆ !prod.dfn s (!succ.dfn (!succ.dfn (!isEmpty))) ∧
    !IsFunction.dfn p ∧ !internallyFiniteFormula (!domain.dfn p)”

def domainAboveFormula : SetTheorySemisentence 2 := f“p d. d ⊆ !domain.dfn p”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_finiteBinaryFunctionFormula (p s : V) :
    finiteBinaryFunctionFormula.Evalb ![p, s] ↔
      p ∈ finitePartialFunctions s ((2 : ℕ) : V) := by
  rw [mem_finitePartialFunctions]
  simp [finiteBinaryFunctionFormula]
  intros
  rfl

theorem eval_domainAboveFormula (p d : V) :
    domainAboveFormula.Evalb ![p, d] ↔ d ⊆ domain p := by
  simp [domainAboveFormula]

variable {L : Language.{0}}

def functionOriginal (η : ℒₛₑₜ →ᵥ L) {n : ℕ}
    (φ : SetTheorySemisentence n) : Formula L n := .fo (φ.lMap η)

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_functionOriginal_of_reduct (η : ℒₛₑₜ →ᵥ L) (S : Structure L V)
    (hS : S.lMap η = (inferInstance : Structure ℒₛₑₜ V))
    {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → V) :
    @Formula.Eval L V S n (functionOriginal η φ) b ↔ φ.Evalb b := by
  change (φ.lMap η).Evalb (s := S) b ↔ φ.Evalb b
  calc
    _ ↔ φ.Evalb (s := S.lMap η) b := Semiformula.eval_lMap
    _ ↔ φ.Evalb b := by rw [hS]

def selectedDomainClause (η : ℒₛₑₜ →ᵥ L) (D : Formula L 2) : Formula L 1 :=
  let fin := functionOriginal η internallyFiniteFormula
  let sub := functionOriginal η (“x y. x ⊆ y” : SetTheorySemisentence 2)
  .and
    (.all (.imp (D.rename ![1, 0]) (.and (fin.rename ![0]) sub)))
    (.and
      (.all (.all (.imp (.and (D.rename ![2, 1]) (D.rename ![2, 0]))
        (.or (sub.rename ![1, 0]) (sub.rename ![0, 1])))))
      (.and
        (.all (.imp (.and (fin.rename ![0]) sub)
          (.exs (.and (D.rename ![2, 0]) (sub.rename ![1, 0])))))
        (.and (.q (D.rename ![1, 0]))
          (.all (.imp (D.rename ![1, 0])
            (.neg (.q (.and (D.rename ![2, 0]) (sub.rename ![0, 1])))))))))

def functionNodeClause (η : ℒₛₑₜ →ᵥ L) (D : Formula L 2) : Formula L 2 :=
  .and (functionOriginal η finiteBinaryFunctionFormula)
    (.exs (.and ((functionOriginal η domain.dfn).rename ![0, 1]) (D.rename ![2, 0])))

def functionColorEquality (F : Formula L 3) : Formula L 3 :=
  .exs (.and (F.rename ![3, 0, 1]) (F.rename ![3, 0, 2]))

def functionColorTotal (η : ℒₛₑₜ →ᵥ L) (F : Formula L 3) : Formula L 1 :=
  .all (.exs (.and (F.rename ![2, 0, 1])
    (.all (.imp (F.rename ![3, 0, 2])
      ((functionOriginal η (“x y. x = y” : SetTheorySemisentence 2)).rename ![0, 1])))))

def functionColorCountable (F : Formula L 3) : Formula L 1 :=
  .neg (.q (.exs (F.rename ![2, 1, 0])))

def functionWeakClause (η : ℒₛₑₜ →ᵥ L) (D : Formula L 2)
    (F : Formula L 3) : Formula L 1 :=
  let N := functionNodeClause η D
  let E := functionColorEquality F
  let sub := functionOriginal η (“x y. x ⊆ y” : SetTheorySemisentence 2)
  .all (.all (.all (.imp
    (.and (N.rename ![0, 3]) (.and (N.rename ![1, 3]) (.and (N.rename ![2, 3])
      (.and (sub.rename ![0, 1]) (.and (sub.rename ![0, 2])
        (.and (E.rename ![0, 1, 3]) (E.rename ![0, 2, 3])))))))
    (.or (sub.rename ![1, 2]) (sub.rename ![2, 1])))))

def functionCandidateClause (η : ℒₛₑₜ →ᵥ L) (D : Formula L 2)
    (F : Formula L 3) : Formula L 3 :=
  let N := functionNodeClause η D
  let E := functionColorEquality F
  let sub := functionOriginal η (“x y. x ⊆ y” : SetTheorySemisentence 2)
  .and ((functionOriginal η finiteBinaryFunctionFormula).rename ![0, 2])
    (.exs (.and (N.rename ![0, 3])
      (.and (.or (sub.rename ![0, 2])
        (.and (sub.rename ![2, 0]) (E.rename ![2, 0, 3]))) (sub.rename ![1, 0]))))

def functionCandidateCofinality (η : ℒₛₑₜ →ᵥ L) (D : Formula L 2)
    (F : Formula L 3) : Formula L 2 :=
  .all (.imp (D.rename ![2, 0])
    (.exs (.and ((functionCandidateClause η D F).rename ![0, 2, 3])
      ((functionOriginal η domainAboveFormula).rename ![0, 1]))))

def functionCodesClause (η : ℒₛₑₜ →ᵥ L) (D : Formula L 2)
    (F : Formula L 3) : Formula L 1 :=
  .all (.imp (.and (functionNodeClause η D) (functionCandidateCofinality η D F))
    (.exs (.all (.iff
      ((functionOriginal η (“x y. x ∈ y” : SetTheorySemisentence 2)).rename ![0, 1])
      ((functionCandidateClause η D F).rename ![0, 2, 3])))))

variable (η : ℒₛₑₜ →ᵥ L) (S : Structure L V)
  (hS : S.lMap η = (inferInstance : Structure ℒₛₑₜ V))
  (D : Formula L 2) (F : Formula L 3)

include hS

theorem eval_selectedDomainClause (s : V) :
    @Formula.Eval L V S 1 (selectedDomainClause η D) ![s] ↔
      SelectedDomainClauses s (fun d ↦ @Formula.Eval L V S 2 D ![s, d]) := by
  let : Structure L V := S
  have hf (a : V) : (functionOriginal η internallyFiniteFormula).Eval ![a] ↔
      IsInternallyFinite a := by rw [eval_functionOriginal_of_reduct η S hS]; simp
  have hsub (a b : V) :
      (functionOriginal η (“x y. x ⊆ y” : SetTheorySemisentence 2)).Eval ![a, b] ↔ a ⊆ b := by
    rw [eval_functionOriginal_of_reduct η S hS]; simp
  simp [selectedDomainClause, Formula.eval_and, Formula.eval_all, Formula.eval_imp,
    Formula.eval_or, Formula.eval_exs, Formula.eval_q, Formula.eval_neg, not_not,
    Formula.eval_rename, hf, hsub, and_imp]
  constructor
  · rintro ⟨hfin, hlin, hcof, hunc, hini⟩
    exact ⟨hfin, fun d e hd he ↦ hlin d e hd he, hcof, hunc, hini⟩
  · intro h
    exact ⟨h.finite, h.linear, h.cofinal, h.uncountable, h.initial⟩

theorem eval_functionNodeClause (x s : V) :
    @Formula.Eval L V S 2 (functionNodeClause η D) ![x, s] ↔
      x ∈ finitePartialFunctions s ((2 : ℕ) : V) ∧
        @Formula.Eval L V S 2 D ![s, domain x] := by
  let : Structure L V := S
  have hp := (eval_functionOriginal_of_reduct η S hS finiteBinaryFunctionFormula ![x, s]).trans
    (eval_finiteBinaryFunctionFormula x s)
  have hd (d : V) : (functionOriginal η domain.dfn).Eval ![d, x] ↔ d = domain x := by
    rw [eval_functionOriginal_of_reduct η S hS]; simp
  simp [functionNodeClause, Formula.eval_and, Formula.eval_exs, Formula.eval_rename, hp, hd]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_functionColorTotal (s : V) :
    @Formula.Eval L V S 1 (functionColorTotal η F) ![s] ↔
      ∀ x : V, ∃ c : V, @Formula.Eval L V S 3 F ![s, c, x] ∧
        ∀ d : V, @Formula.Eval L V S 3 F ![s, d, x] → d = c := by
  let : Structure L V := S
  have he (a b : V) :
      (functionOriginal η (“x y. x = y” : SetTheorySemisentence 2)).Eval ![a, b] ↔ a = b := by
    rw [eval_functionOriginal_of_reduct η S hS]; simp
  simp [functionColorTotal, Formula.eval_all, Formula.eval_exs,
    Formula.eval_and, Formula.eval_imp, Formula.eval_rename, he]

omit hS [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_functionColorCountable (s : V) :
    @Formula.Eval L V S 1 (functionColorCountable F) ![s] ↔
      ({c : V | ∃ x : V, @Formula.Eval L V S 3 F ![s, c, x]}).Countable := by
  let : Structure L V := S
  simp [functionColorCountable, Formula.eval_neg, Formula.eval_q,
    Formula.eval_exs, Formula.eval_rename]

omit hS [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_functionColorEquality (f : V → V) (s x y : V)
    (hF : ∀ c z, @Formula.Eval L V S 3 F ![s, c, z] ↔ c = f z) :
    @Formula.Eval L V S 3 (functionColorEquality F) ![x, y, s] ↔ f x = f y := by
  let : Structure L V := S
  simp [functionColorEquality, Formula.eval_exs, Formula.eval_and, Formula.eval_rename, hF]

theorem eval_functionWeakClause (f : V → V) (s : V)
    (hF : ∀ c z, @Formula.Eval L V S 3 F ![s, c, z] ↔ c = f z) :
    @Formula.Eval L V S 1 (functionWeakClause η D F) ![s] ↔
      ∀ x y z : V,
        x ∈ finitePartialFunctions s ((2 : ℕ) : V) → @Formula.Eval L V S 2 D ![s, domain x] →
        y ∈ finitePartialFunctions s ((2 : ℕ) : V) → @Formula.Eval L V S 2 D ![s, domain y] →
        z ∈ finitePartialFunctions s ((2 : ℕ) : V) → @Formula.Eval L V S 2 D ![s, domain z] →
        x ⊆ y → x ⊆ z → f x = f y → f x = f z → y ⊆ z ∨ z ⊆ y := by
  let : Structure L V := S
  have hsub (a b : V) :
      (functionOriginal η (“x y. x ⊆ y” : SetTheorySemisentence 2)).Eval ![a, b] ↔ a ⊆ b := by
    rw [eval_functionOriginal_of_reduct η S hS]; simp
  simp [functionWeakClause, Formula.eval_all, Formula.eval_imp, Formula.eval_and,
    Formula.eval_or, Formula.eval_rename, eval_functionNodeClause η S hS D,
    eval_functionColorEquality S F f s _ _ hF, hsub, and_imp]
  constructor
  · intro h x y z
    exact h z y x
  · intro h z y x
    exact h x y z

theorem eval_functionCandidateClause (f : V → V) (s b p : V)
    (hF : ∀ c z, @Formula.Eval L V S 3 F ![s, c, z] ↔ c = f z) :
    @Formula.Eval L V S 3 (functionCandidateClause η D F) ![p, b, s] ↔
      functionFilterCandidate s (fun d ↦ @Formula.Eval L V S 2 D ![s, d])
        (fun x y ↦ f x = f y) b p := by
  let : Structure L V := S
  have hp := (eval_functionOriginal_of_reduct η S hS finiteBinaryFunctionFormula ![p, s]).trans
    (eval_finiteBinaryFunctionFormula p s)
  have hsub (a b : V) :
      (functionOriginal η (“x y. x ⊆ y” : SetTheorySemisentence 2)).Eval ![a, b] ↔ a ⊆ b := by
    rw [eval_functionOriginal_of_reduct η S hS]; simp
  simp [functionCandidateClause, functionFilterCandidate, Formula.eval_and,
    Formula.eval_or, Formula.eval_exs, Formula.eval_rename, hp,
    eval_functionNodeClause η S hS D, eval_functionColorEquality S F f s _ _ hF, hsub,
    and_assoc]

theorem eval_functionCandidateCofinality (f : V → V) (s b : V)
    (hF : ∀ c z, @Formula.Eval L V S 3 F ![s, c, z] ↔ c = f z) :
    @Formula.Eval L V S 2 (functionCandidateCofinality η D F) ![b, s] ↔
      ∀ d : V, @Formula.Eval L V S 2 D ![s, d] → ∃ p : V,
        functionFilterCandidate s (fun d ↦ @Formula.Eval L V S 2 D ![s, d])
          (fun x y ↦ f x = f y) b p ∧ d ⊆ domain p := by
  let : Structure L V := S
  have hd (p d : V) : (functionOriginal η domainAboveFormula).Eval ![p, d] ↔ d ⊆ domain p :=
    (eval_functionOriginal_of_reduct η S hS domainAboveFormula ![p, d]).trans
      (eval_domainAboveFormula p d)
  simp [functionCandidateCofinality, Formula.eval_all, Formula.eval_imp,
    Formula.eval_exs, Formula.eval_and, Formula.eval_rename,
    eval_functionCandidateClause η S hS D F f s _ _ hF, hd]

theorem eval_functionCodesClause (f : V → V) (s : V)
    (hF : ∀ c z, @Formula.Eval L V S 3 F ![s, c, z] ↔ c = f z) :
    @Formula.Eval L V S 1 (functionCodesClause η D F) ![s] ↔
      ∀ b : V, b ∈ finitePartialFunctions s ((2 : ℕ) : V) →
        @Formula.Eval L V S 2 D ![s, domain b] →
        (∀ d : V, @Formula.Eval L V S 2 D ![s, d] → ∃ p : V,
          functionFilterCandidate s (fun d ↦ @Formula.Eval L V S 2 D ![s, d])
            (fun x y ↦ f x = f y) b p ∧ d ⊆ domain p) →
        ∃ m : V, ∀ p : V, p ∈ m ↔ functionFilterCandidate s
          (fun d ↦ @Formula.Eval L V S 2 D ![s, d]) (fun x y ↦ f x = f y) b p := by
  let : Structure L V := S
  have hm (p m : V) :
      (functionOriginal η (“x y. x ∈ y” : SetTheorySemisentence 2)).Eval ![p, m] ↔ p ∈ m := by
    rw [eval_functionOriginal_of_reduct η S hS]; simp
  simp [functionCodesClause, Formula.eval_all, Formula.eval_imp, Formula.eval_and,
    Formula.eval_exs, Formula.eval_iff, Formula.eval_rename,
    eval_functionNodeClause η S hS D,
    eval_functionCandidateCofinality η S hS D F f s _ hF,
    eval_functionCandidateClause η S hS D F f s _ _ hF, hm, and_imp]

end ZFVP.Schmerl
