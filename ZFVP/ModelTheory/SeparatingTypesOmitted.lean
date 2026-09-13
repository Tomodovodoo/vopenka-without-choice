import ZFVP.ModelTheory.RubinBlockLemmas
import ZFVP.ModelTheory.RubinStageOmitting

/-! # Enayat's Lemma A.5

`ZFVP.SeparatingTypesLocallyOmitted`, stated in `ZFVP.ModelTheory.RubinStage`, says that the
theory `T = rubinTheory δ ρ` of Lemma A.2 locally omits every separating type `Σ^ψ_n`. This file
proves it, so Lemma A.2 becomes unconditional: see
`ZFVP.exists_elementary_extension_inseparable_upper_bounds'` at the end.

The proof is Enayat's, with the block form of Lemmas A.3 and A.4 from
`ZFVP.ModelTheory.RubinBlockLemmas` in place of the alternating one the paper prints.

Suppose `θ` is a formula in `q` free variables with `insert (∃x⃗ θ) T` consistent, and suppose no
member of `Σ^ψ_n` can be denied consistently: for every `a ∈ V n` the theory
`insert (∃x⃗ (θ ⋏ ∼ψ(ȧ, x⃗))) T` is inconsistent, and for every `b ∈ W n` the theory
`insert (∃x⃗ (θ ⋏ ψ(ḃ, x⃗))) T` is inconsistent. Two formulas of the language with the constants,
with one free slot `v` in place of the constant naming the parameter, carry those two families:

* `existsNotSat θ ψ`, `∃x⃗ (θ ⋏ ∼ψ(v, x⃗))`;
* `existsSat θ ψ`, `∃x⃗ (θ ⋏ ψ(v, x⃗))`.

Both are single formulas, so `ZFVP.exists_indices` gives one injective family `ks` of indices
covering the constants `d_n` of both, and `ZFVP.abstractFormula ks` turns each into an
`ℒₛₑₜ`-formula `A` of arity `1 + p` whose slot `0` is `v` and whose slots `1, …, p` are the
values of `d_{ks 1}, …, d_{ks p}`. Filling slot `0` with a parameter `&a` (`paramSubst`) gives the
body of Lemma A.4 for the sentence with `ȧ` in place of `v`, which is what
`ZFVP.consistent_insert_iff_blockEx_of_body` was made for: no `constSupport` of a substituted
formula has to be computed.

The two inconsistency assumptions then read, through
`ZFVP.consistent_insert_iff_blockEx_of_body` and `ZFVP.not_blockEx_iff`, as membership of `a` in

`Λ = {v | ∃r⃗ ∈ D⃗ ∀s⃗ ∈ D⃗ [(⋀ᵢ rᵢ <_{D_{k_i}} sᵢ) → ¬A⁻(v, s⃗)]}`

and of `b` in the same set `Γ` built from `A⁺`. Both are definable in `M` with parameters, by
`ZFVP.blockAllFormula` (`definable_blockAllNot`; the one point of bookkeeping is that
`blockAllFormula` hands its body the assignment `Matrix.appendr s ![v]` while `abstractFormula`
produces `Fin.addCases ![v] s`, and `swapSubst` moves between the two layouts).

`Λ` and `Γ` are disjoint: a common `v` gives an `∃⃗∀⃗` block over "no `x⃗` satisfies `θ ⋏ ∼ψ(v, x⃗)`
and none satisfies `θ ⋏ ψ(v, x⃗)`", while the consistency of `insert (∃x⃗ θ) T` gives an `∀⃗∃⃗`
block over "some `x⃗` satisfies `θ`", and `ZFVP.blockAll_blockEx_contradiction` puts the two
together inside one structure `(M, c)`, where `c` names the tuple `s⃗` by the constants `d_{ks i}`
(`ZFVP.exists_assign_of_injective`). So `Λ` is a definable set containing `V n` and missing
`W n`, contradicting `Inseparable M (V n) (W n)`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v

/-! ## The two formulas with a free slot for the parameter -/

section Xi

variable {C : Type u} {N : Type v} [SetStructure N] {q : ℕ}

/-- `θ(x⃗)` read in the context `x⃗, v` of arity `1 + q`, with `x⃗` at the low slots. -/
def liftFreeBody (θ : Semisentence (LSetC C) q) : Semisentence (LSetC C) (1 + q) :=
  θ ⇜ fun i : Fin q ↦ #(i.addCast 1)

/-- `ψ(v, x⃗)` read in the same context, with `v` at the top slot. -/
def liftParamBody (ψ : Semisentence (LSetC C) (q + 1)) : Semisentence (LSetC C) (1 + q) :=
  ψ ⇜ (#((0 : Fin 1).addNat q) :> fun i : Fin q ↦ #(i.addCast 1))

theorem eval_liftFreeBody (c : C → N) (θ : Semisentence (LSetC C) q) (v : N) (x : Fin q → N) :
    Semiformula.Eval (s := setConstStructure N c) (Matrix.appendr x ![v]) Empty.elim
        (liftFreeBody θ)
      ↔ Semiformula.Eval (s := setConstStructure N c) x Empty.elim θ := by
  rw [liftFreeBody, Semiformula.eval_substs]
  have h : (Semiterm.val (s := setConstStructure N c) (Matrix.appendr x ![v]) Empty.elim ∘
      fun i : Fin q ↦ (#(i.addCast 1) : Semiterm (LSetC C) Empty (1 + q))) = x := by
    funext i; simp
  rw [h]

theorem eval_liftParamBody (c : C → N) (ψ : Semisentence (LSetC C) (q + 1)) (v : N)
    (x : Fin q → N) :
    Semiformula.Eval (s := setConstStructure N c) (Matrix.appendr x ![v]) Empty.elim
        (liftParamBody ψ)
      ↔ Semiformula.Eval (s := setConstStructure N c) (v :> x) Empty.elim ψ := by
  rw [liftParamBody, Semiformula.eval_substs]
  have h : (Semiterm.val (s := setConstStructure N c) (Matrix.appendr x ![v]) Empty.elim ∘
      (#((0 : Fin 1).addNat q) :> fun i : Fin q ↦ (#(i.addCast 1) :
        Semiterm (LSetC C) Empty (1 + q)))) = (v :> x) := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  rw [h]

/-- `∃x⃗ θ(x⃗)`, with a free slot for a parameter that does not occur. -/
def existsBody (θ : Semisentence (LSetC C) q) : Semisentence (LSetC C) 1 :=
  ∃¹^[q] liftFreeBody θ

/-- `∃x⃗ (θ(x⃗) ⋏ ψ(v, x⃗))`, with `v` in the remaining slot. -/
def existsSat (θ : Semisentence (LSetC C) q) (ψ : Semisentence (LSetC C) (q + 1)) :
    Semisentence (LSetC C) 1 :=
  ∃¹^[q] (liftFreeBody θ ⋏ liftParamBody ψ)

/-- `∃x⃗ (θ(x⃗) ⋏ ∼ψ(v, x⃗))`, with `v` in the remaining slot. -/
def existsNotSat (θ : Semisentence (LSetC C) q) (ψ : Semisentence (LSetC C) (q + 1)) :
    Semisentence (LSetC C) 1 :=
  ∃¹^[q] (liftFreeBody θ ⋏ ∼liftParamBody ψ)

theorem eval_existsBody (c : C → N) (θ : Semisentence (LSetC C) q) (v : N) :
    Semiformula.Eval (s := setConstStructure N c) ![v] Empty.elim (existsBody θ)
      ↔ ∃ x : Fin q → N, Semiformula.Eval (s := setConstStructure N c) x Empty.elim θ := by
  simp only [existsBody, Semiformula.eval_exsItr, eval_liftFreeBody]

theorem eval_existsSat (c : C → N) (θ : Semisentence (LSetC C) q)
    (ψ : Semisentence (LSetC C) (q + 1)) (v : N) :
    Semiformula.Eval (s := setConstStructure N c) ![v] Empty.elim (existsSat θ ψ)
      ↔ ∃ x : Fin q → N, Semiformula.Eval (s := setConstStructure N c) x Empty.elim θ ∧
          Semiformula.Eval (s := setConstStructure N c) (v :> x) Empty.elim ψ := by
  simp only [existsSat, Semiformula.eval_exsItr, LogicalConnective.HomClass.map_and,
    eval_liftFreeBody, eval_liftParamBody]
  exact Iff.rfl

theorem eval_existsNotSat (c : C → N) (θ : Semisentence (LSetC C) q)
    (ψ : Semisentence (LSetC C) (q + 1)) (v : N) :
    Semiformula.Eval (s := setConstStructure N c) ![v] Empty.elim (existsNotSat θ ψ)
      ↔ ∃ x : Fin q → N, Semiformula.Eval (s := setConstStructure N c) x Empty.elim θ ∧
          ¬Semiformula.Eval (s := setConstStructure N c) (v :> x) Empty.elim ψ := by
  simp only [existsNotSat, Semiformula.eval_exsItr, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_neg, eval_liftFreeBody, eval_liftParamBody]
  exact Iff.rfl

/-! ### The same three statements read off the sentences of `LocallyOmits` -/

theorem eval_exsClosure_self (c : C → N) (θ : Semisentence (LSetC C) q) :
    Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim (∃¹* θ)
      ↔ ∃ x : Fin q → N, Semiformula.Eval (s := setConstStructure N c) x Empty.elim θ := by
  simp only [Semiformula.eval_exsClosure]

theorem eval_exsClosure_and (c : C → N) (θ : Semisentence (LSetC C) q)
    (ψ : Semisentence (LSetC C) (q + 1)) (a : C) :
    Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim (∃¹* (θ ⋏ substConst ψ a))
      ↔ ∃ x : Fin q → N, Semiformula.Eval (s := setConstStructure N c) x Empty.elim θ ∧
          Semiformula.Eval (s := setConstStructure N c) (c a :> x) Empty.elim ψ := by
  simp only [Semiformula.eval_exsClosure, LogicalConnective.HomClass.map_and, eval_substConst]
  exact Iff.rfl

theorem eval_exsClosure_and_neg (c : C → N) (θ : Semisentence (LSetC C) q)
    (ψ : Semisentence (LSetC C) (q + 1)) (a : C) :
    Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim (∃¹* (θ ⋏ ∼substConst ψ a))
      ↔ ∃ x : Fin q → N, Semiformula.Eval (s := setConstStructure N c) x Empty.elim θ ∧
          ¬Semiformula.Eval (s := setConstStructure N c) (c a :> x) Empty.elim ψ := by
  simp only [Semiformula.eval_exsClosure, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_neg, eval_substConst]
  exact Iff.rfl

/-- The constants of a conjunction are those of the two conjuncts. -/
theorem constSupport_and {m : ℕ} (φ φ' : Semiformula (LSetC C) Empty m) :
    constSupport (φ ⋏ φ') = constSupport φ ++ constSupport φ' := rfl

end Xi

/-! ## Filling the parameter slot, and the two vector layouts -/

section Subst

variable {M : Type u} [SetStructure M] [Nonempty M] {N : Type v} [SetStructure N] {p : ℕ}

/-- The substitution that fills slot `0` of a formula of arity `1 + p` with the parameter `&a`
and leaves the `p` block slots where they are, in a context of arity `0 + p`. -/
def paramSubst (p : ℕ) (a : M) : Fin (1 + p) → Semiterm ℒₛₑₜ M (0 + p) :=
  Fin.addCases (fun _ : Fin 1 ↦ &a) (fun i : Fin p ↦ #(Fin.natAdd 0 i))

omit [SetStructure M] [Nonempty M] in
theorem eval_paramSubst (A : SetTheorySemiformula M (1 + p)) (a : M) (s : Fin p → N)
    (e : M → N) :
    Semiformula.Eval (Fin.addCases ![] s) e (A ⇜ paramSubst p a)
      ↔ Semiformula.Eval (Fin.addCases ![e a] s) e A := by
  rw [Semiformula.eval_substs]
  have h : (Semiterm.val (s := SetTheory.standardStructure N) (Fin.addCases ![] s) e ∘
      paramSubst p a) = Fin.addCases ![e a] s := by
    funext i
    induction i using Fin.addCases with
    | left j =>
      simp only [Function.comp_apply, paramSubst, Fin.addCases_left, Semiterm.val_fvar,
        Matrix.cons_val_fin_one]
    | right j =>
      simp only [Function.comp_apply, paramSubst, Fin.addCases_right, Semiterm.val_bvar]
  rw [h]

/-- The substitution between the two layouts of a context of arity `1 + p`: the parameter at slot
`0` with the block above it, as `ZFVP.abstractFormula` produces it, and the block at the low slots
with the parameter above it, as the body of `ZFVP.blockAllFormula` is read. -/
def swapSubst (M : Type u) [SetStructure M] (p : ℕ) : Fin (1 + p) → Semiterm ℒₛₑₜ M (1 + p) :=
  Fin.addCases (fun _ : Fin 1 ↦ #((0 : Fin 1).addNat p)) (fun i : Fin p ↦ #(i.addCast 1))

omit [Nonempty M] in
theorem eval_swapSubst (A : SetTheorySemiformula M (1 + p)) (v : M) (s : Fin p → M) :
    Semiformula.Eval (Matrix.appendr s ![v]) id (A ⇜ swapSubst M p)
      ↔ Semiformula.Eval (Fin.addCases ![v] s) id A := by
  rw [Semiformula.eval_substs]
  have h : (Semiterm.val (s := SetTheory.standardStructure M) (Matrix.appendr s ![v]) id ∘
      swapSubst M p) = Fin.addCases ![v] s := by
    funext i
    induction i using Fin.addCases with
    | left j =>
      simp only [Function.comp_apply, swapSubst, Fin.addCases_left, Semiterm.val_bvar,
        Matrix.appeendr_addNat, Matrix.cons_val_fin_one]
    | right j =>
      simp only [Function.comp_apply, swapSubst, Fin.addCases_right, Semiterm.val_bvar,
        Matrix.appeendr_addCast]
  rw [h]

end Subst

/-! ## The set `Λ` -/

section BlockAllNot

variable {M : Type u} [SetStructure M] {p : ℕ}

/-- The set of parameters `v` for which some tuple `r⃗` of `D⃗` bounds the failure of `A`: no
tuple `s⃗` of `D⃗` above `r⃗` satisfies `A(v, s⃗)`. This is Enayat's `Λ` (and, at the other formula,
his `Γ`). -/
def blockAllNot (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (ks : Fin p → ℕ) (A : SetTheorySemiformula M (1 + p)) (v : M) : Prop :=
  BlockAll δ ρ p ks fun s ↦ ¬Semiformula.Eval (Fin.addCases ![v] s) id A

/-- `blockAllNot` is definable in `M` with parameters: it is `ZFVP.blockAllFormula` over the
negated body, with the body moved between the two layouts by `ZFVP.swapSubst`. -/
theorem definable_blockAllNot (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2) (ks : Fin p → ℕ) (A : SetTheorySemiformula M (1 + p)) :
    ℒₛₑₜ-predicate[M] (blockAllNot δ ρ ks A) := by
  refine ⟨⟨blockAllFormula δ ρ ks (∼(A ⇜ swapSubst M p)), ?_⟩⟩
  intro w
  have hw : (![w 0] : Fin 1 → M) = w := by
    funext i; rw [Fin.fin_one_eq_zero i]; simp
  have h1 : Semiformula.Eval w id (blockAllFormula δ ρ ks (∼(A ⇜ swapSubst M p)))
      ↔ Semiformula.Eval ![w 0] id (blockAllFormula δ ρ ks (∼(A ⇜ swapSubst M p))) := by
    rw [hw]
  rw [h1, eval_blockAllFormula]
  refine iff_of_eq (congrArg (BlockAll δ ρ p ks) (funext fun s ↦ propext ?_))
  rw [LogicalConnective.HomClass.map_neg, eval_swapSubst]
  exact Iff.rfl

end BlockAllNot

/-! ## The three bodies of Lemma A.4 -/

section Bodies

variable {M : Type u} [SetStructure M] [Nonempty M] {p q : ℕ}

omit [SetStructure M] in
/-- `abstractFormula ks (existsBody θ)` with the parameter slot filled by `&a` is a body, in the
sense of `ZFVP.consistent_insert_iff_blockEx_of_body`, for the sentence `∃x⃗ θ`. -/
theorem isBody_existsBody (θ : Semisentence (LSetC (M ⊕ ℕ)) q) (ks : Fin p → ℕ)
    (hcov : ∀ k : ℕ, Sum.inr k ∈ constSupport (existsBody θ) → ∃ i, ks i = k) (a : M)
    (N : Type u) (instN : SetStructure N) (_hneN : Nonempty N) (c : M ⊕ ℕ → N) :
    Semiformula.Eval (Fin.addCases ![] fun i ↦ c (Sum.inr (ks i))) (fun a' ↦ c (Sum.inl a'))
        (abstractFormula ks (existsBody θ) ⇜ paramSubst p a)
      ↔ Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim (∃¹* θ) := by
  refine Iff.trans (eval_paramSubst _ a _ (fun a' ↦ c (Sum.inl a'))) ?_
  refine Iff.trans (eval_abstractFormula c ks ![c (Sum.inl a)] (existsBody θ) hcov) ?_
  exact (eval_existsBody c θ (c (Sum.inl a))).trans (eval_exsClosure_self c θ).symm

omit [SetStructure M] in
/-- The same for the sentence `∃x⃗ (θ ⋏ ψ(ȧ, x⃗))`. -/
theorem isBody_existsSat (θ : Semisentence (LSetC (M ⊕ ℕ)) q)
    (ψ : Semisentence (LSetC (M ⊕ ℕ)) (q + 1)) (ks : Fin p → ℕ)
    (hcov : ∀ k : ℕ, Sum.inr k ∈ constSupport (existsSat θ ψ) → ∃ i, ks i = k) (a : M)
    (N : Type u) (instN : SetStructure N) (_hneN : Nonempty N) (c : M ⊕ ℕ → N) :
    Semiformula.Eval (Fin.addCases ![] fun i ↦ c (Sum.inr (ks i))) (fun a' ↦ c (Sum.inl a'))
        (abstractFormula ks (existsSat θ ψ) ⇜ paramSubst p a)
      ↔ Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim
          (∃¹* (θ ⋏ substConst ψ (Sum.inl a))) := by
  refine Iff.trans (eval_paramSubst _ a _ (fun a' ↦ c (Sum.inl a'))) ?_
  refine Iff.trans (eval_abstractFormula c ks ![c (Sum.inl a)] (existsSat θ ψ) hcov) ?_
  exact (eval_existsSat c θ ψ (c (Sum.inl a))).trans
    (eval_exsClosure_and c θ ψ (Sum.inl a)).symm

omit [SetStructure M] in
/-- The same for the sentence `∃x⃗ (θ ⋏ ∼ψ(ȧ, x⃗))`. -/
theorem isBody_existsNotSat (θ : Semisentence (LSetC (M ⊕ ℕ)) q)
    (ψ : Semisentence (LSetC (M ⊕ ℕ)) (q + 1)) (ks : Fin p → ℕ)
    (hcov : ∀ k : ℕ, Sum.inr k ∈ constSupport (existsNotSat θ ψ) → ∃ i, ks i = k) (a : M)
    (N : Type u) (instN : SetStructure N) (_hneN : Nonempty N) (c : M ⊕ ℕ → N) :
    Semiformula.Eval (Fin.addCases ![] fun i ↦ c (Sum.inr (ks i))) (fun a' ↦ c (Sum.inl a'))
        (abstractFormula ks (existsNotSat θ ψ) ⇜ paramSubst p a)
      ↔ Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim
          (∃¹* (θ ⋏ ∼substConst ψ (Sum.inl a))) := by
  refine Iff.trans (eval_paramSubst _ a _ (fun a' ↦ c (Sum.inl a'))) ?_
  refine Iff.trans (eval_abstractFormula c ks ![c (Sum.inl a)] (existsNotSat θ ψ) hcov) ?_
  exact (eval_existsNotSat c θ ψ (c (Sum.inl a))).trans
    (eval_exsClosure_and_neg c θ ψ (Sum.inl a)).symm

end Bodies

/-! ## Lemma A.5 -/

/-- Enayat's Lemma A.5: for a countable `M`, inseparable pairs `{V n, W n}` and definable directed
sets `D n` with no last element, the theory `T` of Lemma A.2 locally omits every separating type
`Σ^ψ_n`. -/
theorem separatingTypesLocallyOmitted : SeparatingTypesLocallyOmitted.{u} := by
  intro M _ _ _ δ ρ V W hins hdir n q ψ θ hθ
  classical
  by_contra hcon
  have hno : ∀ σ ∈ separatingType (V n) (W n) ψ,
      ¬Entailment.Consistent (insert (∃¹* (θ ⋏ ∼σ)) (rubinTheory δ ρ)) :=
    fun σ hσ h ↦ hcon ⟨σ, hσ, h⟩
  -- one family of indices for both formulas and for `∃x⃗ θ`
  obtain ⟨p, ks, hinj, hcov⟩ :=
    exists_indices (existsNotSat θ ψ ⋏ (existsSat θ ψ ⋏ existsBody θ))
  have hcovN : ∀ k : ℕ, Sum.inr k ∈ constSupport (existsNotSat θ ψ) → ∃ i, ks i = k := by
    intro k hk
    refine hcov k ?_
    rw [constSupport_and]
    exact List.mem_append_left _ hk
  have hcovS : ∀ k : ℕ, Sum.inr k ∈ constSupport (existsSat θ ψ) → ∃ i, ks i = k := by
    intro k hk
    refine hcov k ?_
    rw [constSupport_and]
    refine List.mem_append_right _ ?_
    rw [constSupport_and]
    exact List.mem_append_left _ hk
  have hcovB : ∀ k : ℕ, Sum.inr k ∈ constSupport (existsBody θ) → ∃ i, ks i = k := by
    intro k hk
    refine hcov k ?_
    rw [constSupport_and]
    refine List.mem_append_right _ ?_
    rw [constSupport_and]
    exact List.mem_append_right _ hk
  -- `V n ⊆ Λ`
  have hVΛ : ∀ a, V n a → blockAllNot δ ρ ks (abstractFormula ks (existsNotSat θ ψ)) a := by
    intro a ha
    have h1 := hno _ (Or.inl ⟨a, ha, rfl⟩)
    have h2 := consistent_insert_iff_blockEx_of_body hdir
      (∃¹* (θ ⋏ ∼substConst ψ (Sum.inl a))) hinj
      (abstractFormula ks (existsNotSat θ ψ) ⇜ paramSubst p a)
      (isBody_existsNotSat θ ψ ks hcovN a)
    rw [h2, not_blockEx_iff] at h1
    exact BlockAll.mono δ ρ (fun t ht hc ↦ ht ((eval_paramSubst _ a t id).mpr hc)) h1
  -- `W n ⊆ Γ`
  have hWΓ : ∀ b, W n b → blockAllNot δ ρ ks (abstractFormula ks (existsSat θ ψ)) b := by
    intro b hb
    have h1 := hno _ (Or.inr ⟨b, hb, rfl⟩)
    rw [show (∼(∼substConst ψ (Sum.inl b))) = substConst ψ (Sum.inl b) from by simp] at h1
    have h2 := consistent_insert_iff_blockEx_of_body hdir
      (∃¹* (θ ⋏ substConst ψ (Sum.inl b))) hinj
      (abstractFormula ks (existsSat θ ψ) ⇜ paramSubst p b)
      (isBody_existsSat θ ψ ks hcovS b)
    rw [h2, not_blockEx_iff] at h1
    exact BlockAll.mono δ ρ (fun t ht hc ↦ ht ((eval_paramSubst _ b t id).mpr hc)) h1
  -- the block coming from the consistency of `insert (∃x⃗ θ) T`
  have hEx : BlockEx δ ρ p ks fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id
      (abstractFormula ks (existsBody θ) ⇜ paramSubst p (Classical.arbitrary M)) :=
    (consistent_insert_iff_blockEx_of_body hdir (∃¹* θ) hinj
      (abstractFormula ks (existsBody θ) ⇜ paramSubst p (Classical.arbitrary M))
      (isBody_existsBody θ ks hcovB (Classical.arbitrary M))).mp hθ
  -- `Λ` and `Γ` are disjoint
  have hdisj : ∀ v, blockAllNot δ ρ ks (abstractFormula ks (existsNotSat θ ψ)) v →
      blockAllNot δ ρ ks (abstractFormula ks (existsSat θ ψ)) v → False := by
    intro v hΛ hΓ
    refine blockAll_blockEx_contradiction δ ρ (BlockAll.and δ ρ hdir hΛ hΓ) hEx ?_
    rintro s ⟨h1, h2⟩ h3
    obtain ⟨c, hcl, hcr⟩ := exists_assign_of_injective hinj s
    have hks : (fun i ↦ c (Sum.inr (ks i))) = s := funext hcr
    have hid : (fun a : M ↦ c (Sum.inl a)) = id := funext hcl
    have eN := eval_abstractFormula c ks ![v] (existsNotSat θ ψ) hcovN
    have eS := eval_abstractFormula c ks ![v] (existsSat θ ψ) hcovS
    have eB := eval_abstractFormula c ks ![Classical.arbitrary M] (existsBody θ) hcovB
    rw [hks, hid] at eN eS eB
    have hx : ∃ x : Fin q → M, Semiformula.Eval (s := setConstStructure M c) x Empty.elim θ :=
      (eval_existsBody c θ (Classical.arbitrary M)).mp
        (eB.mp ((eval_paramSubst _ (Classical.arbitrary M) s id).mp h3))
    obtain ⟨x, hxθ⟩ := hx
    by_cases hψ : Semiformula.Eval (s := setConstStructure M c) (v :> x) Empty.elim ψ
    · exact h2 (eS.mpr ((eval_existsSat c θ ψ v).mpr ⟨x, hxθ, hψ⟩))
    · exact h1 (eN.mpr ((eval_existsNotSat c θ ψ v).mpr ⟨x, hxθ, hψ⟩))
  -- `Λ` would separate `V n` from `W n`
  obtain ⟨v, hWv, hΛv⟩ := (hins n).meets _
    (definable_blockAllNot δ ρ ks (abstractFormula ks (existsNotSat θ ψ))) hVΛ
  exact hdisj v hΛv (hWΓ v hWv)

/-- Enayat's Lemma A.2, unconditionally: given a countable model `M`, countably many pairs of
inseparable subsets and countably many definable directed sets with no last element, there is a
countable elementary extension in which the pairs are still inseparable and each directed set has
an element above all of its old elements. -/
theorem exists_elementary_extension_inseparable_upper_bounds' (M : Type u) [SetStructure M]
    [Nonempty M] [Countable M] (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2) (V W : ℕ → M → Prop)
    (hins : ∀ n, Inseparable M (V n) (W n))
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) :
    Nonempty (InseparableUpperBoundExtension M δ ρ V W) :=
  exists_elementary_extension_inseparable_upper_bounds_of_a5 separatingTypesLocallyOmitted.{u}
    M δ ρ V W hins hdir

end ZFVP
