import ZFVP.ModelTheory.AlternatingBlocks
import ZFVP.ModelTheory.ConstantAbstraction
import ZFVP.ModelTheory.OmittingTypesEq

/-! # Enayat's Lemma A.4 in block form

Enayat's Lemma A.4 reads consistency with the theory `T` of Lemma A.2 of a sentence
`σ(d_{k₁}, …, d_{k_p})` off a statement about `M`:

`insert σ T` is consistent iff `M ⊨ ∀r⃗ ∈ D⃗ ∃s⃗ ∈ D⃗ [(⋀ᵢ rᵢ <_{D_{k_i}} sᵢ) ∧ σ(s⃗)]`.

The quantifier prefix is the block one, `BlockEx`, not the alternating one the paper prints; the
header of `ZFVP.ModelTheory.AlternatingBlocks` has the counterexample to the alternating reading.

The two directions are `consistent_insert_of_blockEx` and `blockEx_of_consistent_insert`, and
`consistent_insert_iff_blockEx` is the iff.

The right-hand side is `BlockEx δ ρ p ks` over the body
`fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id (abstractFormula ks σ)`, which by
`ZFVP.eval_abstractFormula` is "`σ` holds in `M` when `d_{ks i}` names `s i`".

The proof uses the concrete body only through `ZFVP.eval_abstractFormula`, so it is carried out
for an arbitrary formula `X` of arity `0 + p` with that evaluation property, which is what
`consistent_insert_of_blockEx_of_body`, `blockEx_of_consistent_insert_of_body` and
`consistent_insert_iff_blockEx_of_body` take as the hypothesis `hX`. A caller that reaches `σ` by
a substitution can then supply its own `X` instead of computing `constSupport σ`. The three
versions with `abstractFormula ks σ` as the body follow, with the covering hypothesis `hcov`.

What this file adds on the way:

* `ElementaryMap.eval_param`, the missing form of elementarity. `ElementaryMap.elementary` only
  accepts formulas whose free variables live in `Type 0`, and the formulas here carry parameters
  from `M : Type u`. The parameters are pushed through `ℕ` by `Semiformula.idxOfFVar` and
  `Semiformula.enumerateFVar`.
* `dltFvarGuard` and `notBodyFormula`, the formula that says, of a fixed tuple `r⃗` of parameters,
  that no tuple `s⃗` of `D⃗` above `r⃗` satisfies `σ`. This is the statement that gets transferred
  from `M` to the model of `T`. Its `s` block leaves the assignment `Matrix.appendr s ![]`, which
  `appendr_eq_addCases` identifies with `Fin.addCases ![] s`, the layout `abstractFormula` uses.
* `locallyOmits_bot` and `exists_normalModel_of_consistent`: a consistent theory over
  `LSetC C` with `C` encodable that contains the equality axioms has a countable set-structure
  model with an assignment of the constants. The omitting types theorem for languages with
  equality is applied to the single type `{⊥}`, which every structure omits, so nothing is really
  omitted and only the countable normal model is used.

Enayat's Lemma A.3 is not proved here. It is A.4 applied to `∼σ`, so it needs
`abstractFormula ks (∼σ) = ∼abstractFormula ks σ` and `constSupport (∼σ) = constSupport σ`, two
inductions on the formula, plus the passage between "`T ⊢ σ`" and "`insert (∼σ) T` is
inconsistent". Nothing downstream uses it.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v

/-! ## Elementarity for formulas with parameters in an arbitrary universe -/

/-- Elementarity of `j` for a formula whose free variables are elements of `M`. The structure
`ElementaryMap` only asks for formulas with free variables in a `Type 0`, so the parameters are
first renamed to natural numbers by `Semiformula.idxOfFVar` and read back by
`Semiformula.enumerateFVar`. -/
theorem ElementaryMap.eval_param {M : Type u} [SetStructure M] [Nonempty M] {N : Type v}
    [SetStructure N] (j : ElementaryMap M N) {n : ℕ} (φ : SetTheorySemiformula M n)
    (b : Fin n → M) : φ.Eval b id ↔ φ.Eval (fun i ↦ j (b i)) (fun a ↦ j a) := by
  classical
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  have h1 : φ.Eval b id ↔ φ.Eval b (fun x ↦ φ.enumerateFVar (φ.idxOfFVar x)) :=
    (Semiformula.eval_enumerateFVar_idxOfFVar_eq_id φ b).symm
  have h2 : Semiformula.Eval b φ.enumerateFVar (Rew.rewriteMap φ.idxOfFVar ▹ φ)
      ↔ φ.Eval b (fun x ↦ φ.enumerateFVar (φ.idxOfFVar x)) :=
    Semiformula.eval_rewriteMap _ _
  have h3 := j.elementary (Rew.rewriteMap φ.idxOfFVar ▹ φ) b φ.enumerateFVar
  have h4 : Semiformula.Eval (j.toFun ∘ b) (j.toFun ∘ φ.enumerateFVar)
      (Rew.rewriteMap φ.idxOfFVar ▹ φ)
      ↔ φ.Eval (j.toFun ∘ b) (fun x ↦ j.toFun (φ.enumerateFVar (φ.idxOfFVar x))) :=
    Semiformula.eval_rewriteMap _ _
  have h5 : φ.Eval (j.toFun ∘ b) (fun x ↦ j.toFun (φ.enumerateFVar (φ.idxOfFVar x)))
      ↔ φ.Eval (j.toFun ∘ b) (fun a ↦ j a) := by
    refine Semiformula.eval_iff_of_funEqOn φ ?_
    intro x hx
    simp only [Semiformula.enumerateFVar_idxOfFVar (Semiformula.mem_fvarList_iff_fvar?.mpr hx)]
  exact h1.trans (h2.symm.trans (h3.trans (h4.trans h5)))

/-! ## The two vector layouts at arity zero -/

/-- The assignment a block of `p` quantifiers leaves over an empty context is the assignment
`ZFVP.abstractFormula` expects: the `p` values in the low slots. -/
theorem appendr_eq_addCases {N : Type v} {p : ℕ} (s : Fin p → N) (b : Fin 0 → N) :
    Matrix.appendr s b = Fin.addCases (motive := fun _ ↦ N) ![] s := by
  funext i
  refine Fin.addCases
    (motive := fun i ↦ Matrix.appendr s b i = Fin.addCases (motive := fun _ ↦ N) ![] s i)
    (fun j ↦ j.elim0) (fun j ↦ ?_) i
  rw [Fin.addCases_right, show Fin.natAdd 0 j = j.addCast 0 from Fin.ext (by simp),
    Matrix.appeendr_addCast]

/-- The `i`-th slot of that assignment. -/
theorem addCases_addCast_zero {N : Type v} {p : ℕ} (s : Fin p → N) (i : Fin p) :
    Fin.addCases (motive := fun _ ↦ N) ![] s (i.addCast 0) = s i := by
  rw [← appendr_eq_addCases s ![], Matrix.appeendr_addCast]

/-! ## The guards with a parameter on the left -/

section Guards

variable {M : Type u} [SetStructure M] {N : Type v} [SetStructure N]

omit [SetStructure M] in
/-- The evaluation of `ZFVP.dsetGuard` under an arbitrary assignment of the parameters. -/
theorem eval_dsetGuard_param (δ : ℕ → SetTheorySemiformula M 1) {p m : ℕ} (ks : Fin p → ℕ)
    (v : Fin p → Fin m) (b : Fin m → N) (e : M → N) :
    Semiformula.Eval b e (dsetGuard δ ks v) ↔ ∀ i, (δ (ks i)).Eval ![b (v i)] e := by
  simp only [dsetGuard, Matrix.conj_hom_prop, Semiformula.eval_substs]
  refine forall_congr' fun i ↦ ?_
  have h : (Semiterm.val (s := SetTheory.standardStructure N) b e ∘ ![#(v i)]) = ![b (v i)] := by
    funext k; exact Fin.cases rfl (fun j ↦ j.elim0) k
  rw [h]

/-- The conjunction `⋀ᵢ (rᵢ <_{D_{k_i}} x_{w i})` with the left argument of each conjunct a fixed
parameter `r i` and the right one the variable `#(w i)`. -/
def dltFvarGuard (ρ : ℕ → SetTheorySemiformula M 2) {p : ℕ} (ks : Fin p → ℕ) (r : Fin p → M)
    {m : ℕ} (w : Fin p → Fin m) : SetTheorySemiformula M m :=
  Matrix.conj fun i ↦ ρ (ks i) ⇜ ![&(r i), #(w i)]

omit [SetStructure M] in
theorem eval_dltFvarGuard (ρ : ℕ → SetTheorySemiformula M 2) {p m : ℕ} (ks : Fin p → ℕ)
    (r : Fin p → M) (w : Fin p → Fin m) (b : Fin m → N) (e : M → N) :
    Semiformula.Eval b e (dltFvarGuard ρ ks r w) ↔
      ∀ i, (ρ (ks i)).Eval ![e (r i), b (w i)] e := by
  simp only [dltFvarGuard, Matrix.conj_hom_prop, Semiformula.eval_substs]
  refine forall_congr' fun i ↦ ?_
  have h : (Semiterm.val (s := SetTheory.standardStructure N) b e ∘ ![&(r i), #(w i)])
      = ![e (r i), b (w i)] := by
    funext k
    exact Fin.cases rfl (fun l ↦ Fin.cases rfl (fun m ↦ m.elim0) l) k
  rw [h]

end Guards

/-! ## The formula that says "no tuple above `r⃗` satisfies `σ`" -/

section NotBody

variable {M : Type u} [SetStructure M] [Nonempty M] {N : Type v} [SetStructure N]

/-- With `r⃗` as parameters: every tuple `s⃗` with `s i ∈ D_{k_i}` and `r i <_{D_{k_i}} s i` fails
the body `X`. -/
def notBodyFormulaOf (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2) {p : ℕ} (ks : Fin p → ℕ) (r : Fin p → M)
    (X : SetTheorySemiformula M (0 + p)) : SetTheorySemiformula M 0 :=
  ∀¹^[p] ((dsetGuard δ ks (fun i ↦ i.addCast 0) ⋏ dltFvarGuard ρ ks r (fun i ↦ i.addCast 0)) 🡒
    ∼X)

/-- With `r⃗` as parameters: every tuple `s⃗` with `s i ∈ D_{k_i}` and `r i <_{D_{k_i}} s i` fails
`σ`, read through `ZFVP.abstractFormula`. -/
noncomputable def notBodyFormula (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2) {p : ℕ} (ks : Fin p → ℕ) (r : Fin p → M)
    (σ : Sentence (LSetC (M ⊕ ℕ))) : SetTheorySemiformula M 0 :=
  notBodyFormulaOf δ ρ ks r (abstractFormula ks σ)

omit [SetStructure M] [Nonempty M] in
theorem eval_notBodyFormulaOf (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2) {p : ℕ} (ks : Fin p → ℕ) (r : Fin p → M)
    (X : SetTheorySemiformula M (0 + p)) (b : Fin 0 → N) (e : M → N) :
    Semiformula.Eval b e (notBodyFormulaOf δ ρ ks r X) ↔
      ∀ s : Fin p → N, (∀ i, (δ (ks i)).Eval ![s i] e) →
        (∀ i, (ρ (ks i)).Eval ![e (r i), s i] e) →
          ¬Semiformula.Eval (Fin.addCases ![] s) e X := by
  simp only [notBodyFormulaOf, Semiformula.eval_allItr, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
    eval_dsetGuard_param, eval_dltFvarGuard, appendr_eq_addCases, addCases_addCast_zero]
  exact forall_congr' fun s ↦ and_imp

omit [SetStructure M] in
theorem eval_notBodyFormula (δ : ℕ → SetTheorySemiformula M 1)
    (ρ : ℕ → SetTheorySemiformula M 2) {p : ℕ} (ks : Fin p → ℕ) (r : Fin p → M)
    (σ : Sentence (LSetC (M ⊕ ℕ))) (b : Fin 0 → N) (e : M → N) :
    Semiformula.Eval b e (notBodyFormula δ ρ ks r σ) ↔
      ∀ s : Fin p → N, (∀ i, (δ (ks i)).Eval ![s i] e) →
        (∀ i, (ρ (ks i)).Eval ![e (r i), s i] e) →
          ¬Semiformula.Eval (Fin.addCases ![] s) e (abstractFormula ks σ) :=
  eval_notBodyFormulaOf δ ρ ks r (abstractFormula ks σ) b e

end NotBody

/-! ## A countable normal model of a consistent theory -/

/-- Every structure omits the type `{⊥}`, so every theory locally omits it. This is the type fed
to the omitting types theorem when only its countable model is wanted. -/
theorem locallyOmits_bot {L : Language.{u}} (T : Theory L) {q : ℕ} :
    LocallyOmits T ({⊥} : PartialType L q) := by
  intro θ hθ
  refine ⟨⊥, rfl, ?_⟩
  have := hθ
  obtain ⟨N, _, _, hN⟩ :=
    LO.FirstOrder.satisfiable_iff.mp (Theory.small_satisfiable_of_consistent hθ)
  have hTN : N↓[L] ⊧* T :=
    Semantics.modelsSet_iff.mpr fun {_} h ↦
      Semantics.modelsSet_iff.mp hN (Set.mem_insert_of_mem _ h)
  have h1 : N↓[L] ⊧ (∃¹* θ : Sentence L) :=
    Semantics.modelsSet_iff.mp hN (Set.mem_insert _ _)
  refine consistent_insert_of_model N ?_
  simp only [models_iff, Semiformula.eval_exsClosure] at h1 ⊢
  obtain ⟨e, he⟩ := h1
  exact ⟨e, he, trivial⟩

/-- A consistent theory over `LSetC C`, with `C` encodable, that contains the equality axioms has
a countable model that is a set structure with an assignment of the constants. -/
theorem exists_normalModel_of_consistent {C : Type u} [Encodable C] (T : Theory (LSetC C))
    (hEQ : 𝗘𝗤 (LSetC C) ⊆ T) (hT : Entailment.Consistent T) :
    Nonempty (NormalModel C T (ι := ℕ) (qi := fun _ ↦ 0)
      fun _ ↦ ({⊥} : PartialType (LSetC C) 0)) := by
  obtain ⟨Om⟩ := omittingTypesTheoremEq (LSetC C) T hEQ hT (fun _ ↦ 0)
    (fun _ ↦ ({⊥} : PartialType (LSetC C) 0)) fun _ ↦ locallyOmits_bot T
  exact exists_normalModel T hEQ _ Om.Dom Om.models Om.omits

/-! ## Lemma A.4 -/

section LemmaA4

variable {M : Type u} [SetStructure M] [Nonempty M] {δ : ℕ → SetTheorySemiformula M 1}
  {ρ : ℕ → SetTheorySemiformula M 2}

/-- The easy direction of Lemma A.4 over an arbitrary body: the block statement makes
`insert σ T` finitely satisfiable in `M`. A finite part of the theory mentions finitely many
sentences `ṁ <_{D_n} d_n`; the constants `d_{ks i}` are interpreted by a tuple `s⃗` produced by
the block above all of those `m`, and the remaining `d_n` by a plain upper bound. Injectivity of
`ks` is what makes the assignment give `s i` back at the index `ks i`.

The body `X` is any formula of `ℒₛₑₜ` with parameters from `M` whose truth at the tuple
`fun i ↦ c (Sum.inr (ks i))` is the truth of `σ` under the assignment `c` of the constants, which
is what `hX` says and what `ZFVP.eval_abstractFormula` proves of `abstractFormula ks σ`. -/
theorem consistent_insert_of_blockEx_of_body (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n))
    (σ : Sentence (LSetC (M ⊕ ℕ))) {p : ℕ} {ks : Fin p → ℕ} (hinj : Function.Injective ks)
    (X : SetTheorySemiformula M (0 + p))
    (hX : ∀ (N : Type u) (_ : SetStructure N) (_ : Nonempty N) (c : M ⊕ ℕ → N),
      Semiformula.Eval (Fin.addCases ![] fun i ↦ c (Sum.inr (ks i)))
          (fun a ↦ c (Sum.inl a)) X
        ↔ Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim σ)
    (hblock : BlockEx δ ρ p ks fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id X) :
    Entailment.Consistent (insert σ (rubinTheory δ ρ)) := by
  classical
  refine Theory.consistent_of_satisfiable (compact.mpr ?_)
  intro u hu
  set P : Sentence (LSetC (M ⊕ ℕ)) → Prop :=
    fun τ ↦ ∃ q : ℕ × M, dset δ q.1 q.2 ∧ τ = boundSentence ρ q.1 q.2 with hP
  set dec : Sentence (LSetC (M ⊕ ℕ)) → ℕ × M :=
    fun τ ↦ if h : P τ then h.choose else (0, Classical.arbitrary M) with hdec
  have hdecSpec : ∀ τ, P τ →
      dset δ (dec τ).1 (dec τ).2 ∧ τ = boundSentence ρ (dec τ).1 (dec τ).2 := by
    intro τ h
    rw [hdec]
    simp only [h, ↓reduceDIte]
    exact h.choose_spec
  set pairs : Finset (ℕ × M) := (u.filter P).image dec with hpairs
  set A : ℕ → Finset M :=
    fun n ↦ (pairs.filter (fun q ↦ q.1 = n ∧ dset δ n q.2)).image Prod.snd with hAdef
  have hA : ∀ n, ∀ m ∈ A n, dset δ n m := by
    intro n m hm
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_filter.mp hq).2.2
  obtain ⟨s, hs, hslt, hbody⟩ :=
    blockEx_upper δ ρ hdir hblock (fun i ↦ A (ks i)) fun i m hm ↦ hA (ks i) m hm
  choose d hd using fun n ↦ (hdir n).exists_upper_bound (A n) (hA n)
  set g : ℕ → M := fun n ↦ if h : ∃ i, ks i = n then s (Classical.choose h) else d n with hg
  have hgks : ∀ i, g (ks i) = s i := by
    intro i
    have hex : ∃ i', ks i' = ks i := ⟨i, rfl⟩
    have h1 : g (ks i) = s (Classical.choose hex) := by rw [hg]; exact dite_eq_left hex
    have h2 : Classical.choose hex = i := hinj (Classical.choose_spec hex)
    rw [h1, h2]
  have hgspec : ∀ n, dset δ n (g n) ∧ ∀ m ∈ A n, dlt ρ n m (g n) := by
    intro n
    by_cases hex : ∃ i, ks i = n
    · obtain ⟨i₀, hi1, hi2⟩ : ∃ i₀, ks i₀ = n ∧ g n = s i₀ :=
        ⟨Classical.choose hex, Classical.choose_spec hex, by rw [hg]; exact dite_eq_left hex⟩
      clear hex
      subst hi1
      rw [hi2]
      exact ⟨hs i₀, hslt i₀⟩
    · have h1 : g n = d n := by rw [hg]; exact dite_eq_right hex
      rw [h1]
      exact hd n
  set c : M ⊕ ℕ → M := Sum.elim id g with hc
  have hcl : ∀ m : M, c (Sum.inl m) = m := fun _ ↦ rfl
  have hcomp : (c ∘ Sum.inl) = (id : M → M) := funext hcl
  have hcr : ∀ n, c (Sum.inr n) = g n := fun _ ↦ rfl
  refine ⟨(setConstStructure M c).toStruc, Semantics.modelsSet_iff.mpr ?_⟩
  intro τ hτu
  rcases hu hτu with rfl | hτ
  · refine (hX M inferInstance inferInstance c).mp ?_
    have h1 : (fun i ↦ c (Sum.inr (ks i))) = s := funext fun i ↦ by rw [hcr]; exact hgks i
    have h2 : (fun a : M ↦ c (Sum.inl a)) = id := funext hcl
    rw [h1, h2]
    exact hbody
  · rcases hτ with ((hτ | hτ) | ⟨n, rfl⟩) | hτ
    · exact Semantics.modelsSet_iff.mp (models_sumDiagram_self c hcl) hτ
    · exact Semantics.modelsSet_iff.mp (models_eqAxiom_setConstStructure M c) hτ
    · refine (eval_memberSentence c n).mpr ?_
      rw [hcomp, hcr]
      exact (hgspec n).1
    · have hPτ : P τ := by
        obtain ⟨n, m, h1, h2⟩ := hτ
        exact ⟨(n, m), h1, h2⟩
      obtain ⟨hdset, hform⟩ := hdecSpec τ hPτ
      have hmem : (dec τ).2 ∈ A (dec τ).1 := by
        refine Finset.mem_image.mpr ⟨dec τ, Finset.mem_filter.mpr ⟨?_, rfl, hdset⟩, rfl⟩
        exact Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hτu, hPτ⟩, rfl⟩
      rw [hform]
      refine (eval_boundSentence c (dec τ).1 (dec τ).2).mpr ?_
      rw [hcomp, hcr]
      exact (hgspec (dec τ).1).2 _ hmem

/-- The hard direction of Lemma A.4 over an arbitrary body, by contraposition. A failure of the
block statement gives a tuple `r⃗` in `M` such that no tuple of `D⃗` above `r⃗` satisfies the body.
That is a single `ℒₛₑₜ`-formula with the `r i` as parameters, so it transfers to any elementary
extension of `M`; in a model of `insert σ T` the constants `d_{ks i}` name such a tuple, and `σ`
holds of it. -/
theorem blockEx_of_consistent_insert_of_body [Countable M]
    (σ : Sentence (LSetC (M ⊕ ℕ))) {p : ℕ} {ks : Fin p → ℕ}
    (X : SetTheorySemiformula M (0 + p))
    (hX : ∀ (N : Type u) (_ : SetStructure N) (_ : Nonempty N) (c : M ⊕ ℕ → N),
      Semiformula.Eval (Fin.addCases ![] fun i ↦ c (Sum.inr (ks i)))
          (fun a ↦ c (Sum.inl a)) X
        ↔ Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim σ)
    (hcon : Entailment.Consistent (insert σ (rubinTheory δ ρ))) :
    BlockEx δ ρ p ks fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id X := by
  classical
  by_contra hnb
  rw [not_blockEx_iff] at hnb
  obtain ⟨r, hr, hall⟩ := hnb
  have : Encodable M := Encodable.ofCountable M
  obtain ⟨NM⟩ := exists_normalModel_of_consistent (insert σ (rubinTheory δ ρ))
    (fun {_} h ↦ Set.mem_insert_of_mem _ (eqAxiom_subset_rubinTheory h)) hcon
  have hT : (setConstStructure NM.Dom NM.assign).toStruc ⊧* rubinTheory δ ρ :=
    Semantics.modelsSet_iff.mpr fun {_} h ↦
      Semantics.modelsSet_iff.mp NM.models (Set.mem_insert_of_mem _ h)
  have hσN : Semiformula.Eval (s := setConstStructure NM.Dom NM.assign) ![] Empty.elim σ :=
    Semantics.modelsSet_iff.mp NM.models (Set.mem_insert _ _)
  obtain ⟨j, hj⟩ := elementaryMap_of_models_rubinTheory NM.assign hT
  have hjc : (fun a : M ↦ j a) = NM.assign ∘ Sum.inl := funext hj
  -- the failure of the block statement, as a formula with the `r i` as parameters
  have hΘ : Semiformula.Eval (![] : Fin 0 → M) id (notBodyFormulaOf δ ρ ks r X) := by
    rw [eval_notBodyFormulaOf]
    intro t ht hlt hb
    exact hall t ht hlt hb
  have hΘN := (ElementaryMap.eval_param j (notBodyFormulaOf δ ρ ks r X) ![]).mp hΘ
  rw [eval_notBodyFormulaOf] at hΘN
  refine hΘN (fun i ↦ NM.assign (Sum.inr (ks i))) (fun i ↦ ?_) (fun i ↦ ?_) ?_
  · obtain ⟨hmem, -⟩ := upperBound_of_models_rubinTheory NM.assign hT (ks i)
    rw [hjc]
    exact hmem
  · obtain ⟨-, hbound⟩ := upperBound_of_models_rubinTheory NM.assign hT (ks i)
    rw [hjc, hj (r i)]
    exact hbound (r i) (hr i)
  · rw [hjc]
    exact (hX NM.Dom inferInstance inferInstance NM.assign).mpr hσN

/-- Enayat's Lemma A.4 over an arbitrary body: `insert σ T` is consistent exactly when `M`
satisfies `∀r⃗ ∈ D⃗ ∃s⃗ ∈ D⃗ [(⋀ᵢ rᵢ <_{D_{k_i}} sᵢ) ∧ X(s⃗)]`, for any formula `X` reading `σ`
off the tuple of values of the constants `d_{ks i}`. -/
theorem consistent_insert_iff_blockEx_of_body (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n))
    [Countable M] (σ : Sentence (LSetC (M ⊕ ℕ))) {p : ℕ} {ks : Fin p → ℕ}
    (hinj : Function.Injective ks) (X : SetTheorySemiformula M (0 + p))
    (hX : ∀ (N : Type u) (_ : SetStructure N) (_ : Nonempty N) (c : M ⊕ ℕ → N),
      Semiformula.Eval (Fin.addCases ![] fun i ↦ c (Sum.inr (ks i)))
          (fun a ↦ c (Sum.inl a)) X
        ↔ Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim σ) :
    Entailment.Consistent (insert σ (rubinTheory δ ρ)) ↔
      BlockEx δ ρ p ks fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id X :=
  ⟨blockEx_of_consistent_insert_of_body σ X hX,
    consistent_insert_of_blockEx_of_body hdir σ hinj X hX⟩

/-- The easy direction of Lemma A.4, with `ZFVP.abstractFormula` as the body. -/
theorem consistent_insert_of_blockEx (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n))
    (σ : Sentence (LSetC (M ⊕ ℕ))) {p : ℕ} {ks : Fin p → ℕ} (hinj : Function.Injective ks)
    (hcov : ∀ n : ℕ, Sum.inr n ∈ constSupport σ → ∃ i, ks i = n)
    (hblock : BlockEx δ ρ p ks
      fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id (abstractFormula ks σ)) :
    Entailment.Consistent (insert σ (rubinTheory δ ρ)) :=
  consistent_insert_of_blockEx_of_body hdir σ hinj (abstractFormula ks σ)
    (fun _ _ _ c ↦ eval_abstractFormula c ks ![] σ hcov) hblock

/-- The hard direction of Lemma A.4, with `ZFVP.abstractFormula` as the body. -/
theorem blockEx_of_consistent_insert [Countable M]
    (σ : Sentence (LSetC (M ⊕ ℕ))) {p : ℕ} {ks : Fin p → ℕ}
    (hcov : ∀ n : ℕ, Sum.inr n ∈ constSupport σ → ∃ i, ks i = n)
    (hcon : Entailment.Consistent (insert σ (rubinTheory δ ρ))) :
    BlockEx δ ρ p ks
      fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id (abstractFormula ks σ) :=
  blockEx_of_consistent_insert_of_body σ (abstractFormula ks σ)
    (fun _ _ _ c ↦ eval_abstractFormula c ks ![] σ hcov) hcon

/-- Enayat's Lemma A.4, in the block form: `insert σ T` is consistent exactly when `M` satisfies
`∀r⃗ ∈ D⃗ ∃s⃗ ∈ D⃗ [(⋀ᵢ rᵢ <_{D_{k_i}} sᵢ) ∧ σ(s⃗)]`, where `σ(s⃗)` is `σ` read in `M` with
`d_{ks i}` naming `s i`. -/
theorem consistent_insert_iff_blockEx (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n))
    [Countable M] (σ : Sentence (LSetC (M ⊕ ℕ))) {p : ℕ} {ks : Fin p → ℕ}
    (hinj : Function.Injective ks)
    (hcov : ∀ n : ℕ, Sum.inr n ∈ constSupport σ → ∃ i, ks i = n) :
    Entailment.Consistent (insert σ (rubinTheory δ ρ)) ↔
      BlockEx δ ρ p ks
        fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id (abstractFormula ks σ) :=
  ⟨blockEx_of_consistent_insert σ hcov, consistent_insert_of_blockEx hdir σ hinj hcov⟩

end LemmaA4

/-! ## Lemma A.3

Enayat's Lemma A.3 is Lemma A.4 applied to `∼σ`. Two things are needed to read the result back:
the constants occurring in `∼σ` are those occurring in `σ`, and the body of the block for `∼σ` is
the negation of the body for `σ`. The second one is proved semantically, by naming the tuple `s⃗`
with the constants `d_{ks i}`, which injectivity of `ks` allows. -/

section LemmaA3

/-- Negation does not change which constants occur. -/
theorem constSupport_neg {C : Type u} : ∀ {m : ℕ} (φ : Semiformula (LSetC C) Empty m),
    constSupport (∼φ) = constSupport φ := by
  intro m φ
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
    rcases r with r' | r'
    · rfl
    · exact PEmpty.elim r'
  | hnrel r v =>
    rcases r with r' | r'
    · rfl
    · exact PEmpty.elim r'
  | hand φ ψ ihφ ihψ =>
    rw [show (∼(φ ⋏ ψ)) = ∼φ ⋎ ∼ψ from rfl]
    simp only [constSupport, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    rw [show (∼(φ ⋎ ψ)) = ∼φ ⋏ ∼ψ from rfl]
    simp only [constSupport, ihφ, ihψ]
  | hall φ ih => simp only [Semiformula.neg_all, constSupport, ih]
  | hexs φ ih => simp only [Semiformula.neg_ex, constSupport, ih]

variable {M : Type u} [SetStructure M] [Nonempty M] {δ : ℕ → SetTheorySemiformula M 1}
  {ρ : ℕ → SetTheorySemiformula M 2}

omit [SetStructure M] in
/-- Any tuple `s⃗` indexed by an injective `ks` is named by some assignment of the constants that
names each `m : M` by itself. -/
theorem exists_assign_of_injective {p : ℕ} {ks : Fin p → ℕ} (hinj : Function.Injective ks)
    (s : Fin p → M) :
    ∃ c : M ⊕ ℕ → M, (∀ m, c (Sum.inl m) = m) ∧ ∀ i, c (Sum.inr (ks i)) = s i := by
  classical
  refine ⟨Sum.elim id fun n ↦ if h : ∃ i, ks i = n then s (Classical.choose h)
    else Classical.arbitrary M, fun _ ↦ rfl, fun i ↦ ?_⟩
  have hex : ∃ i', ks i' = ks i := ⟨i, rfl⟩
  show (if h : ∃ i', ks i' = ks i then s (Classical.choose h) else Classical.arbitrary M) = s i
  rw [dite_eq_left hex, hinj (Classical.choose_spec hex)]

/-- The body of the block for `∼σ` is the negation of the body of the block for `σ`. -/
theorem eval_abstractFormula_neg {p : ℕ} {ks : Fin p → ℕ} (hinj : Function.Injective ks)
    (σ : Sentence (LSetC (M ⊕ ℕ)))
    (hcov : ∀ n : ℕ, Sum.inr n ∈ constSupport σ → ∃ i, ks i = n) (s : Fin p → M) :
    Semiformula.Eval (Fin.addCases ![] s) id (abstractFormula ks (∼σ)) ↔
      ¬Semiformula.Eval (Fin.addCases ![] s) id (abstractFormula ks σ) := by
  obtain ⟨c, hcl, hcr⟩ := exists_assign_of_injective hinj s
  have hks : (fun i ↦ c (Sum.inr (ks i))) = s := funext hcr
  have hid : (fun a : M ↦ c (Sum.inl a)) = id := funext hcl
  have hσ := eval_abstractFormula c ks (![] : Fin 0 → M) σ hcov
  have hnσ := eval_abstractFormula c ks (![] : Fin 0 → M) (∼σ)
    (fun n hn ↦ hcov n (by rwa [constSupport_neg] at hn))
  rw [hks, hid] at hσ hnσ
  rw [hσ, hnσ]
  simp only [LogicalConnective.HomClass.map_neg]
  exact Iff.rfl

/-- Enayat's Lemma A.3, in the block form: `T` proves `σ`, that is `insert (∼σ) T` is
inconsistent, exactly when `M` satisfies `∃r⃗ ∈ D⃗ ∀s⃗ ∈ D⃗ [(⋀ᵢ rᵢ <_{D_{k_i}} sᵢ) → σ(s⃗)]`. -/
theorem not_consistent_insert_neg_iff_blockAll
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) [Countable M]
    (σ : Sentence (LSetC (M ⊕ ℕ))) {p : ℕ} {ks : Fin p → ℕ} (hinj : Function.Injective ks)
    (hcov : ∀ n : ℕ, Sum.inr n ∈ constSupport σ → ∃ i, ks i = n) :
    ¬Entailment.Consistent (insert (∼σ) (rubinTheory δ ρ)) ↔
      BlockAll δ ρ p ks
        fun s ↦ Semiformula.Eval (Fin.addCases ![] s) id (abstractFormula ks σ) := by
  rw [consistent_insert_iff_blockEx hdir (∼σ) hinj
    (fun n hn ↦ hcov n (by rwa [constSupport_neg] at hn)), not_blockEx_iff]
  constructor
  · exact BlockAll.mono δ ρ fun t ht ↦
      not_not.mp fun hc ↦ ht ((eval_abstractFormula_neg hinj σ hcov t).mpr hc)
  · exact BlockAll.mono δ ρ fun t ht hc ↦ (eval_abstractFormula_neg hinj σ hcov t).mp hc ht

end LemmaA3

end ZFVP
