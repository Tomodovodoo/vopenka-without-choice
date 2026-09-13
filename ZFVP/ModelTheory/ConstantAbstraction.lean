import ZFVP.ModelTheory.RubinStage

/-! # Turning the constants `d_n` into bound variables (for Enayat's Lemmas A.3 to A.5)

Enayat's Lemmas A.3 and A.4 start from a sentence `φ(d_{k₁}, …, d_{k_p})` of the language
`LSetC (M ⊕ ℕ)`, which has a constant `ṁ` for each `m : M` (`Sum.inl m`) and a constant `d_n` for
each `n : ℕ` (`Sum.inr n`), and read it as a statement about `M` in which the `d`'s have become
quantified variables. This file supplies the syntax for that reading.

Contents:

* `constSupportTerm` and `constSupport`, the list of constants that occur in a term or a formula
  of `LSetC C` with no free variables, `eval_congr_of_agree`, which says that the truth value
  depends on the assignment of the constants only there, and `exists_indices`, which reads off
  from `constSupport φ` an injective family `ks : Fin p → ℕ` covering every `d`-index in `φ`;
* `abstractTerm` and `abstractFormula`, which send a term or formula of `LSetC (M ⊕ ℕ)` of arity
  `m` to one of `ℒₛₑₜ` of arity `m + p` with parameters from `M`: the bound variable `#j` goes to
  `#(j.castAdd p)`, the constant `Sum.inl a` to the free variable `&a`, and the constant
  `Sum.inr n` to the bound variable `#(i.natAdd m)` for some `i` with `ks i = n`;
* `val_abstractTerm` and `eval_abstractFormula`, the evaluation lemmas.

Conventions.

* The concatenation is `Fin.addCases b d : Fin (m + p) → N`: the first `m` slots carry the
  original assignment `b` of the bound variables and the last `p` slots carry the values
  `fun i ↦ c (Sum.inr (ks i))` of the constants `d_{ks i}`. So `#j` for `j : Fin m` keeps its
  place and the `d`'s sit at the end.
* A constant `Sum.inr n` whose index is not of the form `ks i` is sent to the free variable
  `&(Classical.arbitrary M)`, a junk value. The evaluation lemmas take the covering hypothesis
  `∀ n, Sum.inr n ∈ constSupport φ → ∃ i, ks i = n`, which rules that case out.
* The arity of the target is carried as a variable `n` with an equation `n = m + p`, the way
  `ZFVP.altExFormulaAux` carries `n = e + p`, so that the quantifier step of the recursion, which
  needs `(m + 1) + p = (m + p) + 1`, only has to move the equation.
* Injectivity of `ks` is not needed for the evaluation lemmas: if `ks i = ks i'` then the two
  slots carry the same value, so it does not matter which one a constant is sent to. It will
  matter when A.3 and A.4 quantify the `p` slots separately, since there the `p` variables range
  independently and a repeated index would be read as two unrelated elements; that is why
  `exists_indices` produces an injective family.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v

/-! ## The constants that occur in a formula -/

section ConstSupport

variable {C : Type u} {N : Type v} [SetStructure N]

/-- The list of constants of `LSetC C` occurring in a term with no free variables. `ℒₛₑₜ` has no
function symbols, so a term is a bound variable or a single constant. -/
def constSupportTerm : {m : ℕ} → Semiterm (LSetC C) Empty m → List C
  | _, Semiterm.bvar _ => []
  | _, Semiterm.fvar x => x.elim
  | _, Semiterm.func (arity := k) f _ =>
    match k, f with
    | _, Sum.inl f' => Empty.elim f'
    | _, Sum.inr (Language.Constant.Func.const a) => [a]

/-- The list of constants of `LSetC C` occurring in a formula with no free variables. -/
def constSupport : {m : ℕ} → Semiformula (LSetC C) Empty m → List C
  | _, Semiformula.verum => []
  | _, Semiformula.falsum => []
  | _, Semiformula.rel r v =>
    match r with
    | Sum.inl _ => (List.ofFn fun i ↦ constSupportTerm (v i)).flatten
    | Sum.inr r' => PEmpty.elim r'
  | _, Semiformula.nrel r v =>
    match r with
    | Sum.inl _ => (List.ofFn fun i ↦ constSupportTerm (v i)).flatten
    | Sum.inr r' => PEmpty.elim r'
  | _, Semiformula.and φ ψ => constSupport φ ++ constSupport ψ
  | _, Semiformula.or φ ψ => constSupport φ ++ constSupport ψ
  | _, Semiformula.all φ => constSupport φ
  | _, Semiformula.exs φ => constSupport φ

/-- The value of a term depends on the assignment of the constants only at the constants that
occur in it. -/
theorem val_congr_of_agree {m : ℕ} (b : Fin m → N) (t : Semiterm (LSetC C) Empty m)
    (c c' : C → N) (h : ∀ a ∈ constSupportTerm t, c a = c' a) :
    Semiterm.val (s := setConstStructure N c) b Empty.elim t
      = Semiterm.val (s := setConstStructure N c') b Empty.elim t := by
  match t with
  | Semiterm.bvar x => rfl
  | Semiterm.fvar x => exact x.elim
  | Semiterm.func (arity := k) f v =>
    match k, f with
    | _, Sum.inl f' => exact f'.elim
    | _, Sum.inr (Language.Constant.Func.const a) =>
      exact h a (List.mem_singleton_self a)

/-- The truth value of a formula depends on the assignment of the constants only at the constants
that occur in it. -/
theorem eval_congr_of_agree {m : ℕ} (b : Fin m → N) (φ : Semiformula (LSetC C) Empty m)
    (c c' : C → N) (h : ∀ a ∈ constSupport φ, c a = c' a) :
    Semiformula.Eval (s := setConstStructure N c) b Empty.elim φ ↔
      Semiformula.Eval (s := setConstStructure N c') b Empty.elim φ := by
  induction φ using Semiformula.rec' generalizing c c' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v =>
    rcases r with r' | r'
    · have hv : (Semiterm.val (s := setConstStructure N c) b Empty.elim ∘ v)
          = (Semiterm.val (s := setConstStructure N c') b Empty.elim ∘ v) := by
        funext i
        refine val_congr_of_agree b (v i) c c' fun a ha ↦ h a ?_
        simp only [constSupport, List.mem_flatten, List.mem_ofFn]
        exact ⟨constSupportTerm (v i), ⟨i, rfl⟩, ha⟩
      refine Iff.trans (Semiformula.eval_rel (s := setConstStructure N c)) ?_
      refine Iff.trans ?_ (Semiformula.eval_rel (s := setConstStructure N c')).symm
      rw [hv]
      exact Iff.rfl
    · exact r'.elim
  | hnrel r v =>
    rcases r with r' | r'
    · have hv : (Semiterm.val (s := setConstStructure N c) b Empty.elim ∘ v)
          = (Semiterm.val (s := setConstStructure N c') b Empty.elim ∘ v) := by
        funext i
        refine val_congr_of_agree b (v i) c c' fun a ha ↦ h a ?_
        simp only [constSupport, List.mem_flatten, List.mem_ofFn]
        exact ⟨constSupportTerm (v i), ⟨i, rfl⟩, ha⟩
      refine Iff.trans (Semiformula.eval_nrel (s := setConstStructure N c)) ?_
      refine Iff.trans ?_ (Semiformula.eval_nrel (s := setConstStructure N c')).symm
      rw [hv]
      exact Iff.rfl
    · exact r'.elim
  | hand φ ψ ihφ ihψ =>
    simp only [LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ b c c' fun a ha ↦ h a (List.mem_append_left _ ha))
      (ihψ b c c' fun a ha ↦ h a (List.mem_append_right _ ha))
  | hor φ ψ ihφ ihψ =>
    simp only [LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ b c c' fun a ha ↦ h a (List.mem_append_left _ ha))
      (ihψ b c c' fun a ha ↦ h a (List.mem_append_right _ ha))
  | hall φ ih =>
    simp only [Semiformula.eval_all]
    exact forall_congr' fun x ↦ ih _ c c' h
  | hexs φ ih =>
    simp only [Semiformula.eval_ex]
    exact exists_congr fun x ↦ ih _ c c' h

end ConstSupport

/-! ## Reading off the indices of the constants `d_n` -/

section Indices

variable {M : Type u}

/-- The list of indices `n` with `d_n` occurring in `φ`, without repetitions. -/
def dIndices (φ : Semiformula (LSetC (M ⊕ ℕ)) Empty m) : List ℕ :=
  ((constSupport φ).filterMap fun a ↦ match a with | Sum.inl _ => none | Sum.inr n => some n).dedup

theorem mem_dIndices {m : ℕ} (φ : Semiformula (LSetC (M ⊕ ℕ)) Empty m) {n : ℕ}
    (h : Sum.inr n ∈ constSupport φ) : n ∈ dIndices φ := by
  rw [dIndices, List.mem_dedup, List.mem_filterMap]
  exact ⟨Sum.inr n, h, rfl⟩

/-- The indices of the constants `d_n` occurring in `φ` form a finite injective family. This is
the family `k₁, …, k_p` of Enayat's Lemmas A.3 and A.4. -/
theorem exists_indices {m : ℕ} (φ : Semiformula (LSetC (M ⊕ ℕ)) Empty m) :
    ∃ (p : ℕ) (ks : Fin p → ℕ), Function.Injective ks ∧
      ∀ n : ℕ, Sum.inr n ∈ constSupport φ → ∃ i, ks i = n := by
  refine ⟨(dIndices φ).length, (dIndices φ).get, ?_, ?_⟩
  · exact List.nodup_iff_injective_get.mp (List.nodup_dedup _)
  · intro n hn
    exact List.mem_iff_get.mp (mem_dIndices φ hn)

end Indices

/-! ## The abstraction -/

section Abstract

variable {M : Type u} [SetStructure M] [Nonempty M] {N : Type v} [SetStructure N] {p : ℕ}

/-- The slot of the target that a constant `d_j` goes to: the bound variable `#(i.natAdd m)` for
some `i` with `ks i = j`, and a junk free variable if there is no such `i`. -/
noncomputable def dSlot (ks : Fin p → ℕ) {m n : ℕ} (h : n = m + p) (j : ℕ) :
    Semiterm ℒₛₑₜ M n :=
  if hj : ∃ i, ks i = j then Semiterm.bvar (Fin.cast h.symm ((Classical.choose hj).natAdd m))
  else Semiterm.fvar (Classical.arbitrary M)

/-- The abstraction of a term, with the target arity carried as `n = m + p`. -/
noncomputable def abstractTermAux (ks : Fin p → ℕ) :
    {m n : ℕ} → n = m + p → Semiterm (LSetC (M ⊕ ℕ)) Empty m → Semiterm ℒₛₑₜ M n
  | _, _, h, Semiterm.bvar x => Semiterm.bvar (Fin.cast h.symm (x.castAdd p))
  | _, _, _, Semiterm.fvar x => x.elim
  | _, _, h, Semiterm.func (arity := k) f _ =>
    match k, f with
    | _, Sum.inl f' => Empty.elim f'
    | _, Sum.inr (Language.Constant.Func.const a) =>
      match a with
      | Sum.inl a => Semiterm.fvar a
      | Sum.inr j => dSlot ks h j

/-- The abstraction of a formula, with the target arity carried as `n = m + p`. -/
noncomputable def abstractFormulaAux (ks : Fin p → ℕ) :
    {m n : ℕ} → n = m + p → Semiformula (LSetC (M ⊕ ℕ)) Empty m → SetTheorySemiformula M n
  | _, _, _, Semiformula.verum => ⊤
  | _, _, _, Semiformula.falsum => ⊥
  | _, _, h, Semiformula.rel r v =>
    match r with
    | Sum.inl r' => Semiformula.rel r' fun i ↦ abstractTermAux ks h (v i)
    | Sum.inr r' => PEmpty.elim r'
  | _, _, h, Semiformula.nrel r v =>
    match r with
    | Sum.inl r' => Semiformula.nrel r' fun i ↦ abstractTermAux ks h (v i)
    | Sum.inr r' => PEmpty.elim r'
  | _, _, h, Semiformula.and φ ψ => abstractFormulaAux ks h φ ⋏ abstractFormulaAux ks h ψ
  | _, _, h, Semiformula.or φ ψ => abstractFormulaAux ks h φ ⋎ abstractFormulaAux ks h ψ
  | m, n, h, Semiformula.all φ =>
    ∀¹ abstractFormulaAux ks (show n + 1 = (m + 1) + p by omega) φ
  | m, n, h, Semiformula.exs φ =>
    ∃¹ abstractFormulaAux ks (show n + 1 = (m + 1) + p by omega) φ

/-- The abstraction of a term: arity `m` over `LSetC (M ⊕ ℕ)` becomes arity `m + p` over `ℒₛₑₜ`
with parameters from `M`. -/
noncomputable def abstractTerm (ks : Fin p → ℕ) {m : ℕ}
    (t : Semiterm (LSetC (M ⊕ ℕ)) Empty m) : Semiterm ℒₛₑₜ M (m + p) :=
  abstractTermAux ks rfl t

/-- The abstraction of a formula: arity `m` over `LSetC (M ⊕ ℕ)` becomes arity `m + p` over
`ℒₛₑₜ` with parameters from `M`. The constants `ṁ` become the parameters, the constants `d_{ks i}`
become the last `p` bound variables. -/
noncomputable def abstractFormula (ks : Fin p → ℕ) {m : ℕ}
    (φ : Semiformula (LSetC (M ⊕ ℕ)) Empty m) : SetTheorySemiformula M (m + p) :=
  abstractFormulaAux ks rfl φ

/-! ### Evaluation

The assignment of the target is described by the two equations `hb` and `hd` below, on the value
of the index rather than on the index itself, so that the quantifier step of the induction only
has to shift indices by one. -/

omit [SetStructure M] in
theorem val_dSlot (c : M ⊕ ℕ → N) (ks : Fin p → ℕ) {m n : ℕ} (h : n = m + p) (j : ℕ)
    (hj : ∃ i, ks i = j) (v : Fin n → N)
    (hd : ∀ (i : Fin p) (j' : Fin n), (j' : ℕ) = m + (i : ℕ) → v j' = c (Sum.inr (ks i))) :
    Semiterm.val (s := SetTheory.standardStructure N) v (fun a ↦ c (Sum.inl a)) (dSlot ks h j)
      = c (Sum.inr j) := by
  rw [dSlot]
  rw [dite_eq_left_of_eq_true (eq_true hj)]
  rw [Semiterm.val_bvar, hd (Classical.choose hj) _ (by simp)]
  rw [Classical.choose_spec hj]

omit [SetStructure N] in
private theorem hb_succ {m n : ℕ} (b : Fin m → N) (v : Fin n → N) (x : N)
    (hb : ∀ (j : Fin m) (j' : Fin n), (j' : ℕ) = (j : ℕ) → v j' = b j) :
    ∀ (j : Fin (m + 1)) (j' : Fin (n + 1)), (j' : ℕ) = (j : ℕ) → (x :> v) j' = (x :> b) j := by
  intro j j' hj
  rcases Fin.eq_zero_or_eq_succ j' with rfl | ⟨k, rfl⟩
  · have : j = 0 := Fin.ext (by simpa using hj.symm)
    subst this
    simp
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · simp at hj
    · simp only [Matrix.cons_val_succ]
      refine hb i k ?_
      simp only [Fin.val_succ] at hj
      omega

omit [SetStructure M] [Nonempty M] [SetStructure N] in
private theorem hd_succ {m n : ℕ} (c : M ⊕ ℕ → N) (ks : Fin p → ℕ) (v : Fin n → N) (x : N)
    (hd : ∀ (i : Fin p) (j' : Fin n), (j' : ℕ) = m + (i : ℕ) → v j' = c (Sum.inr (ks i))) :
    ∀ (i : Fin p) (j' : Fin (n + 1)), (j' : ℕ) = (m + 1) + (i : ℕ) →
      (x :> v) j' = c (Sum.inr (ks i)) := by
  intro i j' hj
  rcases Fin.eq_zero_or_eq_succ j' with rfl | ⟨k, rfl⟩
  · exfalso; simp only [Fin.val_zero] at hj; omega
  · simp only [Matrix.cons_val_succ]
    refine hd i k ?_
    simp only [Fin.val_succ] at hj
    omega

omit [SetStructure M] in
theorem val_abstractTermAux (c : M ⊕ ℕ → N) (ks : Fin p → ℕ) :
    ∀ {m : ℕ} (t : Semiterm (LSetC (M ⊕ ℕ)) Empty m)
      (_hcov : ∀ j : ℕ, Sum.inr j ∈ constSupportTerm t → ∃ i, ks i = j)
      {n : ℕ} (h : n = m + p) (b : Fin m → N) (v : Fin n → N)
      (_hb : ∀ (j : Fin m) (j' : Fin n), (j' : ℕ) = (j : ℕ) → v j' = b j)
      (_hd : ∀ (i : Fin p) (j' : Fin n), (j' : ℕ) = m + (i : ℕ) → v j' = c (Sum.inr (ks i))),
      Semiterm.val (s := SetTheory.standardStructure N) v (fun a ↦ c (Sum.inl a))
          (abstractTermAux ks h t)
        = Semiterm.val (s := setConstStructure N c) b Empty.elim t := by
  intro m t hcov n h b v hb hd
  match t with
  | Semiterm.bvar x =>
    exact hb x _ (by simp)
  | Semiterm.fvar x => exact x.elim
  | Semiterm.func (arity := k) f w =>
    match k, f with
    | _, Sum.inl f' => exact f'.elim
    | _, Sum.inr (Language.Constant.Func.const a) =>
      match a with
      | Sum.inl a => rfl
      | Sum.inr j =>
        exact val_dSlot c ks h j (hcov j (List.mem_singleton_self _)) v hd

omit [SetStructure M] in
/-- The abstraction of a term evaluates, under an assignment whose last `p` slots carry the
values of the constants `d_{ks i}`, to the value of the original term. -/
theorem val_abstractTerm (c : M ⊕ ℕ → N) (ks : Fin p → ℕ) {m : ℕ} (b : Fin m → N)
    (t : Semiterm (LSetC (M ⊕ ℕ)) Empty m)
    (hcov : ∀ j : ℕ, Sum.inr j ∈ constSupportTerm t → ∃ i, ks i = j) :
    Semiterm.val (s := SetTheory.standardStructure N)
        (Fin.addCases b fun i ↦ c (Sum.inr (ks i))) (fun a ↦ c (Sum.inl a)) (abstractTerm ks t)
      = Semiterm.val (s := setConstStructure N c) b Empty.elim t := by
  refine val_abstractTermAux c ks t hcov rfl b _ ?_ ?_
  · intro j j' hj
    have : j' = j.castAdd p := Fin.ext (by simpa using hj)
    subst this
    simp
  · intro i j' hj
    have : j' = i.natAdd m := Fin.ext (by simpa using hj)
    subst this
    simp

omit [SetStructure M] in
theorem eval_abstractFormulaAux (c : M ⊕ ℕ → N) (ks : Fin p → ℕ) :
    ∀ {m : ℕ} (φ : Semiformula (LSetC (M ⊕ ℕ)) Empty m)
      (_hcov : ∀ j : ℕ, Sum.inr j ∈ constSupport φ → ∃ i, ks i = j)
      {n : ℕ} (h : n = m + p) (b : Fin m → N) (v : Fin n → N)
      (_hb : ∀ (j : Fin m) (j' : Fin n), (j' : ℕ) = (j : ℕ) → v j' = b j)
      (_hd : ∀ (i : Fin p) (j' : Fin n), (j' : ℕ) = m + (i : ℕ) → v j' = c (Sum.inr (ks i))),
      Semiformula.Eval (s := SetTheory.standardStructure N) v (fun a ↦ c (Sum.inl a))
          (abstractFormulaAux ks h φ)
        ↔ Semiformula.Eval (s := setConstStructure N c) b Empty.elim φ := by
  intro m φ
  induction φ using Semiformula.rec' with
  | hverum => intro _ n h b v _ _; simp [abstractFormulaAux]
  | hfalsum => intro _ n h b v _ _; simp [abstractFormulaAux]
  | hrel r w =>
    rcases r with r' | r'
    · intro hcov n h b v hb hd
      have hv : (Semiterm.val (s := SetTheory.standardStructure N) v
            (fun a ↦ c (Sum.inl a)) ∘ fun i ↦ abstractTermAux ks h (w i))
          = (Semiterm.val (s := setConstStructure N c) b Empty.elim ∘ w) := by
        funext i
        refine val_abstractTermAux c ks (w i) (fun j hj ↦ hcov j ?_) h b v hb hd
        simp only [constSupport, List.mem_flatten, List.mem_ofFn]
        exact ⟨constSupportTerm (w i), ⟨i, rfl⟩, hj⟩
      show Semiformula.Eval (s := SetTheory.standardStructure N) v (fun a ↦ c (Sum.inl a))
          (Semiformula.rel r' fun i ↦ abstractTermAux ks h (w i)) ↔ _
      refine Iff.trans (Semiformula.eval_rel (s := SetTheory.standardStructure N)) ?_
      refine Iff.trans ?_ (Semiformula.eval_rel (s := setConstStructure N c)).symm
      rw [hv]
      exact Iff.rfl
    · exact fun _ _ _ _ _ _ _ ↦ r'.elim
  | hnrel r w =>
    rcases r with r' | r'
    · intro hcov n h b v hb hd
      have hv : (Semiterm.val (s := SetTheory.standardStructure N) v
            (fun a ↦ c (Sum.inl a)) ∘ fun i ↦ abstractTermAux ks h (w i))
          = (Semiterm.val (s := setConstStructure N c) b Empty.elim ∘ w) := by
        funext i
        refine val_abstractTermAux c ks (w i) (fun j hj ↦ hcov j ?_) h b v hb hd
        simp only [constSupport, List.mem_flatten, List.mem_ofFn]
        exact ⟨constSupportTerm (w i), ⟨i, rfl⟩, hj⟩
      show Semiformula.Eval (s := SetTheory.standardStructure N) v (fun a ↦ c (Sum.inl a))
          (Semiformula.nrel r' fun i ↦ abstractTermAux ks h (w i)) ↔ _
      refine Iff.trans (Semiformula.eval_nrel (s := SetTheory.standardStructure N)) ?_
      refine Iff.trans ?_ (Semiformula.eval_nrel (s := setConstStructure N c)).symm
      rw [hv]
      exact Iff.rfl
    · exact fun _ _ _ _ _ _ _ ↦ r'.elim
  | hand φ ψ ihφ ihψ =>
    intro hcov n h b v hb hd
    simp only [abstractFormulaAux, LogicalConnective.HomClass.map_and]
    exact and_congr
      (ihφ (fun j hj ↦ hcov j (List.mem_append_left _ hj)) h b v hb hd)
      (ihψ (fun j hj ↦ hcov j (List.mem_append_right _ hj)) h b v hb hd)
  | hor φ ψ ihφ ihψ =>
    intro hcov n h b v hb hd
    simp only [abstractFormulaAux, LogicalConnective.HomClass.map_or]
    exact or_congr
      (ihφ (fun j hj ↦ hcov j (List.mem_append_left _ hj)) h b v hb hd)
      (ihψ (fun j hj ↦ hcov j (List.mem_append_right _ hj)) h b v hb hd)
  | hall φ ih =>
    intro hcov n h b v hb hd
    simp only [abstractFormulaAux, Semiformula.eval_all]
    exact forall_congr' fun x ↦
      ih hcov _ (x :> b) (x :> v) (hb_succ b v x hb) (hd_succ c ks v x hd)
  | hexs φ ih =>
    intro hcov n h b v hb hd
    simp only [abstractFormulaAux, Semiformula.eval_ex]
    exact exists_congr fun x ↦
      ih hcov _ (x :> b) (x :> v) (hb_succ b v x hb) (hd_succ c ks v x hd)

omit [SetStructure M] in
/-- The abstraction of a formula holds, under the assignment that is `b` on the first `m` slots
and `fun i ↦ c (Sum.inr (ks i))` on the last `p`, with the constants `ṁ` read as parameters,
exactly when the original formula holds at `b` in the structure with the constants interpreted by
`c`. -/
theorem eval_abstractFormula (c : M ⊕ ℕ → N) (ks : Fin p → ℕ) {m : ℕ} (b : Fin m → N)
    (φ : Semiformula (LSetC (M ⊕ ℕ)) Empty m)
    (hcov : ∀ n : ℕ, Sum.inr n ∈ constSupport φ → ∃ i, ks i = n) :
    Semiformula.Eval (s := SetTheory.standardStructure N)
        (Fin.addCases b fun i ↦ c (Sum.inr (ks i))) (fun a ↦ c (Sum.inl a))
        (abstractFormula ks φ)
      ↔ Semiformula.Eval (s := setConstStructure N c) b Empty.elim φ := by
  refine eval_abstractFormulaAux c ks φ hcov rfl b _ ?_ ?_
  · intro j j' hj
    have : j' = j.castAdd p := Fin.ext (by simpa using hj)
    subst this
    simp
  · intro i j' hj
    have : j' = i.natAdd m := Fin.ext (by simpa using hj)
    subst this
    simp

end Abstract

end ZFVP
