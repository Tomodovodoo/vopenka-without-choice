import ZFVP.ModelTheory.HenkinSet
import ZFVP.ModelTheory.StageSatisfaction

/-! # The term model of a Henkin set

Reads a model off a `HenkinSet T Ψ` when the language has equality and `T` contains the equality
axioms. The domain is `ℕ`, the free variables of `Proposition L`: every term is named by a
variable, because `∃x (x = t)` is provable from the equality axioms and `HenkinSet.witness`
supplies a variable for it. Equality is interpreted by the relation the Henkin set says it is,
not collapsed to real equality, which is enough for the omitting types statement.
-/

namespace ZFVP

open LO LO.FirstOrder LO.Entailment

universe u

/-! ### Transport along the equivalence `ℕ ≃ ULift ℕ`

The structure on `ℕ` is not an instance, so the transport lemma is stated in a section where the
structure on `ℕ` is a section variable and can be supplied by name at the point of use. -/

section Transport

variable {L : Language.{u}} [s : Structure L ℕ]

/-- Truth in the term model carried to `ULift ℕ`. -/
theorem eval_ulift {ξ : Type*} {n : ℕ} (b : Fin n → ULift.{u} ℕ) (f : ξ → ULift.{u} ℕ)
    (φ : Semiformula L ξ n) :
    Semiformula.Eval (s := Structure.ofEquiv Equiv.ulift.symm) b f φ ↔
      Semiformula.Eval (fun i ↦ (b i).down) (fun x ↦ (f x).down) φ := by
  rw [Structure.eval_ofEquiv_iff]
  rfl

end Transport

section Closure

variable {L : Language.{u}} {T : Theory L}
  {q : ℕ → ℕ} {Ψ : (n : ℕ) → PartialType L (q n)}

/-- A Henkin set is closed under semantic consequence from its own members: if every model of `T`
with an assignment satisfying `Δ` also satisfies `φ`, and `Δ` is drawn from the set, then `φ`
belongs to the set. The models quantified over live in `Type u` for `L : Language.{u}`, which is
the universe `exists_model_of_consistentOver_list` produces. -/
theorem HenkinSet.mem_of_models (H : HenkinSet T Ψ) {φ : Proposition L}
    (Δ : List (Proposition L)) (hΔ : ∀ χ ∈ Δ, χ ∈ H.carrier)
    (h : ∀ (M : Type u) (_ : Nonempty M) (_ : Structure L M) (ε : ℕ → M),
      M↓[L] ⊧* T → (∀ χ ∈ Δ, Semiformula.Eval ![] ε χ) → Semiformula.Eval ![] ε φ) :
    φ ∈ H.carrier := by
  by_contra hφ
  have hmem : ∀ χ ∈ (∼φ :: Δ), χ ∈ H.carrier := by
    intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | hχ
    · exact (H.not_mem_iff φ).mp hφ
    · exact hΔ χ hχ
  have hcon : ConsistentOver T {χ : Proposition L | χ ∈ (∼φ :: Δ)} :=
    (consistentOver_list_iff T _).mpr (H.consistent _ hmem)
  obtain ⟨M, hne, hs, ε, hT, hε⟩ := exists_model_of_consistentOver_list hcon
  have h1 : Semiformula.Eval ![] ε (∼φ) := hε _ List.mem_cons_self
  have h2 : Semiformula.Eval ![] ε φ :=
    h M hne hs ε hT fun χ hχ ↦ hε χ (List.mem_cons_of_mem _ hχ)
  rw [LogicalConnective.HomClass.map_neg] at h1
  exact h1 h2

end Closure

/-! ### Equations between terms -/

variable {L : Language.{u}} [L.Eq] {T : Theory L}
  {q : ℕ → ℕ} {Ψ : (n : ℕ) → PartialType L (q n)}

/-- The formula `t = u`. -/
def eqProp {ξ : Type*} {n : ℕ} (t u : Semiterm L ξ n) : Semiformula L ξ n :=
  Semiformula.Operator.operator op(=) ![t, u]

@[simp] theorem eval_eqProp {M : Type*} [Structure L M] {ξ : Type*} {n : ℕ}
    (b : Fin n → M) (ε : ξ → M) (t u : Semiterm L ξ n) :
    Semiformula.Eval b ε (eqProp t u) ↔
      Structure.Eq.eqv L (Semiterm.val b ε t) (Semiterm.val b ε u) := by
  have hv : (Semiterm.val b ε ∘ (![t, u] : Fin 2 → Semiterm L ξ n))
      = ![Semiterm.val b ε t, Semiterm.val b ε u] := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [eqProp, Semiformula.eval_operator, hv]
  exact Iff.rfl

@[simp] theorem rew_eqProp {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew L ξ₁ n₁ ξ₂ n₂)
    (t u : Semiterm L ξ₁ n₁) : ω ▹ eqProp t u = eqProp (ω t) (ω u) := by
  simp [eqProp]

/-! ### Naming every term by a variable -/

/-- In a model of a theory containing the equality axioms, `=` is interpreted by an equivalence
relation. This is the instance Foundation's congruence lemmas ask for. -/
private theorem modelsSet_eqAxiom {M : Type*} [Nonempty M] [Structure L M] {T : Theory L}
    (hEq : 𝗘𝗤 L ⊆ T) (hT : M↓[L] ⊧* T) : M↓[L] ⊧* 𝗘𝗤 L :=
  Semantics.ModelsSet.of_subset hT hEq

/-- Every term is named by a free variable outside any prescribed finite set: the equality axioms
prove `∃x (x = t)`, so the witness clause of the Henkin set supplies a fresh variable `m` with
`m = t` in the set. -/
theorem exists_name_avoiding (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (t : SyntacticTerm L)
    (F : Finset ℕ) : ∃ m, m ∉ F ∧ eqProp (&m) t ∈ H.carrier := by
  have hex : (∃¹ (eqProp (#0 : Semiterm L ℕ 1) (Rew.bShift t))) ∈ H.carrier := by
    refine H.mem_of_models [] (by simp) ?_
    intro M hne hs ε hT _
    haveI := modelsSet_eqAxiom (M := M) hEq hT
    rw [Semiformula.eval_ex]
    refine ⟨Semiterm.val ![] ε t, ?_⟩
    rw [eval_eqProp]
    simpa using Structure.Eq.eqv_refl (L := L) (Semiterm.val ![] ε t)
  obtain ⟨m, hmF, hm⟩ := H.witness _ hex F
  exact ⟨m, hmF, by simpa using hm⟩

/-- Every term is named by a free variable. -/
theorem exists_name (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (t : SyntacticTerm L) :
    ∃ m : ℕ, eqProp (&m) t ∈ H.carrier :=
  let ⟨m, _, hm⟩ := exists_name_avoiding hEq H t ∅
  ⟨m, hm⟩

/-! ### The structure -/

-- `termStructure` is data read off a Henkin set, so it is a plain definition, not an instance.
set_option warn.classDefReducibility false

/-- The term model of a Henkin set. The domain is `ℕ`, the free variables of `Proposition L`.
A function symbol applied to a tuple of variables is interpreted by a variable naming the resulting
term, and a relation symbol holds of a tuple of variables exactly when the Henkin set contains the
corresponding atomic formula. Equality is not collapsed: it is interpreted by whatever relation the
Henkin set gives it. -/
noncomputable def termStructure (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) : Structure L ℕ where
  func := fun _ f v ↦ (exists_name hEq H (Semiterm.func f fun i ↦ &(v i))).choose
  rel := fun _ r v ↦ Semiformula.rel r (fun i ↦ &(v i)) ∈ H.carrier

/-- The variable interpreting `f` at a tuple of variables names the corresponding term. -/
theorem termStructure_func_mem (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) {k : ℕ} (f : L.Func k)
    (v : Fin k → ℕ) :
    eqProp (&((termStructure hEq H).func f v)) (Semiterm.func f fun i ↦ &(v i)) ∈ H.carrier :=
  (exists_name hEq H _).choose_spec

/-- Relations in the term model are read straight off the Henkin set. -/
theorem termStructure_rel (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) {k : ℕ} (r : L.Rel k)
    (v : Fin k → ℕ) :
    (termStructure hEq H).rel r v ↔ Semiformula.rel r (fun i ↦ &(v i)) ∈ H.carrier :=
  Iff.rfl

/-! ### Equality behaves like equality inside the Henkin set -/

/-- The list of equations `s i = t i`. -/
private def eqList {k : ℕ} (s t : Fin k → SyntacticTerm L) : List (Proposition L) :=
  List.ofFn fun i ↦ eqProp (s i) (t i)

private theorem mem_eqList {k : ℕ} (s t : Fin k → SyntacticTerm L) (i : Fin k) :
    eqProp (s i) (t i) ∈ eqList s t :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

private theorem eqList_subset (H : HenkinSet T Ψ) {k : ℕ} {s t : Fin k → SyntacticTerm L}
    (h : ∀ i, eqProp (s i) (t i) ∈ H.carrier) : ∀ χ ∈ eqList s t, χ ∈ H.carrier := by
  intro χ hχ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hχ
  exact h i

section Congruence

variable (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ)

include hEq

/-- Reflexivity of equality inside the Henkin set. -/
theorem eq_refl_mem (t : SyntacticTerm L) : eqProp t t ∈ H.carrier := by
  refine H.mem_of_models [] (by simp) ?_
  intro M hne hs ε hT _
  haveI := modelsSet_eqAxiom (M := M) hEq hT
  rw [eval_eqProp]
  exact Structure.Eq.eqv_refl _

/-- Symmetry of equality inside the Henkin set. -/
theorem eq_symm_mem {t u : SyntacticTerm L} (h : eqProp t u ∈ H.carrier) :
    eqProp u t ∈ H.carrier := by
  refine H.mem_of_models [eqProp t u] (by simpa using h) ?_
  intro M hne hs ε hT hΔ
  haveI := modelsSet_eqAxiom (M := M) hEq hT
  have h1 : Semiformula.Eval ![] ε (eqProp t u) := hΔ _ (by simp)
  rw [eval_eqProp] at h1 ⊢
  exact Structure.Eq.eqv_symm h1

/-- Transitivity of equality inside the Henkin set. -/
theorem eq_trans_mem {t u v : SyntacticTerm L} (h₁ : eqProp t u ∈ H.carrier)
    (h₂ : eqProp u v ∈ H.carrier) : eqProp t v ∈ H.carrier := by
  refine H.mem_of_models [eqProp t u, eqProp u v] ?_ ?_
  · intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | hχ
    · exact h₁
    · rcases List.mem_cons.mp hχ with rfl | hχ
      · exact h₂
      · simp at hχ
  · intro M hne hs ε hT hΔ
    haveI := modelsSet_eqAxiom (M := M) hEq hT
    have e₁ : Semiformula.Eval ![] ε (eqProp t u) := hΔ _ (by simp)
    have e₂ : Semiformula.Eval ![] ε (eqProp u v) := hΔ _ (by simp)
    rw [eval_eqProp] at e₁ e₂ ⊢
    exact Structure.Eq.eqv_trans e₁ e₂

/-- Congruence for function symbols inside the Henkin set. -/
theorem eq_func_mem {k : ℕ} (f : L.Func k) {s t : Fin k → SyntacticTerm L}
    (h : ∀ i, eqProp (s i) (t i) ∈ H.carrier) :
    eqProp (Semiterm.func f s) (Semiterm.func f t) ∈ H.carrier := by
  refine H.mem_of_models (eqList s t) (eqList_subset H h) ?_
  intro M hne hs ε hT hΔ
  haveI := modelsSet_eqAxiom (M := M) hEq hT
  have hi : ∀ i, Structure.Eq.eqv L (Semiterm.val ![] ε (s i)) (Semiterm.val ![] ε (t i)) := by
    intro i
    have := hΔ _ (mem_eqList s t i)
    rwa [eval_eqProp] at this
  rw [eval_eqProp]
  simpa [Semiterm.val_func, Function.comp_def] using Structure.Eq.eqv_funcExt f hi

/-- Congruence for relation symbols inside the Henkin set, one direction. -/
theorem rel_mem_of_rel_mem {k : ℕ} (r : L.Rel k) {s t : Fin k → SyntacticTerm L}
    (h : ∀ i, eqProp (s i) (t i) ∈ H.carrier) (hr : Semiformula.rel r s ∈ H.carrier) :
    Semiformula.rel r t ∈ H.carrier := by
  refine H.mem_of_models (Semiformula.rel r s :: eqList s t) ?_ ?_
  · intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | hχ
    · exact hr
    · exact eqList_subset H h χ hχ
  · intro M hne hs ε hT hΔ
    haveI := modelsSet_eqAxiom (M := M) hEq hT
    have hi : ∀ i, Structure.Eq.eqv L (Semiterm.val ![] ε (s i)) (Semiterm.val ![] ε (t i)) := by
      intro i
      have := hΔ _ (List.mem_cons_of_mem _ (mem_eqList s t i))
      rwa [eval_eqProp] at this
    have hs' : Semiformula.Eval ![] ε (Semiformula.rel r s) := hΔ _ (by simp)
    rw [Semiformula.eval_rel] at hs' ⊢
    exact (Structure.Eq.eqv_relExt r hi).mp hs'

/-- Congruence for relation symbols inside the Henkin set. -/
theorem rel_mem_iff {k : ℕ} (r : L.Rel k) {s t : Fin k → SyntacticTerm L}
    (h : ∀ i, eqProp (s i) (t i) ∈ H.carrier) :
    Semiformula.rel r s ∈ H.carrier ↔ Semiformula.rel r t ∈ H.carrier :=
  ⟨rel_mem_of_rel_mem hEq H r h,
    rel_mem_of_rel_mem hEq H r fun i ↦ eq_symm_mem hEq H (h i)⟩

end Congruence

/-! ### Every term is named by its own value -/

/-- The value of a term in the term model. -/
noncomputable def termVal (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (t : SyntacticTerm L) : ℕ :=
  Semiterm.val (s := termStructure hEq H) ![] id t

/-- The variable that the term model assigns to a term names that term inside the Henkin set. -/
theorem val_mem (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (t : SyntacticTerm L) :
    eqProp (&(termVal hEq H t)) t ∈ H.carrier := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact eq_refl_mem hEq H _
  | func f v ih =>
      have hval : termVal hEq H (Semiterm.func f v)
          = (termStructure hEq H).func f fun i ↦ termVal hEq H (v i) := rfl
      rw [hval]
      refine eq_trans_mem hEq H (termStructure_func_mem hEq H f _) ?_
      exact eq_func_mem hEq H f ih

/-! ### How a Henkin set treats the logical connectives -/

section Connectives

variable (H : HenkinSet T Ψ)

/-- Substituting the free variable `&x` for the single bound variable and then evaluating is
evaluating at the value of `x`. -/
private theorem val_comp_single {M : Type*} [Structure L M] (ε : ℕ → M) (x : ℕ) :
    (Semiterm.val (L := L) ![] ε ∘ ![(&x : SyntacticTerm L)]) = ![ε x] := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl

/-- A Henkin set contains `⊤`. -/
theorem top_mem : (⊤ : Proposition L) ∈ H.carrier :=
  H.mem_of_models [] (by simp) fun _ _ _ _ _ _ ↦ by simp

/-- A Henkin set does not contain `⊥`. -/
theorem bot_not_mem : (⊥ : Proposition L) ∉ H.carrier :=
  (H.not_mem_iff ⊥).mpr (by simpa using top_mem H)

/-- A Henkin set contains a conjunction exactly when it contains both conjuncts. -/
theorem and_mem_iff (φ ψ : Proposition L) :
    (φ ⋏ ψ) ∈ H.carrier ↔ φ ∈ H.carrier ∧ ψ ∈ H.carrier := by
  constructor
  · intro h
    constructor
    · refine H.mem_of_models [φ ⋏ ψ] (by simpa using h) ?_
      intro M _ _ ε _ hΔ
      have e := hΔ _ (List.mem_cons_self)
      simp only [LogicalConnective.HomClass.map_and] at e
      exact e.1
    · refine H.mem_of_models [φ ⋏ ψ] (by simpa using h) ?_
      intro M _ _ ε _ hΔ
      have e := hΔ _ (List.mem_cons_self)
      simp only [LogicalConnective.HomClass.map_and] at e
      exact e.2
  · rintro ⟨h1, h2⟩
    refine H.mem_of_models [φ, ψ] ?_ ?_
    · intro χ hχ
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact h1
      · rcases List.mem_cons.mp hχ with rfl | hχ
        · exact h2
        · simp at hχ
    · intro M _ _ ε _ hΔ
      simp only [LogicalConnective.HomClass.map_and]
      exact ⟨hΔ _ (by simp), hΔ _ (by simp)⟩

/-- A Henkin set contains a disjunction exactly when it contains one of the disjuncts. -/
theorem or_mem_iff (φ ψ : Proposition L) :
    (φ ⋎ ψ) ∈ H.carrier ↔ φ ∈ H.carrier ∨ ψ ∈ H.carrier := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.mp hc
    refine bot_not_mem H ?_
    refine H.mem_of_models [φ ⋎ ψ, ∼φ, ∼ψ] ?_ ?_
    · intro χ hχ
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact h
      · rcases List.mem_cons.mp hχ with rfl | hχ
        · exact (H.not_mem_iff φ).mp h1
        · rcases List.mem_cons.mp hχ with rfl | hχ
          · exact (H.not_mem_iff ψ).mp h2
          · simp at hχ
    · intro M _ _ ε _ hΔ
      have e0 := hΔ (φ ⋎ ψ) (by simp)
      have e1 := hΔ (∼φ) (by simp)
      have e2 := hΔ (∼ψ) (by simp)
      simp only [LogicalConnective.HomClass.map_or] at e0
      simp only [LogicalConnective.HomClass.map_neg] at e1 e2
      exfalso
      rcases e0 with e0 | e0
      · exact e1 e0
      · exact e2 e0
  · intro h
    rcases h with h | h
    · refine H.mem_of_models [φ] (by simpa using h) ?_
      intro M _ _ ε _ hΔ
      simp only [LogicalConnective.HomClass.map_or]
      exact Or.inl (hΔ _ (by simp))
    · refine H.mem_of_models [ψ] (by simpa using h) ?_
      intro M _ _ ε _ hΔ
      simp only [LogicalConnective.HomClass.map_or]
      exact Or.inr (hΔ _ (by simp))

/-- A Henkin set contains a universal formula exactly when it contains every instance of it at a
free variable. -/
theorem all_mem_iff (φ : Semiproposition L 1) :
    (∀¹ φ : Proposition L) ∈ H.carrier ↔ ∀ x : ℕ, φ/[(&x : SyntacticTerm L)] ∈ H.carrier := by
  constructor
  · intro h x
    refine H.mem_of_models [∀¹ φ] (by simpa using h) ?_
    intro M _ _ ε _ hΔ
    have e := hΔ _ (List.mem_cons_self)
    rw [Semiformula.eval_all] at e
    rw [Semiformula.eval_substs, val_comp_single]
    exact e (ε x)
  · intro h
    by_contra hn
    have hneg : (∃¹ (∼φ) : Proposition L) ∈ H.carrier := by
      simpa using (H.not_mem_iff (∀¹ φ : Proposition L)).mp hn
    obtain ⟨m, -, hm⟩ := H.witness (∼φ) hneg ∅
    rw [show (∼φ)/[(&m : SyntacticTerm L)] = ∼(φ/[(&m : SyntacticTerm L)]) from by simp] at hm
    exact ((H.not_mem_iff _).mpr hm) (h m)

/-- A Henkin set contains an existential formula exactly when it contains some instance of it at a
free variable. -/
theorem exs_mem_iff (φ : Semiproposition L 1) :
    (∃¹ φ : Proposition L) ∈ H.carrier ↔ ∃ x : ℕ, φ/[(&x : SyntacticTerm L)] ∈ H.carrier := by
  constructor
  · intro h
    obtain ⟨m, -, hm⟩ := H.witness φ h ∅
    exact ⟨m, hm⟩
  · rintro ⟨x, hx⟩
    refine H.mem_of_models [φ/[(&x : SyntacticTerm L)]] (by simpa using hx) ?_
    intro M _ _ ε _ hΔ
    have e := hΔ _ (List.mem_cons_self)
    rw [Semiformula.eval_substs, val_comp_single] at e
    rw [Semiformula.eval_ex]
    exact ⟨ε x, e⟩

end Connectives

/-! ### The truth lemma -/

section Truth

variable (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ)

include hEq

/-- Atomic formulas are true in the term model exactly when the Henkin set contains them. -/
theorem eval_rel_iff_mem {k : ℕ} (r : L.Rel k) (v : Fin k → SyntacticTerm L) :
    Semiformula.Eval (s := termStructure hEq H) ![] (id : ℕ → ℕ) (Semiformula.rel r v)
      ↔ Semiformula.rel r v ∈ H.carrier := by
  rw [Semiformula.eval_rel,
    show (Semiterm.val (s := termStructure hEq H) ![] id ∘ v) = fun i ↦ termVal hEq H (v i) from rfl,
    termStructure_rel]
  exact rel_mem_iff hEq H r fun i ↦ val_mem hEq H (v i)

/-- Negated atomic formulas are true in the term model exactly when the Henkin set contains
them. -/
theorem eval_nrel_iff_mem {k : ℕ} (r : L.Rel k) (v : Fin k → SyntacticTerm L) :
    Semiformula.Eval (s := termStructure hEq H) ![] (id : ℕ → ℕ) (Semiformula.nrel r v)
      ↔ Semiformula.nrel r v ∈ H.carrier := by
  rw [show (Semiformula.nrel r v : Proposition L) = ∼(Semiformula.rel r v) from rfl,
    LogicalConnective.HomClass.map_neg, ← H.not_mem_iff, ← eval_rel_iff_mem hEq H r v]
  exact Iff.rfl

/-- Instantiating the single bound variable of `φ` at the free variable `x` and reading the result
under the identity assignment is evaluating `φ` at `x`. -/
private theorem eval_subst_var (φ : Semiproposition L 1) (x : ℕ) :
    Semiformula.Eval (s := termStructure hEq H) ![] (id : ℕ → ℕ) (φ/[(&x : SyntacticTerm L)])
      ↔ Semiformula.Eval (s := termStructure hEq H) (x :> ![]) (id : ℕ → ℕ) φ := by
  rw [Semiformula.eval_substs,
    @val_comp_single L _ ℕ (termStructure hEq H) (id : ℕ → ℕ) x]
  exact Iff.rfl

/-- The truth lemma: a proposition holds in the term model under the assignment sending every
variable to itself exactly when it belongs to the Henkin set. -/
theorem eval_iff_mem (φ : Proposition L) :
    Semiformula.Eval (s := termStructure hEq H) ![] (id : ℕ → ℕ) φ ↔ φ ∈ H.carrier := by
  suffices h : ∀ (c : ℕ) (φ : Proposition L), φ.complexity ≤ c →
      (Semiformula.Eval (s := termStructure hEq H) ![] (id : ℕ → ℕ) φ ↔ φ ∈ H.carrier) from
    h φ.complexity φ le_rfl
  intro c
  induction c with
  | zero =>
      intro φ
      match φ with
      | Semiformula.rel r v => exact fun _ ↦ eval_rel_iff_mem hEq H r v
      | Semiformula.nrel r v => exact fun _ ↦ eval_nrel_iff_mem hEq H r v
      | ⊤ => exact fun _ ↦ iff_of_true (by simp) (top_mem H)
      | ⊥ => exact fun _ ↦ iff_of_false (by simp) (bot_not_mem H)
      | φ ⋏ ψ => intro hc; simp only [Semiformula.complexity_and] at hc; omega
      | φ ⋎ ψ => intro hc; simp only [Semiformula.complexity_or] at hc; omega
      | ∀¹ φ => intro hc; simp only [Semiformula.complexity_all] at hc; omega
      | ∃¹ φ => intro hc; simp only [Semiformula.complexity_exs] at hc; omega
  | succ c ih =>
      intro φ
      match φ with
      | Semiformula.rel r v => exact fun _ ↦ eval_rel_iff_mem hEq H r v
      | Semiformula.nrel r v => exact fun _ ↦ eval_nrel_iff_mem hEq H r v
      | ⊤ => exact fun _ ↦ iff_of_true (by simp) (top_mem H)
      | ⊥ => exact fun _ ↦ iff_of_false (by simp) (bot_not_mem H)
      | φ ⋏ ψ =>
          intro hc
          simp only [Semiformula.complexity_and] at hc
          rw [LogicalConnective.HomClass.map_and, ih φ (by omega), ih ψ (by omega)]
          exact (and_mem_iff H φ ψ).symm
      | φ ⋎ ψ =>
          intro hc
          simp only [Semiformula.complexity_or] at hc
          rw [LogicalConnective.HomClass.map_or, ih φ (by omega), ih ψ (by omega)]
          exact (or_mem_iff H φ ψ).symm
      | ∀¹ φ =>
          intro hc
          simp only [Semiformula.complexity_all] at hc
          have hsub : ∀ x : ℕ, (φ/[(&x : SyntacticTerm L)]).complexity ≤ c := by
            intro x
            simpa using Nat.le_of_succ_le_succ hc
          rw [Semiformula.eval_all, all_mem_iff H]
          exact forall_congr' fun x ↦ by rw [← ih _ (hsub x), eval_subst_var]
      | ∃¹ φ =>
          intro hc
          simp only [Semiformula.complexity_exs] at hc
          have hsub : ∀ x : ℕ, (φ/[(&x : SyntacticTerm L)]).complexity ≤ c := by
            intro x
            simpa using Nat.le_of_succ_le_succ hc
          rw [Semiformula.eval_ex, exs_mem_iff H]
          exact exists_congr fun x ↦ by rw [← ih _ (hsub x), eval_subst_var]

end Truth

/-! ### The term model is a model of `T` -/

/-- The term model satisfies `T`. -/
theorem models_theory (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) :
    Language.str (s := termStructure hEq H) ℕ L ⊧* T := by
  refine Semantics.modelsSet_iff.mpr fun σ hσ ↦ ?_
  have h := (eval_iff_mem hEq H (Rewriting.emb σ : Proposition L)).mpr (H.axioms_mem hσ)
  rw [Semiformula.eval_emb] at h
  exact h

/-! ### The term model omits every type -/

/-- In a model of the equality axioms the truth of a formula at a tuple depends on the tuple only
up to the interpreted equality. -/
theorem evalb_congr {M : Type*} [Nonempty M] [Structure L M] [M↓[L] ⊧* 𝗘𝗤 L] {k : ℕ}
    (ψ : Semisentence L k) {u w : Fin k → M} (h : ∀ i, Structure.Eq.eqv L (u i) (w i)) :
    Semiformula.Evalb u ψ ↔ Semiformula.Evalb w ψ := by
  have hq : (fun i ↦ (⟦u i⟧ : Structure.Eq.QuotEq L M)) = fun i ↦ ⟦w i⟧ := by
    funext i
    exact Structure.Eq.of_eq_of.mpr (h i)
  have h1 := Structure.Eq.QuotEq.eval_mk (M := M) (bv := u) (fv := (Empty.elim : Empty → M))
    (φ := ψ)
  have h2 := Structure.Eq.QuotEq.eval_mk (M := M) (bv := w) (fv := (Empty.elim : Empty → M))
    (φ := ψ)
  rw [← h1, ← h2, hq]

/-- A Henkin set does not distinguish tuples of variables it declares equal. -/
theorem substTuple_mem_of_mem (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) {k : ℕ}
    (ψ : Semisentence L k) {a b : Fin k → ℕ}
    (h : ∀ i, eqProp (&(a i) : SyntacticTerm L) (&(b i)) ∈ H.carrier)
    (hmem : substTuple ψ a ∈ H.carrier) : substTuple ψ b ∈ H.carrier := by
  refine H.mem_of_models
    (substTuple ψ a :: eqList (fun i ↦ (&(a i) : SyntacticTerm L)) (fun i ↦ &(b i))) ?_ ?_
  · intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | hχ
    · exact hmem
    · exact eqList_subset H h χ hχ
  · intro M hne hs ε hT hΔ
    haveI := modelsSet_eqAxiom (M := M) hEq hT
    have hi : ∀ i, Structure.Eq.eqv L (ε (a i)) (ε (b i)) := by
      intro i
      have := hΔ _ (List.mem_cons_of_mem _ (mem_eqList _ _ i))
      rw [eval_eqProp] at this
      simpa using this
    have h0 : Semiformula.Evalb (fun i ↦ ε (a i)) ψ := by
      have := hΔ _ List.mem_cons_self
      rwa [eval_substTuple] at this
    rw [eval_substTuple]
    exact (evalb_congr ψ hi).mp h0

/-! ### Injective tuples of names -/

/-- The variables used up when naming the first `k` entries of `b`. -/
private noncomputable def nameSet (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (b : ℕ → ℕ) :
    ℕ → Finset ℕ
  | 0 => ∅
  | k + 1 =>
      insert (exists_name_avoiding hEq H (&(b k)) (nameSet hEq H b k)).choose
        (nameSet hEq H b k)

/-- A variable naming `&(b k)` and different from all the earlier ones. -/
private noncomputable def nameOf (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (b : ℕ → ℕ) (k : ℕ) : ℕ :=
  (exists_name_avoiding hEq H (&(b k)) (nameSet hEq H b k)).choose

private theorem nameSet_succ (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (b : ℕ → ℕ) (k : ℕ) :
    nameSet hEq H b (k + 1) = insert (nameOf hEq H b k) (nameSet hEq H b k) := rfl

private theorem nameOf_not_mem (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (b : ℕ → ℕ) (k : ℕ) :
    nameOf hEq H b k ∉ nameSet hEq H b k :=
  (exists_name_avoiding hEq H (&(b k)) (nameSet hEq H b k)).choose_spec.1

private theorem nameOf_mem (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (b : ℕ → ℕ) (k : ℕ) :
    eqProp (&(nameOf hEq H b k) : SyntacticTerm L) (&(b k)) ∈ H.carrier :=
  (exists_name_avoiding hEq H (&(b k)) (nameSet hEq H b k)).choose_spec.2

private theorem nameSet_mono (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (b : ℕ → ℕ) :
    Monotone (nameSet hEq H b) :=
  monotone_nat_of_le_succ fun k ↦ by
    rw [nameSet_succ]
    exact Finset.subset_insert _ _

private theorem nameOf_injective (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (b : ℕ → ℕ) :
    Function.Injective (nameOf hEq H b) := by
  have key : ∀ j k : ℕ, j < k → nameOf hEq H b j ≠ nameOf hEq H b k := by
    intro j k hjk he
    refine nameOf_not_mem hEq H b k ?_
    rw [← he]
    refine nameSet_mono hEq H b (Nat.succ_le_of_lt hjk) ?_
    rw [nameSet_succ]
    exact Finset.mem_insert_self _ _
  intro j k he
  rcases lt_trichotomy j k with h | h | h
  · exact absurd he (key j k h)
  · exact h
  · exact absurd he.symm (key k j h)

/-- The term model omits every type of the family. -/
theorem omits_type (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (n : ℕ) :
    @Omits L ℕ (termStructure hEq H) (q n) (Ψ n) := by
  intro b
  set b' : ℕ → ℕ := fun k ↦ if h : k < q n then b ⟨k, h⟩ else 0 with hb'
  refine ?_
  set a : Fin (q n) → ℕ := fun i ↦ nameOf hEq H b' i.val with ha
  have hainj : Function.Injective a := fun i j hij ↦
    Fin.val_injective (nameOf_injective hEq H b' hij)
  have haeq : ∀ i : Fin (q n),
      eqProp (&(a i) : SyntacticTerm L) (&(b i)) ∈ H.carrier := by
    intro i
    have h := nameOf_mem hEq H b' i.val
    rwa [show b' i.val = b i from by simp [hb']] at h
  obtain ⟨ψ, hψΨ, hψ⟩ := H.omits n a hainj
  have hna : substTuple ψ a ∉ H.carrier := (H.not_mem_iff _).mpr hψ
  refine ⟨ψ, hψΨ, ?_⟩
  intro hev
  refine hna (substTuple_mem_of_mem hEq H ψ (fun i ↦ eq_symm_mem hEq H (haeq i)) ?_)
  rw [← eval_iff_mem hEq H, @eval_substTuple L ℕ (termStructure hEq H) (q n) ψ b id]
  simpa using hev

/-! ### The packaged model

`OmittingModel` wants a domain in `Type u` for `L : Language.{u}`, so the term model is carried
along the equivalence `ℕ ≃ ULift ℕ`. -/

/-- The term model transported to `ULift ℕ`. -/
noncomputable def uliftTermStructure (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) :
    Structure L (ULift.{u} ℕ) :=
  @Structure.ofEquiv L ℕ (termStructure hEq H) (ULift.{u} ℕ) Equiv.ulift.symm

/-- The transported term model satisfies `T`. -/
theorem models_theory_ulift (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) :
    Language.str (s := uliftTermStructure hEq H) (ULift.{u} ℕ) L ⊧* T := by
  refine Semantics.modelsSet_iff.mpr fun σ hσ ↦ ?_
  have h : Semiformula.Eval (s := termStructure hEq H) ![] (Empty.elim : Empty → ℕ) σ :=
    Semantics.modelsSet_iff.mp (models_theory hEq H) hσ
  show Semiformula.Eval (s := uliftTermStructure hEq H) ![] Empty.elim σ
  rw [uliftTermStructure, eval_ulift (s := termStructure hEq H)]
  simpa [Matrix.empty_eq, Empty.eq_elim] using h

/-- The transported term model omits every type of the family. -/
theorem omits_type_ulift (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) (n : ℕ) :
    @Omits L (ULift.{u} ℕ) (uliftTermStructure hEq H) (q n) (Ψ n) := by
  intro c
  obtain ⟨ψ, hψΨ, hψ⟩ := omits_type hEq H n fun i ↦ (c i).down
  refine ⟨ψ, hψΨ, ?_⟩
  intro hev
  refine hψ ?_
  have h : Semiformula.Eval (s := uliftTermStructure hEq H) c Empty.elim ψ := hev
  rw [uliftTermStructure, eval_ulift (s := termStructure hEq H)] at h
  simpa [Function.comp_def, Empty.eq_elim] using h

/-- The model the omitting types theorem asks for, read off a Henkin set: a countable model of `T`
omitting every type of the family. -/
noncomputable def omittingModel (hEq : 𝗘𝗤 L ⊆ T) (H : HenkinSet T Ψ) : OmittingModel T Ψ where
  Dom := ULift.{u} ℕ
  nonempty := ⟨⟨0⟩⟩
  str := uliftTermStructure hEq H
  countable := inferInstance
  models := models_theory_ulift hEq H
  omits := omits_type_ulift hEq H

end ZFVP
