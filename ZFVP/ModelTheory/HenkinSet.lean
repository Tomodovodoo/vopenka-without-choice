import ZFVP.ModelTheory.HenkinConsistency
import ZFVP.ModelTheory.OmittingTypes

/-! # The maximal Henkin set for the omitting types theorem

A Henkin construction inside `Foundation`'s first-order syntax whose witnesses are fresh *free
variables* rather than new constants. `Proposition L = SyntacticFormula L` already has free
variables indexed by `ℕ`, so no expansion of the language is needed, and `ConsistentOver T H`
from `ZFVP.ModelTheory.HenkinConsistency` is the right notion of consistency for a set `H` of
such formulas.

The structure `HenkinSet T Ψ` packages what a term model needs: a set of propositions consistent
over `T`, complete, witnessed for every existential formula it contains (with witnesses escaping
any prescribed finite set of variables), and, for every injective tuple of variables, refuting
some member of every type `Ψ n`. The omitting requirement enters `exists_henkinSet` as the
hypothesis `hchoose`, so this file does not mention local omission and stays independent of the
machinery that will supply `hchoose`.

The construction runs through finite stages `Δ 0 = [] ⊆ Δ 1 ⊆ ⋯`, each consistent over `T`, and
does three jobs at every stage: decide the `k`-th proposition, feed a witness to the `k.unpair.1`-th
proposition if it is an existential formula already present, and refute a member of the type named
by the `k`-th entry of a surjection onto the omitting jobs. The witness variable is taken to be
`max Δ.newVar k.unpair.2`, above both everything occurring in the stage (so the witness step of
`HenkinConsistency` applies) and the second pairing component (so that letting that component grow
pushes the witness past any finite set).
-/

namespace ZFVP

open LO LO.FirstOrder

variable {L : Language}

/-! ### Substituting free variables for the bound variables of a sentence -/

/-- `substTuple ψ a` replaces the `k` bound variables of the sentence `ψ : Semisentence L k` by the
free variables `&(a 0), …, &(a (k-1))`. -/
def substTuple {k : ℕ} (ψ : Semisentence L k) (a : Fin k → ℕ) : Proposition L :=
  Rew.embSubsts (fun i ↦ (&(a i) : SyntacticTerm L)) ▹ ψ

/-- Evaluating `substTuple ψ a` under an assignment `ε` of the free variables is evaluating `ψ` at
the tuple `fun i ↦ ε (a i)`. -/
@[simp] theorem eval_substTuple {M : Type*} [Structure L M] {k : ℕ}
    (ψ : Semisentence L k) (a : Fin k → ℕ) (ε : ℕ → M) :
    Semiformula.Eval ![] ε (substTuple ψ a) ↔ Semiformula.Evalb (fun i ↦ ε (a i)) ψ := by
  simp [substTuple, Function.comp_def]

/-! ### The structure -/

/-- A maximal Henkin set over `T` omitting the family of types `Ψ`: a set of propositions,
consistent over `T`, deciding every proposition, containing a witness `φ/[&m]` for every
existential member `∃¹ φ` with `m` outside any prescribed finite set of variables, and refuting a
member of `Ψ n` at every injective tuple of free variables. -/
structure HenkinSet (T : Theory L) {q : ℕ → ℕ} (Ψ : (n : ℕ) → PartialType L (q n)) where
  /-- The set of propositions. -/
  carrier : Set (Proposition L)
  /-- It is consistent together with the axioms of `T`. -/
  consistent : ConsistentOver T carrier
  /-- It decides every proposition. -/
  mem_or_neg_mem : ∀ φ : Proposition L, φ ∈ carrier ∨ ∼φ ∈ carrier
  /-- Every existential member has witnesses with arbitrarily large variables. -/
  witness : ∀ φ : Semiproposition L 1, (∃¹ φ) ∈ carrier → ∀ F : Finset ℕ,
      ∃ m ∉ F, φ/[&m] ∈ carrier
  /-- At every injective tuple of free variables it refutes a member of every type. -/
  omits : ∀ (n : ℕ) (a : Fin (q n) → ℕ), Function.Injective a →
      ∃ ψ ∈ Ψ n, ∼(substTuple ψ a) ∈ carrier

/-! ### Freshness above `newVar` -/

private lemma fvSup_le_newVar {Γ : Sequent L} {ψ : Proposition L} (h : ψ ∈ Γ) :
    ψ.fvSup ≤ Γ.newVar := by
  simp only [Sequent.newVar]
  exact List.le_max_of_le (List.mem_map_of_mem h) (le_refl _)

/-- Any variable at or above `Γ.newVar` is free in no member of `Γ`. -/
private lemma not_fvar?_of_newVar_le {Γ : Sequent L} {ψ : Proposition L} (h : ψ ∈ Γ) {m : ℕ}
    (hm : Γ.newVar ≤ m) : ¬ψ.FVar? m :=
  Semiformula.not_fvar?_of_lt_fvSup ψ (le_trans (fvSup_le_newVar h) hm)

/-! ### One stage of the construction -/

private lemma setOf_mem_cons (χ : Proposition L) (Δ : List (Proposition L)) :
    {φ : Proposition L | φ ∈ χ :: Δ} = insert χ {φ | φ ∈ Δ} := by
  ext φ; simp

section Construction

variable {q : ℕ → ℕ}

/-- An omitting job: a type index `n` together with an injective tuple of free variables. -/
private abbrev OmitJob (q : ℕ → ℕ) : Type :=
  Σ n : ℕ, {a : Fin (q n) → ℕ // Function.Injective a}

/-- What one stage of the construction achieves: the stage grows, stays consistent, decides the
`k`-th proposition, witnesses the `k.unpair.1`-th proposition when that is an existential formula
already present, and refutes a member of the type named by the `k`-th omitting job. -/
private def StepSpec (T : Theory L) (Ψ : (n : ℕ) → PartialType L (q n))
    (e : ℕ → Proposition L) (o : ℕ → OmitJob q) (k : ℕ) (Δ Δ' : List (Proposition L)) : Prop :=
  Δ ⊆ Δ' ∧ ConsistentOver T {φ | φ ∈ Δ'} ∧
    (e k ∈ Δ' ∨ ∼(e k) ∈ Δ') ∧
    (∀ φ : Semiproposition L 1, e k.unpair.1 = ∃¹ φ → (∃¹ φ) ∈ Δ →
      ∃ m, k.unpair.2 ≤ m ∧ φ/[&m] ∈ Δ') ∧
    (∃ ψ ∈ Ψ (o k).1, ∼(substTuple ψ (o k).2.1) ∈ Δ')

/-- The hypothesis that drives the omitting step: every consistent finite stage can be extended by
the negation of some member of `Ψ n` at the tuple `a`. -/
private def Chooser (T : Theory L) (Ψ : (n : ℕ) → PartialType L (q n)) : Prop :=
  ∀ (n : ℕ) (a : Fin (q n) → ℕ), Function.Injective a →
    ∀ Δ : List (Proposition L), ConsistentOver T {φ | φ ∈ Δ} →
    ∃ ψ ∈ Ψ n, ConsistentOver T {φ | φ ∈ (∼(substTuple ψ a) :: Δ)}

private lemma exists_step (T : Theory L) (Ψ : (n : ℕ) → PartialType L (q n))
    (hchoose : Chooser T Ψ) (e : ℕ → Proposition L) (o : ℕ → OmitJob q) (k : ℕ)
    (Δ : List (Proposition L)) (h : ConsistentOver T {φ | φ ∈ Δ}) :
    ∃ Δ', StepSpec T Ψ e o k Δ Δ' := by
  -- decision
  obtain ⟨Δ₁, hsub₁, hcon₁, hdec⟩ :
      ∃ Δ₁, Δ ⊆ Δ₁ ∧ ConsistentOver T {φ | φ ∈ Δ₁} ∧ (e k ∈ Δ₁ ∨ ∼(e k) ∈ Δ₁) := by
    rcases consistentOver_insert_or h (e k) with hc | hc
    · exact ⟨e k :: Δ, List.subset_cons_self _ _, by rw [setOf_mem_cons]; exact hc,
        Or.inl (by simp)⟩
    · exact ⟨∼(e k) :: Δ, List.subset_cons_self _ _, by rw [setOf_mem_cons]; exact hc,
        Or.inr (by simp)⟩
  -- witness
  obtain ⟨Δ₂, hsub₂, hcon₂, hwit⟩ :
      ∃ Δ₂, Δ₁ ⊆ Δ₂ ∧ ConsistentOver T {φ | φ ∈ Δ₂} ∧
        ∀ φ : Semiproposition L 1, e k.unpair.1 = ∃¹ φ → (∃¹ φ) ∈ Δ₁ →
          ∃ m, k.unpair.2 ≤ m ∧ φ/[&m] ∈ Δ₂ := by
    by_cases hex : ∃ φ : Semiproposition L 1, e k.unpair.1 = ∃¹ φ
    · obtain ⟨φ, hφ⟩ := hex
      by_cases hmem : (∃¹ φ) ∈ Δ₁
      · refine ⟨φ/[&(max (Sequent.newVar Δ₁) k.unpair.2)] :: Δ₁, List.subset_cons_self _ _, ?_, ?_⟩
        · rw [setOf_mem_cons]
          exact consistentOver_insert_subst hcon₁ hmem
            fun ψ hψ ↦ not_fvar?_of_newVar_le hψ (le_max_left _ _)
        · intro φ' hφ' _
          have : φ' = φ := by
            have : (∃¹ φ' : Proposition L) = ∃¹ φ := by rw [← hφ', hφ]
            simpa using this
          subst this
          exact ⟨max (Sequent.newVar Δ₁) k.unpair.2, le_max_right _ _, by simp⟩
      · refine ⟨Δ₁, List.Subset.refl _, hcon₁, ?_⟩
        intro φ' hφ' hmem'
        have : φ' = φ := by
          have : (∃¹ φ' : Proposition L) = ∃¹ φ := by rw [← hφ', hφ]
          simpa using this
        subst this
        exact absurd hmem' hmem
    · exact ⟨Δ₁, List.Subset.refl _, hcon₁, fun φ' hφ' _ ↦ absurd ⟨φ', hφ'⟩ hex⟩
  -- omitting
  obtain ⟨ψ, hψΨ, hcon₃⟩ := hchoose (o k).1 (o k).2.1 (o k).2.2 Δ₂ hcon₂
  refine ⟨∼(substTuple ψ (o k).2.1) :: Δ₂, ?_, hcon₃, ?_, ?_, ⟨ψ, hψΨ, by simp⟩⟩
  · exact fun x hx ↦ List.mem_cons_of_mem _ (hsub₂ (hsub₁ hx))
  · rcases hdec with hd | hd
    · exact Or.inl (List.mem_cons_of_mem _ (hsub₂ hd))
    · exact Or.inr (List.mem_cons_of_mem _ (hsub₂ hd))
  · intro φ hφ hmem
    obtain ⟨m, hm, hmem'⟩ := hwit φ hφ (hsub₁ hmem)
    exact ⟨m, hm, List.mem_cons_of_mem _ hmem'⟩

/-- The stages of the construction, as a sequence of finite lists each consistent over `T`. -/
private noncomputable def stageSeq (T : Theory L) (Ψ : (n : ℕ) → PartialType L (q n))
    (hT : Entailment.Consistent T) (hchoose : Chooser T Ψ) (e : ℕ → Proposition L)
    (o : ℕ → OmitJob q) : (k : ℕ) → {Δ : List (Proposition L) // ConsistentOver T {φ | φ ∈ Δ}}
  | 0 => ⟨[], by
      have : {φ : Proposition L | φ ∈ ([] : List (Proposition L))} = ∅ := by ext φ; simp
      rw [this]
      exact consistentOver_empty_iff.mpr hT⟩
  | k + 1 =>
      ⟨(exists_step T Ψ hchoose e o k (stageSeq T Ψ hT hchoose e o k).1
          (stageSeq T Ψ hT hchoose e o k).2).choose,
        (exists_step T Ψ hchoose e o k (stageSeq T Ψ hT hchoose e o k).1
          (stageSeq T Ψ hT hchoose e o k).2).choose_spec.2.1⟩

private lemma stageSeq_spec (T : Theory L) (Ψ : (n : ℕ) → PartialType L (q n))
    (hT : Entailment.Consistent T) (hchoose : Chooser T Ψ) (e : ℕ → Proposition L)
    (o : ℕ → OmitJob q) (k : ℕ) :
    StepSpec T Ψ e o k (stageSeq T Ψ hT hchoose e o k).1
      (stageSeq T Ψ hT hchoose e o (k + 1)).1 :=
  (exists_step T Ψ hchoose e o k (stageSeq T Ψ hT hchoose e o k).1
    (stageSeq T Ψ hT hchoose e o k).2).choose_spec

private lemma stageSeq_mono (T : Theory L) (Ψ : (n : ℕ) → PartialType L (q n))
    (hT : Entailment.Consistent T) (hchoose : Chooser T Ψ) (e : ℕ → Proposition L)
    (o : ℕ → OmitJob q) :
    Monotone fun k ↦ {φ : Proposition L | φ ∈ (stageSeq T Ψ hT hchoose e o k).1} := by
  refine monotone_nat_of_le_succ fun k φ hφ ↦ ?_
  exact (stageSeq_spec T Ψ hT hchoose e o k).1 hφ

end Construction

/-! ### Existence -/

section Existence

variable [L.Encodable]

private noncomputable def propEnum (L : Language) [L.Encodable] (k : ℕ) : Proposition L :=
  (Encodable.decode k).getD ⊤

private lemma propEnum_surjective (φ : Proposition L) :
    propEnum L (Encodable.encode φ) = φ := by
  simp [propEnum]

/-- A maximal Henkin set exists: given a consistent theory and a rule `hchoose` for refuting some
member of each type at each injective tuple of variables, the stagewise construction closes off to
a `HenkinSet`. -/
theorem exists_henkinSet (T : Theory L) (hT : Entailment.Consistent T)
    {q : ℕ → ℕ} (Ψ : (n : ℕ) → PartialType L (q n))
    (hchoose : ∀ (n : ℕ) (a : Fin (q n) → ℕ), Function.Injective a →
        ∀ Δ : List (Proposition L), ConsistentOver T {φ | φ ∈ Δ} →
        ∃ ψ ∈ Ψ n, ConsistentOver T {φ | φ ∈ (∼(substTuple ψ a) :: Δ)}) :
    Nonempty (HenkinSet T Ψ) := by
  have hne : Nonempty (OmitJob q) := ⟨⟨0, ⟨fun i ↦ (i : ℕ), Fin.val_injective⟩⟩⟩
  obtain ⟨o, hosurj⟩ := exists_surjective_nat (OmitJob q)
  set e : ℕ → Proposition L := propEnum L with he
  set S : ℕ → {Δ : List (Proposition L) // ConsistentOver T {φ | φ ∈ Δ}} :=
    stageSeq T Ψ hT hchoose e o with hS
  set H : Set (Proposition L) := {φ | ∃ k, φ ∈ (S k).1} with hH
  have hspec : ∀ k, StepSpec T Ψ e o k (S k).1 (S (k + 1)).1 :=
    fun k ↦ stageSeq_spec T Ψ hT hchoose e o k
  have hmono : Monotone fun k ↦ {φ : Proposition L | φ ∈ (S k).1} :=
    stageSeq_mono T Ψ hT hchoose e o
  have hHU : H = ⋃ k, {φ : Proposition L | φ ∈ (S k).1} := by
    ext φ; simp [hH]
  refine ⟨{ carrier := H
            consistent := ?_
            mem_or_neg_mem := ?_
            witness := ?_
            omits := ?_ }⟩
  · rw [hHU]
    exact consistentOver_iUnion hmono fun k ↦ (S k).2
  · intro φ
    have h := (hspec (Encodable.encode φ)).2.2.1
    rw [show e (Encodable.encode φ) = φ from propEnum_surjective φ] at h
    rcases h with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr ⟨_, h⟩
  · rintro φ ⟨k₀, hk₀⟩ F
    set r : ℕ := max k₀ (F.sup id + 1) with hr
    set k : ℕ := Nat.pair (Encodable.encode (∃¹ φ : Proposition L)) r with hk
    have hk₀le : k₀ ≤ k := le_trans (le_max_left _ _) (hk ▸ Nat.right_le_pair _ _)
    have hmemk : (∃¹ φ : Proposition L) ∈ (S k).1 := hmono hk₀le hk₀
    have hfst : e k.unpair.1 = ∃¹ φ := by
      rw [hk, Nat.unpair_pair]
      exact propEnum_surjective _
    obtain ⟨m, hm, hmem⟩ := (hspec k).2.2.2.1 φ hfst hmemk
    rw [hk, Nat.unpair_pair] at hm
    refine ⟨m, ?_, ⟨k + 1, hmem⟩⟩
    intro hmF
    have h1 : (F.sup id : ℕ) + 1 ≤ m := le_trans (le_max_right _ _) hm
    have h2 : m ≤ F.sup id := Finset.le_sup (f := id) hmF
    omega
  · intro n a ha
    obtain ⟨k, hk⟩ := hosurj ⟨n, ⟨a, ha⟩⟩
    have h := (hspec k).2.2.2.2
    rw [hk] at h
    obtain ⟨ψ, hψΨ, hψmem⟩ := h
    exact ⟨ψ, hψΨ, ⟨k + 1, hψmem⟩⟩

end Existence

/-! ### What a term model reads off a Henkin set -/

variable {T : Theory L} {q : ℕ → ℕ} {Ψ : (n : ℕ) → PartialType L (q n)}

/-- A Henkin set never contains a proposition together with its negation. -/
theorem HenkinSet.not_mem_iff (H : HenkinSet T Ψ) (φ : Proposition L) :
    φ ∉ H.carrier ↔ ∼φ ∈ H.carrier := by
  constructor
  · intro hφ
    rcases H.mem_or_neg_mem φ with h | h
    · exact absurd h hφ
    · exact h
  · intro hn hp
    refine H.consistent [φ, ∼φ] ?_ ⟨[], by simp, ⟨Derivation.close φ (by simp) (by simp)⟩⟩
    intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | hχ
    · exact hp
    · rcases List.mem_cons.mp hχ with rfl | hχ
      · exact hn
      · simp at hχ

/-- A Henkin set is deductively closed: if `∼φ` together with members of the set is refutable over
`T`, then `φ` belongs to the set. -/
theorem HenkinSet.mem_of_refutable_neg (H : HenkinSet T Ψ) {φ : Proposition L}
    (Δ : List (Proposition L)) (hΔ : ∀ χ ∈ Δ, χ ∈ H.carrier) (h : Refutable T (∼φ :: Δ)) :
    φ ∈ H.carrier := by
  by_contra hφ
  refine H.consistent (∼φ :: Δ) ?_ h
  intro χ hχ
  rcases List.mem_cons.mp hχ with rfl | hχ
  · exact (H.not_mem_iff φ).mp hφ
  · exact hΔ χ hχ

/-- The axioms of `T` belong to a Henkin set over `T`. -/
theorem HenkinSet.axioms_mem (H : HenkinSet T Ψ) {σ : Sentence L} (hσ : σ ∈ T) :
    (Rewriting.emb σ : Proposition L) ∈ H.carrier := by
  refine H.mem_of_refutable_neg [] (by simp) ⟨[σ], by simpa using hσ, ⟨?_⟩⟩
  exact Derivation.close (Rewriting.emb σ : Proposition L) (by simp) (by simp)

end ZFVP
