import Foundation.FirstOrder.Completeness.CounterModel
import ZFVP.ModelTheory.HenkinConsistency

/-! # A finite stage of a Henkin construction is consistent iff it has a model

`ZFVP.ConsistentOver T H` is a syntactic notion: no finite list of members of `H` can be refuted
from finitely many axioms of `T`. This file identifies it, for a finite `H` given by a list `Δ` of
formulas with free variables, with the existence of a model of `T` together with an assignment of
its free variables making every member of `Δ` true.

The bridge is the sentence `stageClosure Δ`, the existential closure of the conjunction of `Δ`,
whose negation `stageDenial Δ` is the universal closure of the negation of that conjunction.
A structure satisfies `stageClosure Δ` exactly when some assignment satisfies all of `Δ`
(`models_stageClosure_iff`), and `Δ` is refutable over `T` exactly when `T` proves `stageDenial Δ`
(`refutable_iff_provable_stageDenial`). Completeness for theories of sentences then gives the
model.

The two derivation-level lemmas that make the syntactic half work are `exsClosureIntro`, which
introduces all the quantifiers of an existential closure at once in front of a context, and
`allClosureFixitr`, which introduces all the quantifiers of a universal closure in front of a
context that is invariant under shifting.
-/

namespace ZFVP

open LO LO.FirstOrder LO.Entailment

universe u

variable {L : Language.{u}} {T : Theory L}

/-! ### Substituting every bound variable of a closure at once -/

/-- Peeling the outermost substituted term off a simultaneous substitution. -/
private lemma subst_q_subst {n : ℕ} (χ : Semiproposition L (n + 1))
    (w : Fin (n + 1) → SyntacticTerm L) :
    ((Rew.subst (fun i ↦ w i.succ)).q ▹ χ) ⇜ ![w 0] = χ ⇜ w := by
  have e : (Rew.subst ![w 0]).comp (Rew.subst (fun i ↦ w i.succ)).q = Rew.subst w := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => simp [Rew.comp_app]
    · simp [Rew.comp_app]
  show Rew.subst ![w 0] ▹ ((Rew.subst (fun i ↦ w i.succ)).q ▹ χ) = Rew.subst w ▹ χ
  rw [← TransitiveRewriting.comp_app, e]

/-- Introduce all the quantifiers of the existential closure `∃¹* χ` at once, using the terms `w`,
in front of an arbitrary context. -/
def exsClosureIntro {Γ : Sequent L} :
    {n : ℕ} → (χ : Semiproposition L n) → (w : Fin n → SyntacticTerm L) →
      ⊢ᴸᴷ¹ (χ ⇜ w) :: Γ → ⊢ᴸᴷ¹ (∃¹* χ) :: Γ
  | 0, _, _, d => Derivation.cast d (by simp)
  | _ + 1, χ, w, d =>
      exsClosureIntro (∃¹ χ) (fun i ↦ w i.succ)
        (Derivation.cast
          (Derivation.exs (t := w 0) (Derivation.cast d (by rw [subst_q_subst]))) (by simp))

/-- Introduce all the quantifiers of the universal closure of `φ` in front of a context that is
invariant under shifting. -/
def allClosureFixitr {Λ : Sequent L} (hΛ : Λ⁺ = Λ) {φ : Proposition L} (d : ⊢ᴸᴷ¹ φ :: Λ) :
    (m : ℕ) → ⊢ᴸᴷ¹ (∀¹* (Rew.fixitr 0 m ▹ φ)) :: Λ
  | 0 => Derivation.cast d (by simp)
  | m + 1 => by
      rw [LawfulSyntacticRewriting.allClosure_fixitr]
      refine Derivation.all (Derivation.cast (allClosureFixitr hΛ d m) ?_)
      rw [hΛ]; simp

/-! ### The closure of a finite stage -/

/-- The sentence saying that no assignment of the free variables makes every member of `Δ` true:
the universal closure of the negation of the conjunction of `Δ`. -/
def stageDenial (Δ : List (Proposition L)) : Sentence L := Semiformula.univCl (∼⋀Δ)

/-- The sentence saying that some assignment of the free variables makes every member of `Δ` true:
the existential closure of the conjunction of `Δ`. -/
def stageClosure (Δ : List (Proposition L)) : Sentence L := ∼stageDenial Δ

@[simp] theorem neg_stageClosure (Δ : List (Proposition L)) :
    ∼stageClosure Δ = stageDenial Δ := by simp [stageClosure]

/-! ### The semantic half -/

private lemma evalf_conj {M : Type*} [Structure L M] (ε : ℕ → M) (Δ : List (Proposition L)) :
    Semiformula.Evalf ε (⋀Δ : Proposition L) ↔ ∀ φ ∈ Δ, Semiformula.Eval ![] ε φ :=
  List.map_conj₂_prop

/-- A structure satisfies `stageClosure Δ` exactly when some assignment of the free variables
makes every member of `Δ` true. -/
theorem models_stageClosure_iff {M : Type*} [Nonempty M] [Structure L M]
    (Δ : List (Proposition L)) :
    M↓[L] ⊧ stageClosure Δ ↔ ∃ ε : ℕ → M, ∀ φ ∈ Δ, Semiformula.Eval ![] ε φ := by
  have h : M↓[L] ⊧ stageDenial Δ ↔ ∀ ε : ℕ → M, ¬∀ φ ∈ Δ, Semiformula.Eval ![] ε φ := by
    rw [stageDenial, models_iff_proposition]
    refine forall_congr' fun ε ↦ ?_
    rw [LogicalConnective.HomClass.map_neg, evalf_conj]
    rfl
  rw [stageClosure, Semantics.Not.models_not, h]
  push Not
  rfl

/-! ### The syntactic half -/

private lemma shifts_embed_neg (A : List (Sentence L)) :
    (∼Sequent.embed A : Sequent L)⁺ = ∼Sequent.embed A := by
  rw [Rewriting.shifts_neg, Sequent.embed_shift]

private lemma fvSup_neg (φ : Proposition L) : (∼φ).fvSup = φ.fvSup := by
  simp [Semiformula.fvSup]

/-- Strip the universal closure `ψ.univCl'` down to `ψ` in front of an arbitrary context, by
instantiating every quantifier at the free variable it came from. -/
def univCl'Inst {Λ : Sequent L} {ψ : Proposition L} (d : ⊢ᴸᴷ¹ ψ.univCl' :: Λ) : ⊢ᴸᴷ¹ ψ :: Λ := by
  have base : ⊢ᴸᴷ¹ ((Rew.fixitr 0 ψ.fvSup ▹ (∼ψ))
      ⇜ (fun x : Fin (0 + ψ.fvSup) ↦ (&(x : ℕ) : SyntacticTerm L))) :: [ψ] := by
    have e : (∼ψ).fvSup = ψ.fvSup := fvSup_neg ψ
    have d' : ⊢ᴸᴷ¹ (∼ψ) :: [ψ] := Derivation.close ψ (by simp) (by simp)
    refine Derivation.cast d' ?_
    rw [← e, Semiformula.subst_comp_fixitr]
  have aux : ⊢ᴸᴷ¹ (∼ψ.univCl') :: [ψ] := by
    refine Derivation.cast (exsClosureIntro _ _ base) ?_
    simp [Semiformula.univCl']
  refine (Derivation.cut d aux).contraction ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_cons_of_mem _ hx
  · rcases List.mem_singleton.mp hx with rfl
    exact List.mem_cons_self

/-- If `Δ` is refutable over `T` then `T` proves that no assignment satisfies all of `Δ`. -/
theorem provable_stageDenial_of_refutable {Δ : List (Proposition L)} (h : Refutable T Δ) :
    T ⊢ stageDenial Δ := by
  obtain ⟨A, hA, ⟨d⟩⟩ := h
  have d₁ : ⊢ᴸᴷ¹ (∼⋀Δ : Proposition L) :: ∼Sequent.embed A := by
    have := OneSidedLK.disj₂ (𝔇 := Derivation (L := L)) d
    simpa using this
  have d₂ : ⊢ᴸᴷ¹ ((∼⋀Δ : Proposition L).univCl') :: ∼Sequent.embed A :=
    allClosureFixitr (shifts_embed_neg A) d₁ _
  refine Theory.Proof.provable_iff.mpr ⟨A, hA, ⟨Derivation.cast d₂ ?_⟩⟩
  simp [stageDenial]

/-- If `T` proves that no assignment satisfies all of `Δ` then `Δ` is refutable over `T`. -/
theorem refutable_of_provable_stageDenial {Δ : List (Proposition L)} (h : T ⊢ stageDenial Δ) :
    Refutable T Δ := by
  obtain ⟨A, hA, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp h
  have d₀ : ⊢ᴸᴷ¹ (∼⋀Δ : Proposition L).univCl' :: ∼Sequent.embed A :=
    Derivation.cast d (by simp [stageDenial])
  have d₁ : ⊢ᴸᴷ¹ (∼⋀Δ : Proposition L) :: ∼Sequent.embed A := univCl'Inst d₀
  have dc : ⊢ᴸᴷ¹ (⋀Δ : Proposition L) :: ∼Δ :=
    OneSidedLK.conj₂ (𝔇 := Derivation (L := L)) (Δ := ∼Δ)
      fun φ hφ ↦ Derivation.close φ (by simp) (by simp [hφ])
  exact ⟨A, hA, ⟨Derivation.cut dc d₁⟩⟩

/-- `Δ` is refutable over `T` exactly when `T` proves that no assignment satisfies all of `Δ`. -/
theorem refutable_iff_provable_stageDenial {Δ : List (Proposition L)} :
    Refutable T Δ ↔ T ⊢ stageDenial Δ :=
  ⟨provable_stageDenial_of_refutable, refutable_of_provable_stageDenial⟩

/-- `Δ` is refutable over `T` exactly when `T` refutes the closure of `Δ`. -/
theorem refutable_iff_provable_neg_stageClosure {Δ : List (Proposition L)} :
    Refutable T Δ ↔ T ⊢ ∼stageClosure Δ := by
  rw [refutable_iff_provable_stageDenial, neg_stageClosure]

/-- `Δ` is unrefutable over `T` exactly when `T` together with the closure of `Δ` is consistent. -/
theorem not_refutable_iff_consistent_insert {Δ : List (Proposition L)} :
    ¬Refutable T Δ ↔ Consistent (insert (stageClosure Δ) T) := by
  have : DecidableEq (Sentence L) := Classical.decEq _
  rw [refutable_iff_provable_neg_stageClosure]
  have h := unprovable_iff_consistent_adjoin (𝓢 := T) (φ := ∼stageClosure Δ)
  rw [show (∼∼stageClosure Δ) = stageClosure Δ from by simp [stageClosure]] at h
  exact h

/-! ### Consistency over a finite stage -/

/-- Consistency over `T` of the set of members of a list is just unrefutability of that list. -/
theorem consistentOver_list_iff (T : Theory L) (Δ : List (Proposition L)) :
    ConsistentOver T {φ | φ ∈ Δ} ↔ ¬Refutable T Δ := by
  constructor
  · intro h; exact h Δ (fun φ hφ ↦ hφ)
  · intro h Δ' hΔ' hr; exact h (hr.mono hΔ')

/-! ### The two halves of the main theorem -/

/-- Soundness half: a model of `T` with an assignment satisfying every member of `Δ` shows that no
sublist of `Δ` is refutable over `T`. -/
theorem consistentOver_list_of_model {Δ : List (Proposition L)} {M : Type*} [Nonempty M]
    [Structure L M] (hT : M↓[L] ⊧* T) (ε : ℕ → M) (hε : ∀ φ ∈ Δ, Semiformula.Eval ![] ε φ) :
    ConsistentOver T {φ | φ ∈ Δ} := by
  rw [consistentOver_list_iff]
  rintro ⟨A, hA, ⟨d⟩⟩
  obtain ⟨χ, hχ, hval⟩ := Derivation.sound ε d
  rcases List.mem_append.mp hχ with hχ | hχ
  · rw [List.tilde_def] at hχ
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hχ
    have : ¬Semiformula.Evalf ε φ := by simpa using hval
    exact this (hε φ hφ)
  · rw [List.tilde_def] at hχ
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hχ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hφ
    have hσM : M↓[L] ⊧ σ := Semantics.modelsSet_iff.mp hT (hA σ hσ)
    rw [models_iff] at hσM
    have hne : ¬Semiformula.Evalf ε (Rewriting.emb σ : Proposition L) := by simpa using hval
    exact hne (by simpa using hσM)

/-- Completeness half: a list consistent over `T` has a model of `T` with an assignment satisfying
every member of the list. -/
theorem exists_model_of_consistentOver_list {Δ : List (Proposition L)}
    (h : ConsistentOver T {φ | φ ∈ Δ}) :
    ∃ (M : Type u) (_ : Nonempty M) (_ : Structure L M) (ε : ℕ → M),
      M↓[L] ⊧* T ∧ ∀ φ ∈ Δ, Semiformula.Eval ![] ε φ := by
  have hcon : Consistent (insert (stageClosure Δ) T) :=
    not_refutable_iff_consistent_insert.mp ((consistentOver_list_iff T Δ).mp h)
  obtain ⟨M, hM, hs, hmod⟩ :=
    LO.FirstOrder.satisfiable_iff.mp (Theory.small_satisfiable_of_consistent hcon)
  have hc : M↓[L] ⊧ stageClosure Δ := Semantics.modelsSet_iff.mp hmod (Set.mem_insert _ _)
  obtain ⟨ε, hε⟩ := (models_stageClosure_iff Δ).mp hc
  exact ⟨M, hM, hs, ε, Semantics.ModelsSet.of_subset hmod (Set.subset_insert _ _), hε⟩

/-- A finite stage of a Henkin construction is consistent over `T` exactly when `T` has a model
with an assignment of the free variables satisfying every formula of the stage. -/
theorem consistentOver_list_iff_exists_model (Δ : List (Proposition L)) :
    ConsistentOver T {φ | φ ∈ Δ} ↔
      ∃ (M : Type u) (_ : Nonempty M) (_ : Structure L M) (ε : ℕ → M),
        M↓[L] ⊧* T ∧ ∀ φ ∈ Δ, Semiformula.Eval ![] ε φ := by
  constructor
  · exact exists_model_of_consistentOver_list
  · rintro ⟨M, _, _, ε, hT, hε⟩
    exact consistentOver_list_of_model hT ε hε

end ZFVP
