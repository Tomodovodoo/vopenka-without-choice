import Foundation.FirstOrder.Completeness.CounterModel

/-! # The Henkin-Orey omitting types theorem

Chang and Keisler, Theorem 2.2.9. Let `L` be a countable language and `T` a consistent
`L`-theory. Suppose that for each `n` we are given a set `Ψ n` of `L`-formulas in `q n` free
variables which `T` locally omits. Then `T` has a countable model omitting every `Ψ n`.

Enayat's Appendix uses this for the successor step of Rubin's construction (his Lemma A.2), so
the statement here is the full one: types in finitely many free variables, over an arbitrary
consistent theory, countably many of them at once.

What this file contains:

* the three definitions (`PartialType`, `Omits`, `LocallyOmits`) in the form Chang and Keisler
  state them;
* `OmittingTypesTheorem`, the theorem as a named `Prop`, together with the structure
  `OmittingModel` that packages the model it produces;
* the lemmas around the statement that are proved here: the converse direction for complete
  theories (`locallyOmits_of_omits`), the fact that a principal type is never locally omitted
  (`not_locallyOmits_of_principal`), and the non-vacuity of local omission
  (`LocallyOmits.nonempty`).

`OmittingTypesTheorem` itself is *not* proved here. The vendored `Foundation` library proves
completeness by forcing over the poset of cut-free consistent sequents
(`Foundation/FirstOrder/Completeness/CounterModel.lean`), and a condition there is a finite
sequent with no theory attached: the forcing relation is defined from cut-free provability and
its key property, `IsWeaklyForced.complete`, rests on the Hauptsatz. Infinite theories are
reached only afterwards, by compactness plus an ultraproduct
(`Theory.small_satisfiable_of_consistent`), and an ultraproduct realizes every type one wants
omitted. Running the forcing over conditions consistent with `T` therefore needs a `T`-relative
cut elimination, which `Foundation` does not have. `Foundation` does have the relativized
entailment `T ⊢ φ` with the deduction theorem (`Entailment.Deduction (Theory L)`) and compactness,
so `ConsistentSequentOver T` is cheap to define, but none of the forcing lemmas transfer to it.
The other route, a Henkin construction with new constants and a term model, would have to be
built from scratch: `Foundation` contains no Henkin theories, no witness expansion and no term
model over a complete theory.

The statement is therefore exported unproved so that everything using it carries it as a visible
hypothesis, the same way `RubinShelahSchmerl` is handled in
`ZFVP.ModelTheory.CountabilityEssential`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.Entailment

universe u v w

variable {L : Language.{u}}

/-! ### The three notions -/

/-- A type in `q` free variables: a set of `L`-formulas all of whose variables are among
`x₀, …, x_{q-1}`. This is Chang and Keisler's `Σ(x₁, …, x_q)` from Section 2.2. -/
abbrev PartialType (L : Language.{u}) (q : ℕ) : Type u := Set (Semisentence L q)

/-- `Omits M Ψ` says that the structure `M` omits the type `Ψ`: no `q`-tuple from `M` satisfies
every formula of `Ψ`. This is Chang and Keisler's "`M` omits `Σ`". -/
def Omits (M : Type v) [Structure L M] {q : ℕ} (Ψ : PartialType L q) : Prop :=
  ∀ a : Fin q → M, ∃ ψ ∈ Ψ, ¬ψ.Evalb a

/-- `LocallyOmits T Ψ` says that `T` locally omits the type `Ψ`: for every formula `θ` in the
same `q` free variables such that `T + ∃x⃗ θ(x⃗)` is consistent there is some `ψ ∈ Ψ` with
`T + ∃x⃗ (θ(x⃗) ⋏ ∼ψ(x⃗))` consistent. This is the hypothesis of Chang and Keisler's
Theorem 2.2.9, their "`T` locally omits `Σ`"; equivalently, no `θ` consistent with `T` isolates
`Ψ` over `T`. -/
def LocallyOmits (T : Theory L) {q : ℕ} (Ψ : PartialType L q) : Prop :=
  ∀ θ : Semisentence L q, Consistent (insert (∃¹* θ) T) →
    ∃ ψ ∈ Ψ, Consistent (insert (∃¹* (θ ⋏ ∼ψ)) T)

/-! ### The conclusion of the theorem, packaged -/

/-- A countable model of `T` omitting every type in the family `Ψ`. This is what the omitting
types theorem produces. -/
structure OmittingModel {L : Language.{w}} (T : Theory L) {ι : Type*} {q : ι → ℕ}
    (Ψ : (i : ι) → PartialType L (q i)) where
  /-- The underlying type of the model. -/
  Dom : Type w
  [nonempty : Nonempty Dom]
  [str : Structure L Dom]
  [countable : Countable Dom]
  /-- It is a model of `T`. -/
  models : Dom↓[L] ⊧* T
  /-- It omits every type of the family. -/
  omits : ∀ i, Omits Dom (Ψ i)

attribute [instance] OmittingModel.nonempty OmittingModel.str OmittingModel.countable

/-- The Henkin-Orey omitting types theorem (Chang and Keisler, Theorem 2.2.9): a consistent
theory in a countable language which locally omits each of countably many types has a countable
model omitting all of them.

This development does not prove it; see the header of this file for what blocks the proof.
Anything that uses the theorem should take this `Prop` as a hypothesis. -/
def OmittingTypesTheorem : Prop :=
  ∀ (L : Language.{w}) [L.Encodable] (T : Theory L), Consistent T →
    ∀ (q : ℕ → ℕ) (Ψ : (n : ℕ) → PartialType L (q n)),
      (∀ n, LocallyOmits T (Ψ n)) → Nonempty (OmittingModel T Ψ)

/-! ### Elementary facts about omitting -/

/-- Omitting a smaller set of formulas is harder: if `M` omits `Ψ` and `Ψ ⊆ Ψ'`, then `M` omits
`Ψ'`. -/
theorem Omits.mono {M : Type v} [Structure L M] {q : ℕ} {Ψ Ψ' : PartialType L q}
    (h : Omits M Ψ) (hss : Ψ ⊆ Ψ') : Omits M Ψ' := fun a ↦
  let ⟨ψ, hψ, hne⟩ := h a
  ⟨ψ, hss hψ, hne⟩

/-- Nothing omits a set of formulas that is satisfied by no tuple only because it is empty: a
structure omits the empty type exactly when it has no `q`-tuples at all. -/
@[simp] theorem omits_empty_iff {M : Type v} [Structure L M] {q : ℕ} :
    Omits M (∅ : PartialType L q) ↔ IsEmpty (Fin q → M) := by
  constructor
  · intro h
    exact ⟨fun a ↦ by rcases h a with ⟨_, h, _⟩; exact h⟩
  · intro h a
    exact (h.false a).elim

/-! ### Consistency bookkeeping -/

/-- If `T ⊢ ∼σ` then `T` together with `σ` is inconsistent. -/
theorem not_consistent_insert_of_provable_neg {T : Theory L} {σ : Sentence L} (h : T ⊢ ∼σ) :
    ¬Consistent (insert σ T) := by
  intro hcon
  have h1 : insert σ T ⊢ σ := Entailment.Axiomatized.adjoin! σ T
  have h2 : insert σ T ⊢ ∼σ := Entailment.Axiomatized.to_adjoin h
  exact Entailment.consistent_iff_unprovable_bot.mp hcon (neg_mdp h2 h1)

/-- If `T` together with `σ` is consistent then `T` does not refute `σ`. -/
theorem unprovable_neg_of_consistent_insert {T : Theory L} {σ : Sentence L}
    (h : Consistent (insert σ T)) : T ⊬ ∼σ := fun hp ↦
  not_consistent_insert_of_provable_neg hp h

/-- A structure satisfying `T` and one further sentence witnesses that the extended theory is
consistent. -/
theorem consistent_insert_of_model {T : Theory L} {σ : Sentence L} (M : Type v) [Nonempty M]
    [Structure L M] [hT : M↓[L] ⊧* T] (hσ : M↓[L] ⊧ σ) : Consistent (insert σ T) :=
  have : M↓[L] ⊧* insert σ T := Semantics.ModelsSet.insert_iff.mpr ⟨hσ, hT⟩
  consistent_of_model (insert σ T) M

/-- Local omission is not vacuous: a consistent theory can only locally omit a nonempty set of
formulas. Taking `θ = ⊤` in the definition already forces some `ψ ∈ Ψ`. -/
theorem LocallyOmits.nonempty {T : Theory L} [hT : Consistent T] {q : ℕ} {Ψ : PartialType L q}
    (h : LocallyOmits T Ψ) : Ψ.Nonempty := by
  obtain ⟨M, _, _, hM⟩ :=
    LO.FirstOrder.satisfiable_iff.mp (Theory.small_satisfiable_of_consistent hT)
  have := hM
  have htop : M↓[L] ⊧ (∃¹* (⊤ : Semisentence L q) : Sentence L) := by
    simp [models_iff]
  obtain ⟨ψ, hψ, -⟩ := h ⊤ (consistent_insert_of_model M htop)
  exact ⟨ψ, hψ⟩

/-! ### A principal type is not locally omitted -/

/-- If some `θ` consistent with `T` implies, over `T`, every formula of `Ψ`, then `T` does not
locally omit `Ψ`. This is the standard obstruction: local omission of `Ψ` says exactly that no
formula consistent with `T` isolates `Ψ`. -/
theorem not_locallyOmits_of_principal {T : Theory L} {q : ℕ} {Ψ : PartialType L q}
    (θ : Semisentence L q) (hθ : Consistent (insert (∃¹* θ) T))
    (h : ∀ ψ ∈ Ψ, T ⊢ ∀¹* (θ 🡒 ψ)) : ¬LocallyOmits T Ψ := by
  intro hloc
  obtain ⟨ψ, hψ, hcon⟩ := hloc θ hθ
  refine not_consistent_insert_of_provable_neg (σ := ∃¹* (θ ⋏ ∼ψ)) ?_ hcon
  have : ∼(∃¹* (θ ⋏ ∼ψ)) = ∀¹* (θ 🡒 ψ) := by
    simp [Semiformula.imp_eq]
  rw [this]
  exact h ψ hψ

/-! ### The converse direction for complete theories -/

/-- The converse of the omitting types theorem for complete theories: if `T` is complete and has
a model omitting `Ψ`, then `T` locally omits `Ψ`.

Given `θ` consistent with `T`, completeness turns "`T` does not refute `∃x⃗ θ`" into
"`T` proves `∃x⃗ θ`", so the model has a tuple satisfying `θ`; omitting `Ψ` gives a `ψ ∈ Ψ` that
the tuple fails, and the model then witnesses the consistency of `T + ∃x⃗ (θ ⋏ ∼ψ)`. -/
theorem locallyOmits_of_omits {T : Theory L} (hcomplete : ∀ σ : Sentence L, T ⊢ σ ∨ T ⊢ ∼σ)
    (M : Type v) [Nonempty M] [Structure L M] [M↓[L] ⊧* T] {q : ℕ} {Ψ : PartialType L q}
    (hM : Omits M Ψ) : LocallyOmits T Ψ := by
  intro θ hθ
  have hprov : T ⊢ (∃¹* θ : Sentence L) := by
    rcases hcomplete (∃¹* θ) with h | h
    · exact h
    · exact absurd h (unprovable_neg_of_consistent_insert hθ)
  have hsat : M↓[L] ⊧ (∃¹* θ : Sentence L) :=
    consequence_iff'.mp (Theory.Proof.sound hprov) M
  have : ∃ a : Fin q → M, θ.Evalb a := by
    simpa [models_iff] using hsat
  obtain ⟨a, ha⟩ := this
  obtain ⟨ψ, hψΨ, hψ⟩ := hM a
  refine ⟨ψ, hψΨ, consistent_insert_of_model M ?_⟩
  have : ∃ b : Fin q → M, (θ ⋏ ∼ψ).Evalb b := ⟨a, by simp [ha, hψ]⟩
  simpa [models_iff] using this

/-! ### Single type as a special case -/

/-- The single type case of the omitting types theorem, read off the countable family case by
taking a constant family. -/
theorem omittingModel_of_omittingTypesTheorem (H : OmittingTypesTheorem.{w})
    (L : Language.{w}) [L.Encodable] (T : Theory L) (hT : Consistent T) {q : ℕ}
    (Ψ : PartialType L q) (hΨ : LocallyOmits T Ψ) :
    Nonempty (OmittingModel T (ι := ℕ) (q := fun _ ↦ q) fun _ ↦ Ψ) :=
  H L T hT (fun _ ↦ q) (fun _ ↦ Ψ) fun _ ↦ hΨ

end ZFVP
