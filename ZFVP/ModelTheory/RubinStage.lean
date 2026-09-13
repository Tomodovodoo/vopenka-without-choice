import ZFVP.ModelTheory.ConstantExpansion
import ZFVP.ModelTheory.OmittingTypes

/-! # The successor step of Rubin's construction (Enayat's Lemma A.2)

Enayat's Appendix builds a Rubin model as a union of an `ω₁`-chain of countable models. The step
that produces `M_{α+1}` from `M_α` is his Lemma A.2: given a countable model `M`, countably many
pairs of subsets of `M` that cannot be separated by a definable set, and countably many definable
directed sets with no last element, there is an elementary extension of `M` in which the pairs are
still inseparable and each directed set has an element above all of its old elements.

This file sets up that step and proves everything around the two inputs that are not available
here: the Henkin-Orey omitting types theorem (`OmittingTypesTheorem`, stated but unproved in
`ZFVP.ModelTheory.OmittingTypes`) and Enayat's Lemma A.5. Both appear as visible hypotheses of the
final theorem, the way `RubinShelahSchmerl` is carried in `ZFVP.ModelTheory.CountabilityEssential`.

Contents:

* `Inseparable N V W`, Enayat's inseparability, and `inseparable_compl_of_not_definable`, the fact
  he uses at every stage: a parametrically undefinable `S` and its complement are inseparable;
* `rubinTheory δ ρ`, the theory `T` of Lemma A.2 over the constants `M ⊕ ℕ`, and the two theorems
  saying what a model of it gives: an elementary map from `M`, and the upper bounds of clause (b);
* `separatingType`, Enayat's `Σ^ψ_n`, with the bridge `definable_iff_exists_semisentence` between
  parametrically definable subsets of a model and the sets defined by an `LSetC (M ⊕ ℕ)`-formula
  at a tuple, and `inseparable_of_omits`, which turns omission of every `Σ^ψ_n` into
  inseparability;
* `consistent_rubinTheory`, Enayat's "readily seen since finitely satisfiable in `M`", and
  `exists_normalModel`, which turns a model of `T` in Foundation's sense into a set structure
  with an assignment of the constants;
* `SeparatingTypesLocallyOmitted`, Enayat's Lemma A.5, stated as a named `Prop`;
* `exists_elementary_extension_inseparable_upper_bounds`, Lemma A.2 itself.

Two things are done differently from the paper, both recorded in the docstrings below: the theory
`T` also carries the equality axioms of its language (Foundation's semantics allows structures
that interpret `=` as a congruence, and Enayat works with normal models throughout), and a
directed set with no last element is described by the strict order alone, through
`DirectedNoLast`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v

/-! ## Inseparable pairs of subsets -/

section Inseparable

variable {N : Type v} [SetStructure N]

/-- Enayat's inseparability: `V` and `W` are inseparable in `N` if no subset of `N` that is
definable in `N` with parameters contains `V` and misses `W`. Enayat states it for disjoint `V`
and `W`; disjointness is a property of the pairs he carries along, not part of this definition,
and none of the arguments below need it. -/
def Inseparable (N : Type v) [SetStructure N] (V W : N → Prop) : Prop :=
  ¬∃ X : N → Prop, (ℒₛₑₜ-predicate[N] X) ∧ (∀ x, V x → X x) ∧ ∀ x, W x → ¬X x

/-- The form in which inseparability gets used: a definable set containing `V` meets `W`. -/
theorem Inseparable.meets {V W : N → Prop} (h : Inseparable N V W) (X : N → Prop)
    (hX : ℒₛₑₜ-predicate[N] X) (hVX : ∀ x, V x → X x) : ∃ x, W x ∧ X x := by
  by_contra hc
  exact h ⟨X, hX, hVX, fun x hW hX ↦ hc ⟨x, hW, hX⟩⟩

/-- Inseparability is not vacuous: a definable `V` is separated from anything disjoint from it. -/
theorem not_inseparable_of_definable {V W : N → Prop} (hV : ℒₛₑₜ-predicate[N] V)
    (hdisj : ∀ x, V x → W x → False) : ¬Inseparable N V W :=
  fun h ↦ h ⟨V, hV, fun _ hx ↦ hx, fun x hW hV ↦ hdisj x hV hW⟩

/-- The step Enayat uses at every stage of the construction: if `S` is not definable in `N` with
parameters then `S` and its complement are inseparable in `N`. A definable set containing `S` and
missing the complement of `S` would be `S` itself. -/
theorem inseparable_compl_of_not_definable (S : N → Prop) (hS : ¬(ℒₛₑₜ-predicate[N] S)) :
    Inseparable N S (fun x ↦ ¬S x) := by
  rintro ⟨X, hX, hSX, hcompl⟩
  refine hS ?_
  have hXS : ∀ x, X x ↔ S x := fun x ↦
    ⟨fun hx ↦ Classical.byContradiction fun h ↦ hcompl x h hx, hSX x⟩
  obtain ⟨φ, hφ⟩ := hX.definable
  exact ⟨φ, fun v ↦ (hφ v).trans (hXS (v 0))⟩

end Inseparable

/-! ## Equality in the language with constants

Foundation's structures interpret `=` by an arbitrary relation, so the equality axioms have to be
carried explicitly; they are part of the theory `T` below. -/

instance lSetCEq (C : Type u) : Language.Eq (LSetC C) := ⟨Sum.inl Language.Eq.eq⟩

instance lSetCMem (C : Type u) : Language.Mem (LSetC C) := ⟨Sum.inl Language.Mem.mem⟩

/-- A set structure with an assignment of the constants interprets `=` as equality, so it
satisfies the equality axioms of `LSetC C`. -/
theorem models_eqAxiom_setConstStructure {C : Type u} (N : Type v) [SetStructure N] [Nonempty N]
    (c : C → N) : (setConstStructure N c).toStruc ⊧* (𝗘𝗤 (LSetC C)) := by
  let _ : Structure (LSetC C) N := setConstStructure N c
  have : Structure.Eq (LSetC C) N := ⟨fun _ _ ↦ iff_of_eq rfl⟩
  exact Structure.Eq.models_eq (LSetC C) N

/-! ## The theory `T` of Lemma A.2 -/

section RubinTheory

variable (M : Type u) [SetStructure M] [Nonempty M]

/-- The elementary diagram of `M` written in the language that also has the constants `d_n`: the
sentences `φ(ṁ₁, …, ṁ_k)` for tuples satisfying `φ` in `M`. Only the constants `Sum.inl m` occur
in it. This is Enayat's `Th(M, m)_{m ∈ M}`. -/
def sumDiagram : Theory (LSetC (M ⊕ ℕ)) :=
  {σ | ∃ (ξ : Type) (n : ℕ) (φ : SetTheorySemiformula ξ n) (b : Fin n → M) (f : ξ → M),
    φ.Eval b f ∧ σ = diagramSentence φ (Sum.inl ∘ b) (Sum.inl ∘ f)}

variable {M}

omit [Nonempty M] in
theorem mem_sumDiagram {ξ : Type} {n : ℕ} (φ : SetTheorySemiformula ξ n) (b : Fin n → M)
    (f : ξ → M) (h : φ.Eval b f) : diagramSentence φ (Sum.inl ∘ b) (Sum.inl ∘ f) ∈ sumDiagram M :=
  ⟨ξ, n, φ, b, f, h, rfl⟩

/-- `M` models its own diagram under any assignment that names each `m` by itself. -/
theorem models_sumDiagram_self (c : M ⊕ ℕ → M) (hc : ∀ m, c (Sum.inl m) = m) :
    (setConstStructure M c).toStruc ⊧* sumDiagram M := by
  refine Semantics.modelsSet_iff.mpr ?_
  rintro σ ⟨ξ, n, φ, b, f, hφ, rfl⟩
  refine (eval_diagramSentence c φ (Sum.inl ∘ b) (Sum.inl ∘ f)).mpr ?_
  have hb : c ∘ (Sum.inl ∘ b) = b := by funext i; exact hc (b i)
  have hf : c ∘ (Sum.inl ∘ f) = f := by funext x; exact hc (f x)
  rw [hb, hf]
  exact hφ

variable {N : Type v} [SetStructure N] [Nonempty N]

omit [Nonempty M] in
/-- The variant of `elementaryMap_of_models_elementaryDiagram` for the diagram written over
`M ⊕ ℕ`: a model of `sumDiagram M` is an elementary extension of `M` along the map that reads off
the constants `Sum.inl m`. -/
theorem elementaryMap_of_models_sumDiagram (c : M ⊕ ℕ → N)
    (h : (setConstStructure N c).toStruc ⊧* sumDiagram M) :
    ∃ j : ElementaryMap M N, ∀ m, j m = c (Sum.inl m) := by
  have key : ∀ {ξ : Type} {n : ℕ} (φ : SetTheorySemiformula ξ n) (b : Fin n → M) (f : ξ → M),
      φ.Eval b f → φ.Eval (c ∘ Sum.inl ∘ b) (c ∘ Sum.inl ∘ f) := by
    intro ξ n φ b f hφ
    exact (eval_diagramSentence c φ (Sum.inl ∘ b) (Sum.inl ∘ f)).mp
      (Semantics.modelsSet_iff.mp h (mem_sumDiagram φ b f hφ))
  refine ⟨⟨fun m ↦ c (Sum.inl m), fun {ξ n} φ b f ↦ ⟨key φ b f, fun hN ↦ ?_⟩⟩, fun _ ↦ rfl⟩
  by_contra hM
  have hneg := key (∼φ) b f (by simpa using hM)
  simp only [LogicalConnective.HomClass.map_neg] at hneg
  exact hneg hN

/-! ### The definable directed sets

A definable directed set with no last element is given by the formula `δ n` defining it and the
formula `ρ n` defining its strict order, both with parameters from `M` in their free variables.
`DirectedNoLast` states, for the strict order alone, what Enayat's "directed set with no last
element" is used for: every pair of elements has a strict upper bound. -/

/-- The set defined by `δ n` in `M`, with the parameters read off the free variables. -/
def dset (δ : ℕ → SetTheorySemiformula M 1) (n : ℕ) (x : M) : Prop := (δ n).Eval ![x] id

/-- The strict order defined by `ρ n` in `M`. -/
def dlt (ρ : ℕ → SetTheorySemiformula M 2) (n : ℕ) (x y : M) : Prop := (ρ n).Eval ![x, y] id

/-- What "directed with no last element" gives for the strict order `lt` on `D`: `D` is nonempty,
`lt` is transitive on `D`, and any two elements of `D` have a strict upper bound in `D`. Taking
`x = y` in `upper` is the "no last element" half. -/
structure DirectedNoLast (D : M → Prop) (lt : M → M → Prop) : Prop where
  /-- The set is not empty. -/
  nonempty : ∃ x, D x
  /-- The strict order is transitive on the set. -/
  trans : ∀ x y z, D x → D y → D z → lt x y → lt y z → lt x z
  /-- Two elements have a common strict upper bound. -/
  upper : ∀ x y, D x → D y → ∃ z, D z ∧ lt x z ∧ lt y z

omit [SetStructure M] [Nonempty M] in
/-- A finite subset of a directed set with no last element has a strict upper bound in it. -/
theorem DirectedNoLast.exists_upper_bound {D : M → Prop} {lt : M → M → Prop}
    (h : DirectedNoLast D lt) (A : Finset M) (hA : ∀ m ∈ A, D m) :
    ∃ d, D d ∧ ∀ m ∈ A, lt m d := by
  classical
  induction A using Finset.induction with
  | empty => obtain ⟨x, hx⟩ := h.nonempty; exact ⟨x, hx, by simp⟩
  | insert a A _ ih =>
    obtain ⟨d, hd, hdA⟩ := ih fun m hm ↦ hA m (Finset.mem_insert_of_mem hm)
    have ha : D a := hA a (Finset.mem_insert_self a A)
    obtain ⟨z, hz, haz, hdz⟩ := h.upper a d ha hd
    refine ⟨z, hz, fun m hm ↦ ?_⟩
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact haz
    · exact h.trans m d z (hA m (Finset.mem_insert_of_mem hm)) hd hz (hdA m hm) hdz

/-! ### The theory -/

/-- The sentence `d_n ∈ D_n`. -/
def memberSentence (δ : ℕ → SetTheorySemiformula M 1) (n : ℕ) : Sentence (LSetC (M ⊕ ℕ)) :=
  diagramSentence (δ n) ![Sum.inr n] Sum.inl

/-- The sentence `ṁ <_{D_n} d_n`. -/
def boundSentence (ρ : ℕ → SetTheorySemiformula M 2) (n : ℕ) (m : M) :
    Sentence (LSetC (M ⊕ ℕ)) :=
  diagramSentence (ρ n) ![Sum.inl m, Sum.inr n] Sum.inl

/-- Enayat's theory `T` of Lemma A.2: the elementary diagram of `M`, the sentences `d_n ∈ D_n`,
and the sentences `ṁ <_{D_n} d_n` for the `m` that lie in `D_n` in `M`.

It also contains the equality axioms of `LSetC (M ⊕ ℕ)`. Enayat does not list them because he
works with normal models throughout; Foundation's structures interpret `=` by an arbitrary
relation, so a model of `T` is only normalizable if `T` says that `=` is a congruence. Adding them
changes nothing about consistency: they hold in `M`. -/
def rubinTheory (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2) :
    Theory (LSetC (M ⊕ ℕ)) :=
  sumDiagram M ∪ 𝗘𝗤 (LSetC (M ⊕ ℕ)) ∪ Set.range (memberSentence δ) ∪
    {σ | ∃ n m, dset δ n m ∧ σ = boundSentence ρ n m}

variable {δ : ℕ → SetTheorySemiformula M 1} {ρ : ℕ → SetTheorySemiformula M 2}

omit [Nonempty M] in
theorem sumDiagram_subset_rubinTheory : sumDiagram M ⊆ rubinTheory δ ρ :=
  fun _ hσ ↦ Or.inl (Or.inl (Or.inl hσ))

omit [Nonempty M] in
theorem memberSentence_mem_rubinTheory (n : ℕ) : memberSentence δ n ∈ rubinTheory δ ρ :=
  Or.inl (Or.inr ⟨n, rfl⟩)

omit [Nonempty M] in
theorem boundSentence_mem_rubinTheory {n : ℕ} {m : M} (h : dset δ n m) :
    boundSentence ρ n m ∈ rubinTheory δ ρ :=
  Or.inr ⟨n, m, h, rfl⟩

omit [Nonempty M] in
theorem eqAxiom_subset_rubinTheory : 𝗘𝗤 (LSetC (M ⊕ ℕ)) ⊆ rubinTheory δ ρ :=
  fun _ hσ ↦ Or.inl (Or.inl (Or.inr hσ))

variable {N : Type v} [SetStructure N] [Nonempty N]

omit [SetStructure M] [Nonempty M] [Nonempty N] in
theorem eval_memberSentence (c : M ⊕ ℕ → N) (n : ℕ) :
    Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim (memberSentence δ n)
      ↔ (δ n).Eval ![c (Sum.inr n)] (c ∘ Sum.inl) := by
  rw [memberSentence, eval_diagramSentence]
  have h : (c ∘ ![Sum.inr n]) = ![c (Sum.inr n)] := by
    funext i; exact Fin.cases rfl (fun j ↦ j.elim0) i
  rw [h]

omit [SetStructure M] [Nonempty M] [Nonempty N] in
theorem eval_boundSentence (c : M ⊕ ℕ → N) (n : ℕ) (m : M) :
    Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim (boundSentence ρ n m)
      ↔ (ρ n).Eval ![c (Sum.inl m), c (Sum.inr n)] (c ∘ Sum.inl) := by
  rw [boundSentence, eval_diagramSentence]
  have h : (c ∘ ![Sum.inl m, Sum.inr n]) = ![c (Sum.inl m), c (Sum.inr n)] := by
    funext i; exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j) i
  rw [h]

omit [Nonempty M] in
/-- Clause of Lemma A.2 that comes for free: a model of `T` is an elementary extension of `M`
along the map reading off the constants `ṁ`. -/
theorem elementaryMap_of_models_rubinTheory (c : M ⊕ ℕ → N)
    (h : (setConstStructure N c).toStruc ⊧* rubinTheory δ ρ) :
    ∃ j : ElementaryMap M N, ∀ m, j m = c (Sum.inl m) :=
  elementaryMap_of_models_sumDiagram c
    (Semantics.modelsSet_iff.mpr fun {_} hσ ↦
      Semantics.modelsSet_iff.mp h (sumDiagram_subset_rubinTheory hσ))

omit [Nonempty M] in
/-- Clause (b) of Lemma A.2: in a model of `T` the element named by `d_n` lies in `D_n` and is
strictly above every element of `D_n` that comes from `M`. -/
theorem upperBound_of_models_rubinTheory (c : M ⊕ ℕ → N)
    (h : (setConstStructure N c).toStruc ⊧* rubinTheory δ ρ) (n : ℕ) :
    (δ n).Eval ![c (Sum.inr n)] (c ∘ Sum.inl) ∧
      ∀ m : M, dset δ n m → (ρ n).Eval ![c (Sum.inl m), c (Sum.inr n)] (c ∘ Sum.inl) := by
  refine ⟨(eval_memberSentence c n).mp
      (Semantics.modelsSet_iff.mp h (memberSentence_mem_rubinTheory n)), fun m hm ↦ ?_⟩
  exact (eval_boundSentence c n m).mp
    (Semantics.modelsSet_iff.mp h (boundSentence_mem_rubinTheory hm))

end RubinTheory

/-! ## Definable subsets and formulas of the language with constants

The two notions of "definable subset of `N`" that Lemma A.2 has to compare are
`ℒₛₑₜ-predicate[N] X`, a subset defined by an `ℒₛₑₜ`-formula with parameters from `N`, and the
subsets `{y | ψ(y, a⃗)}` cut out by an `LSetC C`-formula at a tuple `a⃗` from `N`. They are the
same, and both directions are proved here: `definable_of_semisentence` replaces the constants by
their values, read as parameters, and `exists_semisentence_of_definable` turns the finitely many
parameters of a formula into extra bound variables. -/

section Definability

variable {C : Type u} {N : Type v} [SetStructure N]

/-- The constants of `LSetC C` are removed from a term by replacing each of them with the free
variable named by its value. `ℒₛₑₜ` has no function symbols, so nothing else can happen. -/
def elimTerm (c : C → N) : ∀ {m : ℕ}, Semiterm (LSetC C) Empty m → Semiterm ℒₛₑₜ N m
  | _, Semiterm.bvar x => Semiterm.bvar x
  | _, Semiterm.fvar x => x.elim
  | _, Semiterm.func (arity := k) f _ =>
    match k, f with
    | _, Sum.inl f' => Empty.elim f'
    | _, Sum.inr (Language.Constant.Func.const a) => Semiterm.fvar (c a)

/-- The same for formulas: the relation symbols of `LSetC C` are those of `ℒₛₑₜ`. -/
def elimFormula (c : C → N) :
    ∀ {m : ℕ}, Semiformula (LSetC C) Empty m → Semiformula ℒₛₑₜ N m
  | _, Semiformula.verum => ⊤
  | _, Semiformula.falsum => ⊥
  | _, Semiformula.rel r v =>
    match r with
    | Sum.inl r' => Semiformula.rel r' fun i ↦ elimTerm c (v i)
    | Sum.inr r' => PEmpty.elim r'
  | _, Semiformula.nrel r v =>
    match r with
    | Sum.inl r' => Semiformula.nrel r' fun i ↦ elimTerm c (v i)
    | Sum.inr r' => PEmpty.elim r'
  | _, Semiformula.and φ ψ => elimFormula c φ ⋏ elimFormula c ψ
  | _, Semiformula.or φ ψ => elimFormula c φ ⋎ elimFormula c ψ
  | _, Semiformula.all φ => ∀¹ elimFormula c φ
  | _, Semiformula.exs φ => ∃¹ elimFormula c φ

theorem val_elimTerm (c : C → N) {m : ℕ} (b : Fin m → N) (t : Semiterm (LSetC C) Empty m) :
    Semiterm.val (s := SetTheory.standardStructure N) b id (elimTerm c t)
      = Semiterm.val (s := setConstStructure N c) b Empty.elim t := by
  match t with
  | Semiterm.bvar x => rfl
  | Semiterm.fvar x => exact x.elim
  | Semiterm.func (arity := k) f v =>
    match k, f with
    | _, Sum.inl f' => exact f'.elim
    | _, Sum.inr (Language.Constant.Func.const a) => rfl

theorem eval_elimFormula (c : C → N) :
    ∀ {m : ℕ} (b : Fin m → N) (φ : Semiformula (LSetC C) Empty m),
      Semiformula.Eval (s := SetTheory.standardStructure N) b id (elimFormula c φ)
        ↔ Semiformula.Eval (s := setConstStructure N c) b Empty.elim φ := by
  intro m b φ
  induction φ using Semiformula.rec' with
  | hverum => simp [elimFormula]
  | hfalsum => simp [elimFormula]
  | hrel r v =>
    rcases r with r' | r'
    · have hv : (fun i ↦ Semiterm.val (s := SetTheory.standardStructure N) b id (elimTerm c (v i)))
          = fun i ↦ Semiterm.val (s := setConstStructure N c) b Empty.elim (v i) :=
        funext fun i ↦ val_elimTerm c b (v i)
      simp only [elimFormula, Semiformula.eval_rel, Function.comp_def, hv]
      rfl
    · exact r'.elim
  | hnrel r v =>
    rcases r with r' | r'
    · have hv : (fun i ↦ Semiterm.val (s := SetTheory.standardStructure N) b id (elimTerm c (v i)))
          = fun i ↦ Semiterm.val (s := setConstStructure N c) b Empty.elim (v i) :=
        funext fun i ↦ val_elimTerm c b (v i)
      simp only [elimFormula, Semiformula.eval_nrel, Function.comp_def, hv]
      rfl
    · exact r'.elim
  | hand φ ψ ihφ ihψ => simp [elimFormula, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [elimFormula, ihφ, ihψ]
  | hall φ ih => simp [elimFormula, ih]
  | hexs φ ih => simp [elimFormula, ih]

/-- One direction of the correspondence: the subset of `N` cut out by an `LSetC C`-formula at a
tuple from `N` is definable in `N` with parameters. -/
theorem definable_of_semisentence (c : C → N) {q : ℕ} (ψ : Semisentence (LSetC C) (q + 1))
    (a : Fin q → N) :
    ℒₛₑₜ-predicate[N]
      (fun y ↦ Semiformula.Eval (s := setConstStructure N c) (y :> a) Empty.elim ψ) := by
  refine ⟨elimFormula c ψ ⇜ (Semiterm.bvar 0 :> fun i ↦ Semiterm.fvar (a i)), fun v ↦ ?_⟩
  rw [Semiformula.eval_substs]
  have hv : (Semiterm.val (s := SetTheory.standardStructure N) v id ∘
      (Semiterm.bvar 0 :> fun i ↦ Semiterm.fvar (a i))) = (v 0 :> a) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [hv]
  exact eval_elimFormula c (v 0 :> a) ψ

/-- The other direction: a subset of `N` definable with parameters is cut out by an
`LSetC C`-formula at a tuple from `N`. The parameters that actually occur in the defining formula
are finitely many, and they become the extra bound variables of the formula. -/
theorem exists_semisentence_of_definable (c : C → N) (X : N → Prop)
    (hX : ℒₛₑₜ-predicate[N] X) :
    ∃ (q : ℕ) (ψ : Semisentence (LSetC C) (q + 1)) (a : Fin q → N),
      ∀ y, X y ↔ Semiformula.Eval (s := setConstStructure N c) (y :> a) Empty.elim ψ := by
  classical
  obtain ⟨φ, hφ⟩ := hX.definable
  let s : Finset N := φ.freeVariables
  let q : ℕ := s.card
  let a : Fin q → N := fun i ↦ (s.equivFin.symm i : N)
  let w : N → Semiterm ℒₛₑₜ Empty (q + 1) := fun x ↦
    if h : x ∈ s then Semiterm.bvar (s.equivFin ⟨x, h⟩).succ else Semiterm.bvar 0
  let ω : Rew ℒₛₑₜ N 1 Empty (q + 1) := Rew.bind (fun _ ↦ Semiterm.bvar 0) w
  refine ⟨q, Semiformula.lMap (Language.Hom.add₁ ℒₛₑₜ (Language.constant C)) (ω ▹ φ), a, fun y ↦ ?_⟩
  rw [Semiformula.eval_lMap]
  rw [show Structure.lMap (Language.Hom.add₁ ℒₛₑₜ (Language.constant C)) (setConstStructure N c)
      = SetTheory.standardStructure N from lMap_add₁_setConstStructure N c]
  rw [Semiformula.eval_rew]
  have hfe : Function.funEqOn φ.FVar? (id : N → N)
      (fun x ↦ Semiterm.val (s := SetTheory.standardStructure N) (y :> a) Empty.elim
        (ω (Semiterm.fvar x))) := by
    intro x hx
    have hxs : x ∈ s := hx
    show x = Semiterm.val (y :> a) Empty.elim (w x)
    have hwx : w x = Semiterm.bvar (s.equivFin ⟨x, hxs⟩).succ := dite_eq_left_of_eq_true (eq_true hxs)
    rw [hwx]
    show x = (y :> a) (s.equivFin ⟨x, hxs⟩).succ
    rw [Matrix.cons_val_succ]
    show x = ((s.equivFin.symm (s.equivFin ⟨x, hxs⟩) : s) : N)
    rw [Equiv.symm_apply_apply]
  exact ((hφ (fun _ ↦ y)).symm).trans (Semiformula.eval_iff_of_funEqOn φ hfe)

/-- The two notions of definable subset agree. -/
theorem definable_iff_exists_semisentence (c : C → N) (X : N → Prop) :
    (ℒₛₑₜ-predicate[N] X) ↔
      ∃ (q : ℕ) (ψ : Semisentence (LSetC C) (q + 1)) (a : Fin q → N),
        ∀ y, X y ↔ Semiformula.Eval (s := setConstStructure N c) (y :> a) Empty.elim ψ := by
  refine ⟨exists_semisentence_of_definable c X, ?_⟩
  rintro ⟨q, ψ, a, hψ⟩
  obtain ⟨χ, hχ⟩ := definable_of_semisentence c ψ a
  exact ⟨χ, fun v ↦ (hχ v).trans (hψ (v 0)).symm⟩

end Definability

/-! ## The types `Σ^ψ_n` -/

section SeparatingType

variable {C : Type u} {N : Type v} [SetStructure N]

/-- `ψ(ȧ, x⃗)`: the first variable of `ψ` is filled with the constant naming `a`, the rest are
left free. -/
def substConst {q : ℕ} (ψ : Semisentence (LSetC C) (q + 1)) (a : C) : Semisentence (LSetC C) q :=
  ψ ⇜ (constTerm a :> fun i ↦ Semiterm.bvar i)

theorem eval_substConst (c : C → N) {q : ℕ} (ψ : Semisentence (LSetC C) (q + 1)) (a : C)
    (x : Fin q → N) :
    Semiformula.Eval (s := setConstStructure N c) x Empty.elim (substConst ψ a)
      ↔ Semiformula.Eval (s := setConstStructure N c) (c a :> x) Empty.elim ψ := by
  rw [substConst, Semiformula.eval_substs]
  have h : (Semiterm.val (s := setConstStructure N c) x Empty.elim ∘
      (constTerm a :> fun i ↦ Semiterm.bvar i)) = (c a :> x) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [h]

/-- `Omits` for the structure that an assignment of the constants puts on `N`. -/
def OmitsWith (N : Type v) [SetStructure N] (c : C → N) {q : ℕ} (Ψ : PartialType (LSetC C) q) :
    Prop :=
  @Omits (LSetC C) N (setConstStructure N c) q Ψ

variable {M : Type u} [SetStructure M]

/-- Enayat's `Σ^ψ_n(x⃗)`: the formulas `ψ(ȧ, x⃗)` for `a ∈ V` together with the formulas
`¬ψ(ḃ, x⃗)` for `b ∈ W`. A tuple realizes it exactly when `ψ(·, x⃗)` separates `V` from `W`, which
is what `realizes_separatingType_iff` says. Enayat writes `Σ^ψ_n` for the pair `{V_n, W_n}`; the
index `n` only picks the pair out of the list, so it is not an argument here. -/
def separatingType {q : ℕ} (V W : M → Prop) (ψ : Semisentence (LSetC (M ⊕ ℕ)) (q + 1)) :
    PartialType (LSetC (M ⊕ ℕ)) q :=
  {σ | ∃ a, V a ∧ σ = substConst ψ (Sum.inl a)} ∪
    {σ | ∃ b, W b ∧ σ = ∼substConst ψ (Sum.inl b)}

omit [SetStructure M] in
/-- The type says what Enayat says it says: a tuple `x⃗` satisfies every formula of `Σ^ψ` exactly
when `ψ(·, x⃗)` holds of every name of an element of `V` and of no name of an element of `W`. -/
theorem realizes_separatingType_iff (c : M ⊕ ℕ → N) {q : ℕ} (V W : M → Prop)
    (ψ : Semisentence (LSetC (M ⊕ ℕ)) (q + 1)) (x : Fin q → N) :
    (∀ σ ∈ separatingType V W ψ,
        Semiformula.Eval (s := setConstStructure N c) x Empty.elim σ) ↔
      (∀ a, V a →
          Semiformula.Eval (s := setConstStructure N c) (c (Sum.inl a) :> x) Empty.elim ψ) ∧
        ∀ b, W b →
          ¬Semiformula.Eval (s := setConstStructure N c) (c (Sum.inl b) :> x) Empty.elim ψ := by
  constructor
  · intro h
    refine ⟨fun a ha ↦ (eval_substConst c ψ (Sum.inl a) x).mp (h _ (Or.inl ⟨a, ha, rfl⟩)), ?_⟩
    intro b hb hcon
    have := h _ (Or.inr ⟨b, hb, rfl⟩)
    simp only [LogicalConnective.HomClass.map_neg] at this
    exact this ((eval_substConst c ψ (Sum.inl b) x).mpr hcon)
  · rintro ⟨hV, hW⟩ σ (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact (eval_substConst c ψ (Sum.inl a) x).mpr (hV a ha)
    · simp only [LogicalConnective.HomClass.map_neg]
      exact fun hcon ↦ hW b hb ((eval_substConst c ψ (Sum.inl b) x).mp hcon)

omit [SetStructure M] in
/-- The payoff of the omitting types argument, Enayat's clause (a). If a model of the diagram
omits `Σ^ψ` for every `ψ`, then the images of `V` and `W` are inseparable in it.

Both directions of `definable_iff_exists_semisentence` are what makes this work: a definable
subset of `N` separating the two images would be given by some `ψ` at some tuple, and that tuple
would realize `Σ^ψ`. -/
theorem inseparable_of_omits (c : M ⊕ ℕ → N) (V W : M → Prop)
    (hom : ∀ (q : ℕ) (ψ : Semisentence (LSetC (M ⊕ ℕ)) (q + 1)),
      OmitsWith N c (separatingType V W ψ)) :
    Inseparable N (fun y ↦ ∃ a, V a ∧ y = c (Sum.inl a))
      (fun y ↦ ∃ b, W b ∧ y = c (Sum.inl b)) := by
  rintro ⟨X, hX, hVX, hWX⟩
  obtain ⟨q, ψ, x, hψ⟩ := exists_semisentence_of_definable c X hX
  obtain ⟨σ, hσ, hne⟩ := hom q ψ x
  refine hne ?_
  refine (realizes_separatingType_iff c V W ψ x).mpr ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩ σ hσ
  · exact (hψ (c (Sum.inl a))).mp (hVX _ ⟨a, ha, rfl⟩)
  · exact fun hcon ↦ hWX _ ⟨b, hb, rfl⟩ ((hψ (c (Sum.inl b))).mpr hcon)

end SeparatingType

/-! ## `T` is consistent

Enayat's "readily seen since it is finitely satisfiable in `M`". A finite part of `T` mentions
finitely many of the sentences `ṁ <_{D_n} d_n`, so each `d_n` can be interpreted in `M` by a
strict upper bound of the finitely many `m` that the finite part mentions. -/

section Consistency

variable {M : Type u} [SetStructure M] [Nonempty M] {δ : ℕ → SetTheorySemiformula M 1}
  {ρ : ℕ → SetTheorySemiformula M 2}

theorem consistent_rubinTheory (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) :
    Entailment.Consistent (rubinTheory δ ρ) := by
  classical
  refine Theory.consistent_of_satisfiable (compact.mpr ?_)
  intro u hu
  set P : Sentence (LSetC (M ⊕ ℕ)) → Prop :=
    fun σ ↦ ∃ p : ℕ × M, dset δ p.1 p.2 ∧ σ = boundSentence ρ p.1 p.2 with hP
  set dec : Sentence (LSetC (M ⊕ ℕ)) → ℕ × M :=
    fun σ ↦ if h : P σ then h.choose else (0, Classical.arbitrary M) with hdec
  have hdecSpec : ∀ σ, P σ →
      dset δ (dec σ).1 (dec σ).2 ∧ σ = boundSentence ρ (dec σ).1 (dec σ).2 := by
    intro σ h
    rw [hdec]
    simp only [h, ↓reduceDIte]
    exact h.choose_spec
  set pairs : Finset (ℕ × M) := (u.filter P).image dec with hpairs
  set A : ℕ → Finset M :=
    fun n ↦ (pairs.filter (fun p ↦ p.1 = n ∧ dset δ n p.2)).image Prod.snd with hAdef
  have hA : ∀ n, ∀ m ∈ A n, dset δ n m := by
    intro n m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_filter.mp hp).2.2
  choose d hd using fun n ↦ (hdir n).exists_upper_bound (A n) (hA n)
  set c : M ⊕ ℕ → M := Sum.elim id d with hc
  have hcl : ∀ m : M, c (Sum.inl m) = m := fun _ ↦ rfl
  have hcomp : (c ∘ Sum.inl) = (id : M → M) := funext hcl
  refine ⟨(setConstStructure M c).toStruc, Semantics.modelsSet_iff.mpr ?_⟩
  intro σ hσu
  have hσ : σ ∈ rubinTheory δ ρ := hu hσu
  rcases hσ with ((hσ | hσ) | ⟨n, rfl⟩) | hσ
  · exact Semantics.modelsSet_iff.mp (models_sumDiagram_self c hcl) hσ
  · exact Semantics.modelsSet_iff.mp (models_eqAxiom_setConstStructure M c) hσ
  · refine (eval_memberSentence c n).mpr ?_
    rw [hcomp]
    exact (hd n).1
  · have hPσ : P σ := by
      obtain ⟨n, m, h1, h2⟩ := hσ
      exact ⟨(n, m), h1, h2⟩
    obtain ⟨hdset, hform⟩ := hdecSpec σ hPσ
    have hmem : (dec σ).2 ∈ A (dec σ).1 := by
      refine Finset.mem_image.mpr ⟨dec σ, Finset.mem_filter.mpr ⟨?_, rfl, hdset⟩, rfl⟩
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hσu, hPσ⟩, rfl⟩
    rw [hform]
    refine (eval_boundSentence c (dec σ).1 (dec σ).2).mpr ?_
    rw [hcomp]
    exact (hd (dec σ).1).2 _ hmem

end Consistency

/-! ## From an arbitrary model to a set structure

The omitting types theorem produces a structure for `LSetC C` in Foundation's sense, where `=` is
interpreted by a congruence rather than by equality. Quotienting by that congruence gives a set
structure together with an assignment of the constants, and both modelling `T` and omitting the
types survive the quotient. -/

section Normalization

/-- A model of `T` that omits every `Ψ i`, presented as a set structure with an assignment of the
constants. -/
structure NormalModel (C : Type u) (T : Theory (LSetC C)) {ι : Type} {qi : ι → ℕ}
    (Ψ : (i : ι) → PartialType (LSetC C) (qi i)) where
  /-- The underlying type. -/
  Dom : Type u
  [setStructure : SetStructure Dom]
  [nonempty : Nonempty Dom]
  [countable : Countable Dom]
  /-- The interpretation of the constants. -/
  assign : C → Dom
  /-- It models `T`. -/
  models : (setConstStructure Dom assign).toStruc ⊧* T
  /-- It omits every type of the family. -/
  omits : ∀ i, OmitsWith Dom assign (Ψ i)

attribute [instance] NormalModel.setStructure NormalModel.nonempty NormalModel.countable

theorem exists_normalModel {C : Type u} (T : Theory (LSetC C)) (hEQ : 𝗘𝗤 (LSetC C) ⊆ T)
    {ι : Type} {qi : ι → ℕ} (Ψ : (i : ι) → PartialType (LSetC C) (qi i))
    (D : Type u) [sD : Structure (LSetC C) D] [Nonempty D] [Countable D]
    (hT : D↓[LSetC C] ⊧* T) (hΨ : ∀ i, Omits D (Ψ i)) : Nonempty (NormalModel C T Ψ) := by
  have hEQD : D↓[LSetC C] ⊧* 𝗘𝗤 (LSetC C) :=
    Semantics.modelsSet_iff.mpr fun {_} h ↦ Semantics.modelsSet_iff.mp hT (hEQ h)
  let _ : SetStructure (Structure.Eq.QuotEq (LSetC C) D) :=
    ⟨fun y x ↦ Structure.rel (L := LSetC C) (Sum.inl Language.Set.Rel.mem) ![x, y]⟩
  let _ : Countable (Structure.Eq.QuotEq (LSetC C) D) :=
    inferInstanceAs (Countable (Quotient (Structure.Eq.eqvSetoid (LSetC C) D)))
  set c : C → Structure.Eq.QuotEq (LSetC C) D :=
    fun a ↦ Structure.func (L := LSetC C) (Sum.inr (Language.Constant.Func.const a)) ![] with hc
  -- the reduct to the language of set theory is the standard structure of the membership defined
  -- from the relation symbol
  have hstd : SetTheory.standardStructure (Structure.Eq.QuotEq (LSetC C) D)
      = Structure.lMap (Language.Hom.add₁ ℒₛₑₜ (Language.constant C))
          (Structure.Eq.QuotEq.struc (L := LSetC C) (M := D)) := by
    refine (Structure.ext ?_ ?_).symm
    · funext k f v
      exact f.elim
    · funext k r v
      match k, r with
      | _, Language.Set.Rel.eq =>
        show Structure.rel (L := LSetC C) (Sum.inl Language.Set.Rel.eq) v = (v 0 = v 1)
        exact propext (Structure.eq_iff_eq (L := LSetC C)
          (M := Structure.Eq.QuotEq (LSetC C) D) (v := v))
      | _, Language.Set.Rel.mem =>
        show Structure.rel (L := LSetC C) (Sum.inl Language.Set.Rel.mem) v
          = Structure.rel (L := LSetC C) (Sum.inl Language.Set.Rel.mem) ![v 0, v 1]
        rw [← Matrix.fun_eq_vec_two]
  have hsame : setConstStructure (Structure.Eq.QuotEq (LSetC C) D) c
      = Structure.Eq.QuotEq.struc (L := LSetC C) (M := D) := by
    refine Structure.ext ?_ ?_
    · funext k f v
      match k, f with
      | _, Sum.inl f' => exact f'.elim
      | _, Sum.inr (Language.Constant.Func.const a) =>
        have hv : v = ![] := funext fun i ↦ i.elim0
        rw [hv]
        rfl
    · funext k r v
      match k, r with
      | _, Sum.inl r' =>
        show (SetTheory.standardStructure _).rel r' v = _
        rw [hstd]
        rfl
      | _, Sum.inr r' => exact r'.elim
  refine ⟨{ Dom := Structure.Eq.QuotEq (LSetC C) D
            assign := c
            models := ?_
            omits := ?_ }⟩
  · rw [hsame]
    exact Semantics.modelsSet_iff.mpr fun {σ} hσ ↦
      (Structure.Eq.QuotEq.models_iff (L := LSetC C) (M := D) (σ := σ)).mpr
        (Semantics.modelsSet_iff.mp hT hσ)
  · intro i
    show @Omits (LSetC C) _ (setConstStructure _ c) _ (Ψ i)
    rw [hsame]
    intro a
    obtain ⟨r, hr⟩ : ∃ r : Fin (qi i) → D, (fun k ↦ (⟦r k⟧ : Structure.Eq.QuotEq (LSetC C) D)) = a :=
      ⟨fun k ↦ (a k).out, funext fun k ↦ Quotient.out_eq _⟩
    obtain ⟨ψ, hψ, hne⟩ := hΨ i r
    refine ⟨ψ, hψ, fun hcon ↦ hne ?_⟩
    have hemp : (fun x ↦ (⟦Empty.elim x⟧ : Structure.Eq.QuotEq (LSetC C) D)) = Empty.elim :=
      funext fun x ↦ x.elim
    have h1 := Structure.Eq.QuotEq.eval_mk (L := LSetC C) (M := D) (φ := ψ) (bv := r)
      (fv := (Empty.elim : Empty → D))
    rw [hr, hemp] at h1
    exact h1.mp hcon

end Normalization

/-! ## Enayat's Lemma A.5 -/

/-- Enayat's Lemma A.5: for a countable `M`, `M`-inseparable pairs `{V n, W n}` and `M`-definable
directed sets `D n` with no last element, the theory `T` of Lemma A.2 locally omits every type
`Σ^ψ_n`.

This development does not prove it, so everything using it carries it as a hypothesis. Enayat's
proof goes through his Lemmas A.3 and A.4, which translate provability from `T`, and consistency
with `T`, of a sentence `φ(d_{k₁}, …, d_{k_p})` into statements about `M` with `p` alternating
quantifier blocks: `∃ r_i ∈ D_{k_i} ∀ s_i ∈ D_{k_i}` for provability (A.3) and
`∀ r_i ∈ D_{k_i} ∃ s_i ∈ D_{k_i}` for consistency (A.4), each guarded by `⋀ᵢ r_i <_{D_{k_i}} s_i`.
A formula `θ` isolating `Σ^ψ_n` over `T` is then turned into two `M`-formulas `λ` and `γ` with
`V n ⊆ Λ` and `W n ⊆ Γ`; directedness gives `Λ ∩ Γ = ∅`, since a common element would make
`ψ(m, x⃗)` and its negation both follow, and no last element rules that out. So `Λ` would separate
the pair. What is missing here is the `p`-fold alternation of A.3 and A.4 as a syntactic
construction on formulas, together with the induction on `p` that proves them. -/
def SeparatingTypesLocallyOmitted : Prop :=
  ∀ (M : Type u) [SetStructure M] [Nonempty M] [Countable M]
      (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
      (V W : ℕ → M → Prop),
    (∀ n, Inseparable M (V n) (W n)) → (∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) →
      ∀ (n q : ℕ) (ψ : Semisentence (LSetC (M ⊕ ℕ)) (q + 1)),
        LocallyOmits (rubinTheory δ ρ) (separatingType (V n) (W n) ψ)

/-! ## Lemma A.2 -/

/-- What Lemma A.2 produces: a countable elementary extension of `M` in which every pair
`{V n, W n}` is still inseparable and every `D n` has an element above all of its old elements. -/
structure InseparableUpperBoundExtension (M : Type u) [SetStructure M] [Nonempty M]
    (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (V W : ℕ → M → Prop) where
  /-- The larger model. -/
  Model : Type u
  [setStructure : SetStructure Model]
  [nonempty : Nonempty Model]
  [countable : Countable Model]
  /-- `M` maps elementarily into it. -/
  embedding : ElementaryMap M Model
  /-- Clause (a): the pairs stay inseparable. -/
  inseparable : ∀ n, Inseparable Model (fun y ↦ ∃ a, V n a ∧ y = embedding a)
    (fun y ↦ ∃ b, W n b ∧ y = embedding b)
  /-- Clause (b): each `D n` gets an element strictly above all of `D n` as computed in `M`. -/
  upperBound : ∀ n, ∃ d : Model, (δ n).Eval ![d] (fun m ↦ embedding m) ∧
    ∀ m : M, dset δ n m → (ρ n).Eval ![embedding m, d] (fun m ↦ embedding m)

attribute [instance] InseparableUpperBoundExtension.setStructure
  InseparableUpperBoundExtension.nonempty InseparableUpperBoundExtension.countable

/-- Enayat's Lemma A.2. Both unproved inputs are hypotheses: the Henkin-Orey omitting types
theorem (`homit`) and Enayat's Lemma A.5 (`hA5`). -/
theorem exists_elementary_extension_inseparable_upper_bounds (homit : OmittingTypesTheorem.{u})
    (hA5 : SeparatingTypesLocallyOmitted.{u}) (M : Type u) [SetStructure M] [Nonempty M]
    [Countable M] (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (V W : ℕ → M → Prop) (hins : ∀ n, Inseparable M (V n) (W n))
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) :
    Nonempty (InseparableUpperBoundExtension M δ ρ V W) := by
  classical
  let _ : Encodable M := Encodable.ofCountable M
  have : Nonempty (ℕ × ((q : ℕ) × Semisentence (LSetC (M ⊕ ℕ)) (q + 1))) := ⟨(0, ⟨0, ⊤⟩)⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ × ((q : ℕ) × Semisentence (LSetC (M ⊕ ℕ)) (q + 1)))
  obtain ⟨Om⟩ := homit (LSetC (M ⊕ ℕ)) (rubinTheory δ ρ) (consistent_rubinTheory hdir)
    (fun k ↦ (e k).2.1) (fun k ↦ separatingType (V (e k).1) (W (e k).1) (e k).2.2)
    fun k ↦ hA5 M δ ρ V W hins hdir (e k).1 (e k).2.1 (e k).2.2
  obtain ⟨NM⟩ := exists_normalModel (rubinTheory δ ρ) eqAxiom_subset_rubinTheory
    (fun k ↦ separatingType (V (e k).1) (W (e k).1) (e k).2.2) Om.Dom Om.models Om.omits
  obtain ⟨j, hj⟩ := elementaryMap_of_models_rubinTheory NM.assign NM.models
  have hjc : (fun m ↦ j m) = NM.assign ∘ Sum.inl := funext hj
  refine ⟨{ Model := NM.Dom
            embedding := j
            inseparable := ?_
            upperBound := ?_ }⟩
  · intro n
    have hom : ∀ (q : ℕ) (ψ : Semisentence (LSetC (M ⊕ ℕ)) (q + 1)),
        OmitsWith NM.Dom NM.assign (separatingType (V n) (W n) ψ) := by
      intro q ψ
      obtain ⟨k, hk⟩ := he (n, ⟨q, ψ⟩)
      have hk' := NM.omits k
      rw [hk] at hk'
      exact hk'
    have := inseparable_of_omits NM.assign (V n) (W n) hom
    simpa only [hj] using this
  · intro n
    obtain ⟨hmem, hbound⟩ := upperBound_of_models_rubinTheory NM.assign NM.models n
    refine ⟨NM.assign (Sum.inr n), ?_, fun m hm ↦ ?_⟩
    · rw [hjc]; exact hmem
    · rw [hjc, hj m]; exact hbound m hm

end ZFVP
