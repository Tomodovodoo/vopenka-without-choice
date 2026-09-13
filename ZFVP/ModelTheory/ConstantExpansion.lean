import ZFVP.SetTheory.ElementaryMap

/-! # The language of set theory with constants, and elementary diagrams

Enayat's Lemma A.2 builds an elementary extension of a model `M` by forming the theory

  `Th(M, m)_{m ∈ M} + (extra sentences about new constants)`

and reading a model of it as an elementary extension of `M`. This file supplies the language,
the structures and the diagram that make that reading available, so that a model of the diagram
really is an `ElementaryMap` in the sense of `ZFVP.ElementaryMap`.

Contents:

* `LSetC C`, the language of set theory with one constant symbol for each `a : C`;
* `constStructure` and `setConstStructure`, the structures given by an assignment `c : C → N`,
  with the reduct along `Language.Hom.add₁` being the set structure on `N`;
* `Language.Encodable (LSetC C)` for encodable `C`, which is what the omitting types statement
  in `ZFVP.ModelTheory.OmittingTypes` asks for;
* `diagramSentence`, the sentence saying that a set-theoretic formula holds of a named tuple;
* `elementaryDiagram M` and its consistency;
* `elementaryMap_of_models_elementaryDiagram`, the reason for the file: a model of the diagram
  is an elementary extension of `M` along the map interpreting the constants.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

-- The two structures below are data supplied by an assignment of the constants, so they are
-- plain definitions rather than instances.
set_option warn.classDefReducibility false

universe u v

/-- The language of set theory expanded by one constant symbol for every element of `C`. -/
abbrev LSetC (C : Type u) : Language.{u} := Language.add ℒₛₑₜ (Language.constant C)

/-! ### Structures for the constants -/

/-- The structure for `Language.constant C` on `N` that sends the constant symbol named `a`
to `c a`. -/
def constStructure {C : Type u} {N : Type v} (c : C → N) : Structure (Language.constant C) N where
  func := fun _ f _ =>
    match f with
    | Language.Constant.Func.const a => c a
  rel := fun _ r _ => PEmpty.elim r

/-- A set structure on `N` together with an assignment `c : C → N` of the constant names makes
`N` a structure for `LSetC C`. -/
def setConstStructure {C : Type u} (N : Type v) [SetStructure N] (c : C → N) :
    Structure (LSetC C) N :=
  @Structure.add ℒₛₑₜ (Language.constant C) N (SetTheory.standardStructure N) (constStructure c)

/-- The reduct of `setConstStructure N c` along the inclusion of `ℒₛₑₜ` is the set structure
on `N`. -/
theorem lMap_add₁_setConstStructure {C : Type u} (N : Type v) [SetStructure N] (c : C → N) :
    Structure.lMap (M := N) (Language.Hom.add₁ ℒₛₑₜ (Language.constant C)) (setConstStructure N c)
      = SetTheory.standardStructure N := rfl

/-! ### Encodability -/

instance constantFunc_encodable {C : Type u} [Encodable C] (k : ℕ) :
    Encodable (Language.Constant.Func C k) where
  encode := fun f =>
    match f with
    | Language.Constant.Func.const a => Encodable.encode a
  decode := fun e =>
    match k with
    | 0 => (Encodable.decode e).map Language.Constant.Func.const
    | _ + 1 => none
  encodek := by rintro ⟨a⟩; simp

instance constantLanguageFunc_encodable {C : Type u} [Encodable C] (k : ℕ) :
    Encodable ((Language.constant C).Func k) :=
  inferInstanceAs (Encodable (Language.Constant.Func C k))

instance constantLanguageRel_isEmpty {C : Type u} (k : ℕ) :
    IsEmpty ((Language.constant C).Rel k) :=
  inferInstanceAs (IsEmpty PEmpty.{u + 1})

instance constantLanguageRel_encodable {C : Type u} (k : ℕ) :
    Encodable ((Language.constant C).Rel k) :=
  @IsEmpty.toEncodable _ (constantLanguageRel_isEmpty k)

instance lSetCFunc_encodable {C : Type u} [Encodable C] (k : ℕ) :
    Encodable ((LSetC C).Func k) :=
  inferInstanceAs (Encodable (Language.Func ℒₛₑₜ k ⊕ (Language.constant C).Func k))

instance lSetCRel_encodable {C : Type u} [Encodable C] (k : ℕ) :
    Encodable ((LSetC C).Rel k) :=
  inferInstanceAs (Encodable (Language.Rel ℒₛₑₜ k ⊕ (Language.constant C).Rel k))

instance lSetC_encodable {C : Type u} [Encodable C] : (LSetC C).Encodable :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-! ### Naming elements by constants -/

/-- The closed term naming `a : C`. -/
def constTerm {C : Type u} (a : C) {ξ : Type*} {n : ℕ} : Semiterm (LSetC C) ξ n :=
  Semiterm.func (arity := 0)
    (show (LSetC C).Func 0 from Sum.inr (Language.Constant.Func.const a)) ![]

@[simp] theorem val_constTerm {C : Type u} {N : Type v} [SetStructure N] (c : C → N) (a : C)
    {ξ : Type*} {n : ℕ} (b : Fin n → N) (f : ξ → N) :
    Semiterm.val (s := setConstStructure N c) b f (constTerm a) = c a := rfl

/-- The `LSetC C`-sentence saying that `φ` holds of the tuple named by `b` and `f`. -/
def diagramSentence {C : Type u} {ξ : Type*} {n : ℕ} (φ : SetTheorySemiformula ξ n)
    (b : Fin n → C) (f : ξ → C) : Sentence (LSetC C) :=
  (Rew.bind (L := LSetC C) (ξ₁ := ξ) (n₁ := n) (ξ₂ := Empty) (n₂ := 0)
      (fun i ↦ constTerm (b i)) (fun x ↦ constTerm (f x))) ▹
    Semiformula.lMap (Language.Hom.add₁ ℒₛₑₜ (Language.constant C)) φ

/-- `diagramSentence φ b f` holds in `(N, c)` exactly when `φ` holds in `N` of the values the
constants take. -/
theorem eval_diagramSentence {C : Type u} {N : Type v} [SetStructure N] (c : C → N)
    {ξ : Type*} {n : ℕ} (φ : SetTheorySemiformula ξ n) (b : Fin n → C) (f : ξ → C) :
    Semiformula.Eval (s := setConstStructure N c) ![] Empty.elim (diagramSentence φ b f)
      ↔ φ.Eval (c ∘ b) (c ∘ f) := by
  rw [diagramSentence, Semiformula.eval_rew, Semiformula.eval_lMap]
  rfl

/-! ### The elementary diagram -/

variable (M : Type u) [SetStructure M] [Nonempty M]

/-- The elementary diagram of `M`: all `LSetC M`-sentences true in `M` when the constant named
`m` is interpreted as `m` itself. -/
def elementaryDiagram : Theory (LSetC M) :=
  {σ | (setConstStructure M (id : M → M)).toStruc ⊧ σ}

theorem mem_elementaryDiagram_iff {σ : Sentence (LSetC M)} :
    σ ∈ elementaryDiagram M ↔ (setConstStructure M (id : M → M)).toStruc ⊧ σ := Iff.rfl

/-- `M` with every constant interpreted as itself models its own elementary diagram. -/
theorem models_elementaryDiagram :
    (setConstStructure M (id : M → M)).toStruc ⊧* elementaryDiagram M :=
  Semantics.modelsSet_iff.mpr fun _ h ↦ h

/-- The elementary diagram of a nonempty set structure is consistent. -/
theorem consistent_elementaryDiagram :
    Entailment.Consistent (elementaryDiagram M) :=
  Theory.consistent_of_satisfiable
    ⟨(setConstStructure M (id : M → M)).toStruc, models_elementaryDiagram M⟩

variable {M}

/-- A set-theoretic formula holds of a tuple in `M` exactly when the sentence naming that tuple
belongs to the elementary diagram. -/
theorem diagramSentence_mem_elementaryDiagram_iff {ξ : Type*} {n : ℕ}
    (φ : SetTheorySemiformula ξ n) (b : Fin n → M) (f : ξ → M) :
    diagramSentence φ b f ∈ elementaryDiagram M ↔ φ.Eval b f := by
  rw [mem_elementaryDiagram_iff]
  exact eval_diagramSentence (id : M → M) φ b f

/-! ### A model of the diagram is an elementary extension -/

variable {N : Type u} [SetStructure N] [Nonempty N]

/-- The point of this file: if `N`, with the constant named `m` interpreted as `c m`, models the
elementary diagram of `M`, then `c` is an elementary map from `M` to `N`. -/
theorem elementaryMap_of_models_elementaryDiagram (c : M → N)
    (h : (setConstStructure N c).toStruc ⊧* elementaryDiagram M) :
    ∃ j : ElementaryMap M N, ∀ m, j m = c m := by
  have key : ∀ {ξ : Type} {n : ℕ} (φ : SetTheorySemiformula ξ n) (b : Fin n → M) (f : ξ → M),
      φ.Eval b f → φ.Eval (c ∘ b) (c ∘ f) := by
    intro ξ n φ b f hφ
    have hmem : diagramSentence φ b f ∈ elementaryDiagram M :=
      (diagramSentence_mem_elementaryDiagram_iff φ b f).mpr hφ
    exact (eval_diagramSentence c φ b f).mp (Semantics.modelsSet_iff.mp h hmem)
  refine ⟨⟨c, fun {ξ n} φ b f ↦ ⟨key φ b f, fun hN ↦ ?_⟩⟩, fun _ ↦ rfl⟩
  by_contra hM
  have hneg := key (∼φ) b f (by simpa using hM)
  simp only [LogicalConnective.HomClass.map_neg] at hneg
  exact hneg hN

/-- Set-theoretic sentences transfer along an elementary map. -/
theorem models_sentence_iff_of_elementaryMap (j : ElementaryMap M N)
    (σ : SetTheorySentence) : M↓[ℒₛₑₜ] ⊧ σ ↔ N↓[ℒₛₑₜ] ⊧ σ := by
  have h := j.elementary σ (![] : Fin 0 → M) (Empty.elim : Empty → M)
  have hb : (j.toFun ∘ (![] : Fin 0 → M)) = (![] : Fin 0 → N) := by
    funext i; exact i.elim0
  have hf : (j.toFun ∘ (Empty.elim : Empty → M)) = (Empty.elim : Empty → N) := by
    funext i; exact i.elim
  rw [hb, hf] at h
  exact h

/-- A set theory holds in `N` as soon as it holds in `M` and there is an elementary map from `M`
to `N`. -/
theorem models_theory_of_elementaryMap (j : ElementaryMap M N) (T : SetTheory)
    (hM : M↓[ℒₛₑₜ] ⊧* T) : N↓[ℒₛₑₜ] ⊧* T :=
  Semantics.modelsSet_iff.mpr fun σ hσ ↦
    (models_sentence_iff_of_elementaryMap j σ).mp (Semantics.modelsSet_iff.mp hM hσ)

/-- A model of the elementary diagram of a model of `ZF` is a model of `ZF`. -/
theorem models_zf_of_models_elementaryDiagram [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (c : M → N)
    (h : (setConstStructure N c).toStruc ⊧* elementaryDiagram M) :
    N↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  obtain ⟨j, -⟩ := elementaryMap_of_models_elementaryDiagram c h
  exact models_theory_of_elementaryMap j 𝗭𝗙 inferInstance

end ZFVP
