import ZFVP.ModelTheory.OmittingTypes

/-! # The omitting types statement, as stated, is false

`ZFVP.OmittingTypesTheorem` quantifies over every language `L` and every consistent theory `T`,
with no equality symbol and no equality axioms anywhere in sight. Foundation's `Structure L M`
interprets the relation symbols of `L` freely, and `Semiformula` has no built-in equality, so a
structure is free to interpret a unary function symbol by a map that misses a point. That is
enough to break the theorem: over the empty theory in an equality-free language there is a type
which is locally omitted and yet realized in every nonempty structure.

The counterexample, in a language with one unary function symbol `f` and unary predicates
`P i` for `i : ℕ`:

* `Ψ = {ψ i | i : ℕ}` with `ψ i = P i x → ∃y P i (f y)`, a set of formulas in one free variable;
* every nonempty structure realizes `Ψ` at the point `f a` for any `a`, since a witness for
  `∃y P i (f y)` is already at hand, namely `y = a`;
* the empty theory locally omits `Ψ`: given `θ` with `∃x θ` consistent, take a model `M` and a
  point `a` with `θ(a)`, pick an index `i` larger than every predicate index occurring in `θ`,
  and duplicate `a` into a new point `a*` outside the range of `f`, interpreting `P i` as
  `{a*}` and every other predicate by pulling back along the collapse `a* ↦ a`. In the new
  structure `θ(a*) ⋏ ∼ψ i (a*)` holds, so `∃x (θ ⋏ ∼ψ i)` is consistent.

The transfer step is `ZFVP.OTC.eval_transfer`: a surjective strong homomorphism preserves and
reflects the truth of every formula whose predicate indices it respects.

The refutation is at universe level 0, `ZFVP.not_omittingTypesTheorem : ¬OmittingTypesTheorem.{0}`,
which is the level the counterexample language lives at (`Rel 1 := ℕ`).
-/

namespace ZFVP.OTC

open LO LO.FirstOrder LO.Entailment

-- `dupStructure` is data supplied by a point and an index, so it is a plain definition rather
-- than an instance.
set_option warn.classDefReducibility false

/-! ### The language -/

/-- Function symbols of the counterexample language: one unary symbol, nothing else. -/
abbrev F₀ : ℕ → Type
  | 1 => Unit
  | _ => Empty

/-- Relation symbols of the counterexample language: one unary symbol `P i` for each `i : ℕ`,
nothing else. -/
abbrev R₀ : ℕ → Type
  | 1 => ℕ
  | _ => Empty

/-- The counterexample language: a unary function symbol `f` and unary predicates `P i`. -/
def L₀ : Language.{0} := ⟨F₀, R₀⟩

@[simp] theorem L₀_func (k : ℕ) : L₀.Func k = F₀ k := rfl

@[simp] theorem L₀_rel (k : ℕ) : L₀.Rel k = R₀ k := rfl

instance (k : ℕ) : Encodable (L₀.Func k) := by
  match k with
  | 0 => exact inferInstanceAs (Encodable Empty)
  | 1 => exact inferInstanceAs (Encodable Unit)
  | (_ + 2) => exact inferInstanceAs (Encodable Empty)

instance (k : ℕ) : Encodable (L₀.Rel k) := by
  match k with
  | 0 => exact inferInstanceAs (Encodable Empty)
  | 1 => exact inferInstanceAs (Encodable ℕ)
  | (_ + 2) => exact inferInstanceAs (Encodable Empty)

instance : L₀.Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- The unary function symbol. -/
def fSym : L₀.Func 1 := ()

/-- The unary predicate symbol with index `i`. -/
def pSym (i : ℕ) : L₀.Rel 1 := i

/-- `fTm t` is the term `f t`. -/
def fTm {ξ : Type*} {n : ℕ} (t : Semiterm L₀ ξ n) : Semiterm L₀ ξ n :=
  Semiterm.func fSym ![t]

/-- `pFml i t` is the atomic formula `P i t`. -/
def pFml {ξ : Type*} {n : ℕ} (i : ℕ) (t : Semiterm L₀ ξ n) : Semiformula L₀ ξ n :=
  Semiformula.rel (pSym i) ![t]

/-- `ψ i` is the formula `P i x₀ → ∃y P i (f y)` in one free variable. -/
def ψ (i : ℕ) : Semisentence L₀ 1 :=
  ∼(pFml i #0) ⋎ (∃¹ (pFml i (fTm #0)))

/-- The type `Ψ = {ψ i | i : ℕ}`. -/
def Ψ : PartialType L₀ 1 := Set.range ψ

/-! ### Counting predicate indices -/

/-- A bound on the index of a relation symbol: `relBound 1 i = i + 1`, and there is nothing to
bound at any other arity. -/
def relBound : (k : ℕ) → L₀.Rel k → ℕ
  | 0, r => Empty.elim r
  | 1, r => (show ℕ from r) + 1
  | (_ + 2), r => Empty.elim r

@[simp] theorem relBound_one (i : ℕ) : relBound 1 (pSym i) = i + 1 := rfl

/-- `predSup φ` is strictly above every predicate index occurring in `φ`. -/
def predSup {ξ : Type*} : {n : ℕ} → Semiformula L₀ ξ n → ℕ
  | _, Semiformula.verum => 0
  | _, Semiformula.falsum => 0
  | _, Semiformula.rel (arity := k) r _ => relBound k r
  | _, Semiformula.nrel (arity := k) r _ => relBound k r
  | _, Semiformula.and φ ψ => max (predSup φ) (predSup ψ)
  | _, Semiformula.or φ ψ => max (predSup φ) (predSup ψ)
  | _, Semiformula.all φ => predSup φ
  | _, Semiformula.exs φ => predSup φ

variable {ξ : Type*} {n : ℕ}

@[simp] theorem predSup_verum : predSup (⊤ : Semiformula L₀ ξ n) = 0 := rfl

@[simp] theorem predSup_falsum : predSup (⊥ : Semiformula L₀ ξ n) = 0 := rfl

@[simp] theorem predSup_rel {k : ℕ} (r : L₀.Rel k) (v : Fin k → Semiterm L₀ ξ n) :
    predSup (Semiformula.rel r v) = relBound k r := rfl

@[simp] theorem predSup_nrel {k : ℕ} (r : L₀.Rel k) (v : Fin k → Semiterm L₀ ξ n) :
    predSup (Semiformula.nrel r v) = relBound k r := rfl

@[simp] theorem predSup_and (φ χ : Semiformula L₀ ξ n) :
    predSup (φ ⋏ χ) = max (predSup φ) (predSup χ) := rfl

@[simp] theorem predSup_or (φ χ : Semiformula L₀ ξ n) :
    predSup (φ ⋎ χ) = max (predSup φ) (predSup χ) := rfl

@[simp] theorem predSup_all (φ : Semiformula L₀ ξ (n + 1)) : predSup (∀¹ φ) = predSup φ := rfl

@[simp] theorem predSup_exs (φ : Semiformula L₀ ξ (n + 1)) : predSup (∃¹ φ) = predSup φ := rfl

/-! ### Vector helpers -/

theorem comp_vec1 {α β : Type*} (g : α → β) (x : α) : g ∘ ![x] = ![g x] := by
  funext j
  have : j = 0 := Subsingleton.elim _ _
  subst this
  rfl

theorem vec1_eq {α : Type*} (v : Fin 1 → α) : v = ![v 0] := by
  funext j
  have : j = 0 := Subsingleton.elim _ _
  subst this
  rfl

theorem comp_vec1' {α β : Type*} (g : α → β) (v : Fin 1 → α) : g ∘ v = ![g (v 0)] := by
  funext j
  have : j = 0 := Subsingleton.elim _ _
  subst this
  rfl

theorem comp_cons {α β : Type*} (g : α → β) (x : α) {m : ℕ} (e : Fin m → α) :
    g ∘ (x :> e) = (g x :> g ∘ e) := by
  funext j
  refine Fin.cases ?_ ?_ j <;> simp

/-! ### Transfer along a surjective strong homomorphism -/

section Transfer

variable {M' M : Type*} [Structure L₀ M'] [Structure L₀ M] (h : M' → M)

/-- Values of terms commute with a map that commutes with the function symbols. -/
theorem val_transfer
    (hfunc : ∀ {k : ℕ} (F : L₀.Func k) (v : Fin k → M'),
      h (Structure.func F v) = Structure.func F (h ∘ v))
    (e : Fin n → M') (ε : ξ → M') (t : Semiterm L₀ ξ n) :
    h (Semiterm.val e ε t) = Semiterm.val (h ∘ e) (h ∘ ε) t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func F v ih =>
    simp only [Semiterm.val_func, hfunc]
    congr 1
    funext j
    simpa using ih j

/-- A surjective map commuting with the function symbols and with all relation symbols of index
below `i` preserves and reflects the truth of every formula whose predicate indices stay below
`i`. -/
theorem eval_transfer (hsurj : Function.Surjective h)
    (hfunc : ∀ {k : ℕ} (F : L₀.Func k) (v : Fin k → M'),
      h (Structure.func F v) = Structure.func F (h ∘ v))
    (i : ℕ)
    (hrel : ∀ {k : ℕ} (r : L₀.Rel k) (v : Fin k → M'), relBound k r ≤ i →
      (Structure.rel r v ↔ Structure.rel r (h ∘ v)))
    (ε : ξ → M') {n : ℕ} (φ : Semiformula L₀ ξ n) :
    predSup φ ≤ i → ∀ e : Fin n → M',
      (Semiformula.Eval e ε φ ↔ Semiformula.Eval (h ∘ e) (h ∘ ε) φ) := by
  induction φ using Semiformula.rec' with
  | hverum => intro _ e; simp
  | hfalsum => intro _ e; simp
  | hrel r v =>
    intro hb e
    have hv : h ∘ (fun j ↦ Semiterm.val e ε (v j))
        = fun j ↦ Semiterm.val (h ∘ e) (h ∘ ε) (v j) := by
      funext j; exact val_transfer h hfunc e ε (v j)
    simp only [Semiformula.eval_rel, Function.comp_def]
    rw [hrel r (fun j ↦ Semiterm.val e ε (v j)) (by simpa using hb)]
    rw [show (h ∘ fun j ↦ Semiterm.val e ε (v j))
        = fun j ↦ Semiterm.val (h ∘ e) (h ∘ ε) (v j) from hv]
    rfl
  | hnrel r v =>
    intro hb e
    have hv : h ∘ (fun j ↦ Semiterm.val e ε (v j))
        = fun j ↦ Semiterm.val (h ∘ e) (h ∘ ε) (v j) := by
      funext j; exact val_transfer h hfunc e ε (v j)
    simp only [Semiformula.eval_nrel, Function.comp_def]
    rw [hrel r (fun j ↦ Semiterm.val e ε (v j)) (by simpa using hb)]
    rw [show (h ∘ fun j ↦ Semiterm.val e ε (v j))
        = fun j ↦ Semiterm.val (h ∘ e) (h ∘ ε) (v j) from hv]
    rfl
  | hand φ χ ihφ ihχ =>
    intro hb e
    simp only [predSup_and, max_le_iff] at hb
    simp [ihφ hb.1 e, ihχ hb.2 e]
  | hor φ χ ihφ ihχ =>
    intro hb e
    simp only [predSup_or, max_le_iff] at hb
    simp [ihφ hb.1 e, ihχ hb.2 e]
  | hall φ ih =>
    intro hb e
    simp only [predSup_all] at hb
    simp only [Semiformula.eval_all]
    constructor
    · intro H y
      obtain ⟨x, rfl⟩ := hsurj y
      have hx := (ih hb (x :> e)).mp (H x)
      rwa [comp_cons] at hx
    · intro H x
      refine (ih hb (x :> e)).mpr ?_
      rw [comp_cons]
      exact H (h x)
  | hexs φ ih =>
    intro hb e
    simp only [predSup_exs] at hb
    simp only [Semiformula.eval_ex]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨h x, ?_⟩
      have hx' := (ih hb (x :> e)).mp hx
      rwa [comp_cons] at hx'
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hsurj y
      refine ⟨x, (ih hb (x :> e)).mpr ?_⟩
      rw [comp_cons]
      exact hy

end Transfer

/-! ### Evaluating the formulas of `Ψ` -/

section Eval

variable {M : Type*} [Structure L₀ M]

@[simp] theorem val_fTm (e : Fin n → M) (ε : ξ → M) (t : Semiterm L₀ ξ n) :
    Semiterm.val e ε (fTm t) = Structure.func fSym ![Semiterm.val e ε t] := by
  simp only [fTm, Semiterm.val_func, comp_vec1]

@[simp] theorem eval_pFml (i : ℕ) (t : Semiterm L₀ ξ n) (e : Fin n → M) (ε : ξ → M) :
    Semiformula.Eval e ε (pFml i t) ↔ Structure.rel (pSym i) ![Semiterm.val e ε t] := by
  simp only [pFml, Semiformula.eval_rel, comp_vec1]

theorem eval_ψ (i : ℕ) (c : M) :
    Semiformula.Evalb ![c] (ψ i) ↔
      (¬Structure.rel (pSym i) ![c] ∨
        ∃ x : M, Structure.rel (pSym i) ![Structure.func fSym ![x]]) := by
  simp [ψ]

end Eval

/-! ### Every nonempty structure realizes `Ψ` -/

/-- No nonempty structure omits `Ψ`: the point `f a` satisfies every `ψ i`. -/
theorem not_omits (M : Type*) [Nonempty M] [Structure L₀ M] : ¬Omits M Ψ := by
  intro hom
  obtain ⟨a⟩ := ‹Nonempty M›
  obtain ⟨χ, hχ, hne⟩ := hom ![(Structure.func fSym ![a] : M)]
  obtain ⟨i, rfl⟩ := hχ
  refine hne ((eval_ψ i _).mpr ?_)
  by_cases hP : Structure.rel (M := M) (pSym i) ![Structure.func fSym ![a]]
  · exact Or.inr ⟨a, hP⟩
  · exact Or.inl hP

/-! ### The empty theory is consistent -/

instance modelsSet_empty (N : Type*) [Nonempty N] [Structure L₀ N] :
    N↓[L₀] ⊧* (∅ : Theory L₀) := ⟨fun φ hφ ↦ absurd hφ (by simp)⟩

theorem consistent_empty : Consistent (∅ : Theory L₀) := consistent_of_model _ Unit

/-! ### Duplicating a point outside the range of `f` -/

section Duplicate

variable {M : Type*}

/-- `collapse a` sends the new point `none` to `a` and `some x` to `x`. -/
def collapse (a : M) : Option M → M := fun o ↦ o.getD a

@[simp] theorem collapse_none (a : M) : collapse a none = a := rfl

@[simp] theorem collapse_some (a x : M) : collapse a (some x) = x := rfl

theorem collapse_surjective (a : M) : Function.Surjective (collapse a) := fun x ↦ ⟨some x, rfl⟩

variable [Structure L₀ M]

/-- The interpretation of the function symbol on `Option M`: collapse, apply, then tag with
`some`, so that `none` is outside the range. -/
def dupFunc (a : M) : (k : ℕ) → L₀.Func k → (Fin k → Option M) → Option M
  | 0, F, _ => Empty.elim F
  | 1, F, v => some (Structure.func F ![collapse a (v 0)])
  | (_ + 2), F, _ => Empty.elim F

/-- The interpretation of the predicates on `Option M`: `P i` holds of `none` alone, every other
predicate is pulled back along the collapse. -/
def dupRel (a : M) (i : ℕ) : (k : ℕ) → L₀.Rel k → (Fin k → Option M) → Prop
  | 0, r, _ => Empty.elim r
  | 1, r, v => if (show ℕ from r) = i then v 0 = none else Structure.rel r ![collapse a (v 0)]
  | (_ + 2), r, _ => Empty.elim r

/-- `M` with the point `a` duplicated: the copy `none` is outside the range of `f` and is the
only point where `P i` holds. -/
def dupStructure (a : M) (i : ℕ) : Structure L₀ (Option M) where
  func := fun {k} F v ↦ dupFunc a k F v
  rel := fun {k} r v ↦ dupRel a i k r v

@[simp] theorem func_dup (a : M) (i : ℕ) (F : L₀.Func 1) (v : Fin 1 → Option M) :
    @Structure.func L₀ (Option M) (dupStructure a i) 1 F v
      = some (Structure.func F ![collapse a (v 0)]) := rfl

@[simp] theorem rel_dup (a : M) (i : ℕ) (r : L₀.Rel 1) (v : Fin 1 → Option M) :
    @Structure.rel L₀ (Option M) (dupStructure a i) 1 r v
      ↔ if (show ℕ from r) = i then v 0 = none else Structure.rel r ![collapse a (v 0)] :=
  Iff.rfl

/-- The collapse commutes with the function symbols. -/
theorem collapse_func (a : M) (i : ℕ) {k : ℕ} (F : L₀.Func k) (v : Fin k → Option M) :
    collapse a (@Structure.func L₀ (Option M) (dupStructure a i) k F v)
      = Structure.func F (collapse a ∘ v) := by
  match k, F, v with
  | 0, F, _ => exact Empty.elim F
  | 1, F, v => rw [func_dup, comp_vec1']; rfl
  | (_ + 2), F, _ => exact Empty.elim F

/-- The collapse preserves and reflects every predicate other than `P i`. -/
theorem collapse_rel (a : M) (i : ℕ) {k : ℕ} (r : L₀.Rel k) (v : Fin k → Option M)
    (hle : relBound k r ≤ i) :
    @Structure.rel L₀ (Option M) (dupStructure a i) k r v
      ↔ Structure.rel r (collapse a ∘ v) := by
  match k, r, v, hle with
  | 0, r, _, _ => exact Empty.elim r
  | 1, r, v, hle =>
    have hlt : (show ℕ from r) + 1 ≤ i := hle
    have hne : (show ℕ from r) ≠ i := by omega
    rw [rel_dup, comp_vec1']
    simp [hne]
  | (_ + 2), r, _, _ => exact Empty.elim r

/-- `P i` holds of the duplicate point. -/
theorem rel_dup_none (a : M) (i : ℕ) :
    @Structure.rel L₀ (Option M) (dupStructure a i) 1 (pSym i) ![none] := by
  show dupRel a i 1 (pSym i) ![none]
  simp [dupRel, pSym]

/-- `P i` holds nowhere in the range of `f`. -/
theorem not_rel_dup_range (a : M) (i : ℕ) (x : Option M) :
    ¬@Structure.rel L₀ (Option M) (dupStructure a i) 1 (pSym i)
      ![@Structure.func L₀ (Option M) (dupStructure a i) 1 fSym ![x]] := by
  show ¬dupRel a i 1 (pSym i) ![dupFunc a 1 fSym ![x]]
  simp [dupRel, dupFunc, pSym]

end Duplicate

/-! ### The empty theory locally omits `Ψ` -/

/-- The empty theory locally omits `Ψ`. Given `θ` with `∃x θ` consistent, take a model `M` and a
point `a` satisfying `θ`, pick a predicate index `i` above all those occurring in `θ`, and
duplicate `a`. In the duplicate `θ` still holds at the copy, while `P i` holds there and nowhere
in the range of `f`, so `ψ i` fails. -/
theorem locallyOmits_empty : LocallyOmits (∅ : Theory L₀) Ψ := by
  intro θ hθ
  obtain ⟨M, _, sM, hM⟩ :=
    LO.FirstOrder.satisfiable_iff.mp (Theory.small_satisfiable_of_consistent hθ)
  have hex : M↓[L₀] ⊧ (∃¹* θ : Sentence L₀) := hM.models_set (Set.mem_insert _ _)
  have hsome : ∃ b : Fin 1 → M, θ.Evalb b := by simpa [models_iff] using hex
  obtain ⟨b, hb⟩ := hsome
  set a : M := b 0 with ha
  set i : ℕ := predSup θ with hi
  let sOpt : Structure L₀ (Option M) := dupStructure a i
  refine ⟨ψ i, ⟨i, rfl⟩, ?_⟩
  have htr := eval_transfer (M' := Option M) (collapse a) (collapse_surjective a)
    (fun {k} F v ↦ collapse_func a i F v) i
    (fun {k} r v hle ↦ collapse_rel a i r v hle) (Empty.elim : Empty → Option M) θ hi.ge ![none]
  have hθnone : Semiformula.Evalb (M := Option M) ![none] θ := by
    refine htr.mpr ?_
    have h1 : collapse a ∘ ![(none : Option M)] = ![a] := comp_vec1 _ _
    have h2 : collapse a ∘ (Empty.elim : Empty → Option M) = Empty.elim :=
      funext fun j ↦ j.elim
    rw [h1, h2, ← vec1_eq b]
    exact hb
  have hψnone : ¬Semiformula.Evalb (M := Option M) ![none] (ψ i) := by
    rw [eval_ψ]
    rintro (hnp | ⟨x, hx⟩)
    · exact hnp (rel_dup_none a i)
    · exact not_rel_dup_range a i x hx
  refine consistent_insert_of_model (Option M) ?_
  have hwit : ∃ c : Fin 1 → Option M, (θ ⋏ ∼ψ i).Evalb c :=
    ⟨![none], by simp [hθnone, hψnone]⟩
  simpa [models_iff] using hwit

end ZFVP.OTC

namespace ZFVP

open LO LO.FirstOrder LO.Entailment

/-- The omitting types statement as formulated in `ZFVP.OmittingTypes` is false. It quantifies
over all languages with no equality symbol and over theories with no equality axioms, and for
such a language a type can be locally omitted and still realized in every structure. -/
theorem not_omittingTypesTheorem : ¬OmittingTypesTheorem.{0} := by
  intro H
  obtain ⟨N⟩ := H OTC.L₀ (∅ : Theory OTC.L₀) OTC.consistent_empty (fun _ ↦ 1)
    (fun _ ↦ OTC.Ψ) (fun _ ↦ OTC.locallyOmits_empty)
  exact OTC.not_omits N.Dom (N.omits 0)

end ZFVP
