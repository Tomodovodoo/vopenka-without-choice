import ZFVP.ModelTheory.HenkinSet
import ZFVP.ModelTheory.StageSatisfaction

/-! # Extending a finite Henkin stage by the denial of a member of a locally omitted type

This file supplies the omitting step of the Henkin construction in `ZFVP.ModelTheory.HenkinSet`:
the hypothesis `hchoose` of `ZFVP.exists_henkinSet`. Given a finite stage `Δ` consistent over `T`
and an injective tuple `a` of free variables, local omission of `Ψ` produces a `ψ ∈ Ψ` such that
`∼ψ(a⃗)` may be added to `Δ` while keeping it consistent over `T`.

The bridge is `stageType Δ a : Semisentence L q`, the formula in `q` free variables saying of a
tuple `x⃗` that some assignment of the remaining free variables makes every member of `Δ` true
while placing `x_i` at the free variable `a i`. Its semantics is `evalb_stageType`, and
injectivity of `a` is what makes the right-to-left direction of that biconditional work.

The construction of `stageType Δ a` is a single simultaneous substitution followed by a block of
existential quantifiers. Fix `N := stageTypeBound Δ a`, a bound above the free variables of every
member of `Δ` and above every `a i`, and at least `1`. Rewrite `⋀Δ` into
`Semiformula L Empty (q + N)` by sending the free variable `a i` to the bound variable `#(i + N)`
and every other free variable `v` to `#v` when that is in range, then quantify the first `N`
bound variables with `∃¹^[N]`. Foundation's `Semiformula.eval_exsItr` puts the quantified block
at the low indices and the `q` remaining slots at the high indices, which is exactly the layout
above.

Free variables `v` that are not below `N` are sent to `#0` by the substitution. They are not free
in any member of `Δ`, so this junk value never matters; it is why `stageTypeBound` is arranged to be
positive, so that `#0` typechecks even when `q = 0` and `Δ` has no free variables.
-/

namespace ZFVP

open LO LO.FirstOrder LO.Entailment

universe u v

variable {L : Language.{u}}

/-! ### The bound on the variables of a stage -/

/-- A positive number above the free variables of every member of `Δ` and above every `a i`. -/
def stageTypeBound (Δ : List (Proposition L)) {q : ℕ} (a : Fin q → ℕ) : ℕ :=
  Sequent.newVar Δ + (Finset.univ.sup a) + 1

theorem lt_stageTypeBound_of_apply (Δ : List (Proposition L)) {q : ℕ} (a : Fin q → ℕ) (i : Fin q) :
    a i < stageTypeBound Δ a := by
  have : a i ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ i)
  simp only [stageTypeBound]; omega

theorem stageTypeBound_pos (Δ : List (Proposition L)) {q : ℕ} (a : Fin q → ℕ) :
    0 < stageTypeBound Δ a := by simp [stageTypeBound]

theorem fvSup_le_stageTypeBound {Δ : List (Proposition L)} {φ : Proposition L} (h : φ ∈ Δ)
    {q : ℕ} (a : Fin q → ℕ) : φ.fvSup ≤ stageTypeBound Δ a := by
  have : φ.fvSup ≤ Sequent.newVar Δ := by
    simp only [Sequent.newVar]
    exact List.le_max_of_le (List.mem_map_of_mem h) (le_refl _)
  simp only [stageTypeBound]; omega

/-! ### The substitution -/

open Classical in
/-- The simultaneous substitution used to build `stageType Δ a`: the free variable `a i` goes to
the bound variable at index `i + stageTypeBound Δ a`, every other free variable `v` goes to the bound
variable at index `v` when that is in range, and everything else goes to `#0`. -/
noncomputable def stageSubst (Δ : List (Proposition L)) {q : ℕ} (a : Fin q → ℕ) :
    ℕ → Semiterm L Empty (q + stageTypeBound Δ a) := fun v =>
  if h : ∃ i, a i = v then #(h.choose.addNat (stageTypeBound Δ a))
  else if hv : v < q + stageTypeBound Δ a then #⟨v, hv⟩
  else #⟨0, by have := stageTypeBound_pos Δ a; omega⟩

theorem stageSubst_apply (Δ : List (Proposition L)) {q : ℕ} {a : Fin q → ℕ}
    (ha : Function.Injective a) (i : Fin q) :
    stageSubst Δ a (a i) = #(i.addNat (stageTypeBound Δ a)) := by
  classical
  have h : ∃ j, a j = a i := ⟨i, rfl⟩
  simp only [stageSubst, h, ↓reduceDIte]
  rw [ha h.choose_spec]

theorem stageSubst_of_not_mem_range (Δ : List (Proposition L)) {q : ℕ} {a : Fin q → ℕ} {v : ℕ}
    (hr : ¬∃ i, a i = v) (hv : v < stageTypeBound Δ a) :
    stageSubst Δ a v = #⟨v, by omega⟩ := by
  classical
  simp only [stageSubst, hr, ↓reduceDIte, show v < q + stageTypeBound Δ a by omega]

/-! ### The formula -/

/-- `stageType Δ a` says of a `q`-tuple `x⃗` that some assignment of the free variables makes every
member of `Δ` true and puts `x_i` at the free variable `a i`. -/
noncomputable def stageType (Δ : List (Proposition L)) {q : ℕ} (a : Fin q → ℕ) :
    Semisentence L q :=
  ∃¹^[stageTypeBound Δ a] (Rew.bind ![] (stageSubst Δ a) ▹ (⋀Δ : Proposition L))

/-- The assignment of the free variables that a tuple of bound variables induces through
`stageSubst`. -/
private noncomputable def stageAssign {M : Type v} [Structure L M] (Δ : List (Proposition L))
    {q : ℕ} (a : Fin q → ℕ) (w : Fin (q + stageTypeBound Δ a) → M) : ℕ → M :=
  fun v => Semiterm.val w (Empty.elim : Empty → M) (stageSubst Δ a v)

private lemma eval_conj_list {M : Type v} [Structure L M] (ε : ℕ → M)
    (Δ : List (Proposition L)) :
    Semiformula.Eval ![] ε (⋀Δ : Proposition L) ↔ ∀ φ ∈ Δ, Semiformula.Eval ![] ε φ :=
  List.map_conj₂_prop (f := Semiformula.Evalf (L := L) ε)

/-- The semantics of `stageType Δ a`. Injectivity of `a` is used for the direction that turns an
assignment of the free variables into a tuple of bound variables. -/
theorem evalb_stageType {M : Type v} [Nonempty M] [Structure L M]
    (Δ : List (Proposition L)) {q : ℕ} {a : Fin q → ℕ} (ha : Function.Injective a)
    (b : Fin q → M) :
    Semiformula.Evalb b (stageType Δ a) ↔
      ∃ ε : ℕ → M, (∀ i, ε (a i) = b i) ∧ ∀ φ ∈ Δ, Semiformula.Eval ![] ε φ := by
  classical
  have hstep : ∀ w : Fin (q + stageTypeBound Δ a) → M,
      Semiformula.Eval w (Empty.elim : Empty → M)
          (Rew.bind ![] (stageSubst Δ a) ▹ (⋀Δ : Proposition L)) ↔
        ∀ φ ∈ Δ, Semiformula.Eval ![] (stageAssign Δ a w) φ := by
    intro w
    rw [Semiformula.eval_rew]
    rw [show (Semiterm.val w (Empty.elim : Empty → M) ∘ Rew.bind ![] (stageSubst Δ a) ∘
        Semiterm.bvar) = ![] from by funext i; exact i.elim0]
    exact eval_conj_list _ Δ
  have hassign_a : ∀ (w : Fin (q + stageTypeBound Δ a) → M) (i : Fin q),
      stageAssign Δ a w (a i) = w (i.addNat (stageTypeBound Δ a)) := by
    intro w i
    simp [stageAssign, stageSubst_apply Δ ha i]
  constructor
  · intro h
    rw [stageType, Semiformula.Evalb, Semiformula.eval_exsItr] at h
    obtain ⟨e', he'⟩ := h
    refine ⟨stageAssign Δ a (Matrix.appendr e' b), fun i ↦ ?_, (hstep _).mp he'⟩
    rw [hassign_a]
    exact Matrix.appeendr_addNat e' b i
  · rintro ⟨ε, hεa, hεΔ⟩
    rw [stageType, Semiformula.Evalb, Semiformula.eval_exsItr]
    refine ⟨fun j : Fin (stageTypeBound Δ a) => ε j, ?_⟩
    -- the induced assignment agrees with `ε` below the bound
    have hagree : ∀ v : ℕ, v < stageTypeBound Δ a →
        stageAssign Δ a (Matrix.appendr (fun j : Fin (stageTypeBound Δ a) => ε j) b) v = ε v := by
      intro v hv
      by_cases hr : ∃ i, a i = v
      · obtain ⟨i, rfl⟩ := hr
        rw [hassign_a, Matrix.appeendr_addNat, hεa]
      · rw [stageAssign, stageSubst_of_not_mem_range Δ hr hv]
        have he : (⟨v, by omega⟩ : Fin (q + stageTypeBound Δ a))
            = (⟨v, hv⟩ : Fin (stageTypeBound Δ a)).addCast q := rfl
        simp only [Semiterm.val_bvar, he]
        exact Matrix.appeendr_addCast _ b _
    refine (hstep _).mpr fun φ hφ ↦ ?_
    refine (Semiformula.eval_iff_of_funEqOn φ ?_).mpr (hεΔ φ hφ)
    intro x hx
    exact hagree x (lt_of_lt_of_le (Semiformula.lt_fvSup_of_fvar? hx) (fvSup_le_stageTypeBound hφ a))

/-! ### The omitting step -/

/-- The omitting step of the Henkin construction. If `T` locally omits `Ψ`, then any finite stage
`Δ` consistent over `T` can be extended, at any injective tuple `a` of free variables, by the
denial of some member of `Ψ`. -/
theorem exists_omit_consistentOver {T : Theory L} {q : ℕ} {Ψ : PartialType L q}
    (hΨ : LocallyOmits T Ψ) (a : Fin q → ℕ) (ha : Function.Injective a)
    (Δ : List (Proposition L)) (hΔ : ConsistentOver T {φ | φ ∈ Δ}) :
    ∃ ψ ∈ Ψ, ConsistentOver T {φ | φ ∈ (∼(substTuple ψ a) :: Δ)} := by
  classical
  -- a model of `T` realizing the stage
  obtain ⟨M, hMne, hMs, ε, hMT, hεΔ⟩ := exists_model_of_consistentOver_list hΔ
  have hb : Semiformula.Evalb (fun i ↦ ε (a i)) (stageType Δ a) :=
    (evalb_stageType Δ ha _).mpr ⟨ε, fun _ ↦ rfl, hεΔ⟩
  have hMmod : M↓[L] ⊧* T := hMT
  have hcon : Consistent (insert (∃¹* (stageType Δ a)) T) :=
    consistent_insert_of_model M (by simpa [models_iff] using ⟨_, hb⟩)
  -- local omission gives a member of `Ψ` that can be denied
  obtain ⟨ψ, hψΨ, hcon'⟩ := hΨ (stageType Δ a) hcon
  obtain ⟨M', hM'ne, hM's, hM'mod⟩ :=
    LO.FirstOrder.satisfiable_iff.mp (Theory.small_satisfiable_of_consistent hcon')
  have hM'T : M'↓[L] ⊧* T := Semantics.ModelsSet.of_subset hM'mod (Set.subset_insert _ _)
  have hsat : M'↓[L] ⊧ (∃¹* (stageType Δ a ⋏ ∼ψ) : Sentence L) :=
    Semantics.modelsSet_iff.mp hM'mod (Set.mem_insert _ _)
  have : ∃ c : Fin q → M', Semiformula.Evalb c (stageType Δ a) ∧ ¬Semiformula.Evalb c ψ := by
    simpa [models_iff] using hsat
  obtain ⟨c, hc, hcψ⟩ := this
  obtain ⟨ε', hε'a, hε'Δ⟩ := (evalb_stageType Δ ha c).mp hc
  refine ⟨ψ, hψΨ, consistentOver_list_of_model hM'T ε' ?_⟩
  intro φ hφ
  rcases List.mem_cons.mp hφ with rfl | hφ
  · have : ¬Semiformula.Eval ![] ε' (substTuple ψ a) := by
      rw [eval_substTuple]
      simpa [hε'a] using hcψ
    simpa using this
  · exact hε'Δ φ hφ

end ZFVP
