import ZFVP.ModelTheory.RubinStage

/-! # The alternating quantifier blocks of Enayat's Lemmas A.3 and A.4

Enayat's Lemmas A.3 and A.4 read a sentence `φ(d_{k₁}, …, d_{k_p})` of the language with the
constants `d_n` off two statements about `M` with `p` alternating quantifier blocks over the
directed sets `D_{k_i}`:

* A.3: `T ⊢ φ(d⃗)` iff `M ⊨ ∃r₁∈D_{k₁} ∀s₁∈D_{k₁} … ∃r_p ∀s_p [(⋀ᵢ rᵢ < sᵢ) → φ(s₁,…,s_p)]`;
* A.4: `T + φ(d⃗)` is consistent iff `M ⊨ ∀r₁∈D_{k₁} ∃s₁∈D_{k₁} … ∀r_p ∃s_p
  [(⋀ᵢ rᵢ < sᵢ) ∧ φ(s₁,…,s_p)]`.

This file builds the two blocks and proves the combinatorial facts about them that Enayat's
Lemma A.5 uses. It does not prove A.3, A.4 or A.5.

That alternating reading of A.4 is false, so the file also builds the form with all `r`
quantifiers in front of all `s` quantifiers, `BlockEx` and `BlockAll`:

* A.3: `T ⊢ φ(d⃗)` iff `M ⊨ ∃r⃗ ∈ D⃗ ∀s⃗ ∈ D⃗ [(⋀ᵢ rᵢ <_{D_{k_i}} sᵢ) → φ(s⃗)]`;
* A.4: `T + φ(d⃗)` is consistent iff `M ⊨ ∀r⃗ ∈ D⃗ ∃s⃗ ∈ D⃗ [(⋀ᵢ rᵢ <_{D_{k_i}} sᵢ) ∧ φ(s⃗)]`.

A counterexample to the alternating reading of A.4: let `M` be the standard naturals, `D_{k₁}`
the even numbers and `D_{k₂}` the odd ones, both ordered by `<`, and let
`φ(d_{k₁}, d_{k₂})` be `d_{k₂} < d_{k₁}`. The theory `T + φ(d⃗)` is consistent, since in an
ultrapower one can take `d_{k₂}` an infinite odd number and `d_{k₁}` a larger even one. The
alternating statement fails: after `s₁` is chosen the `∀r₂` is answered by `r₂ := s₁ + 1`, and
no odd `s₂ > r₂` is below `s₁`. The block forms are the ones both directions of A.3 and A.4 hold
for, so they, not `AltEx` and `AltAll`, are what the proofs of A.3 and A.4 use. The alternating
material is kept because it is what the paper prints.

Each block appears twice: as a meaning, `AltEx` for the A.4 block and `AltAll` for the A.3 block,
defined by recursion on `p` over an arbitrary body `P : (Fin p → M) → Prop`; and as a formula,
`altExFormula` and `altAllFormula`, built from `δ (ks i)` and `ρ (ks i)` by recursion on `p` over
a body formula. `eval_altExFormula` and `eval_altAllFormula` say the formula means the meaning.

Enayat guards the body by the single conjunction `⋀ᵢ rᵢ <_{D_{k_i}} sᵢ`. Here the guard
`rᵢ < sᵢ` sits at step `i` of the recursion instead. That is the same statement: each conjunct
mentions only its own pair of variables, and both `rᵢ` and `sᵢ` are already bound when step `i`
is reached, so pulling the conjunct out to the front of the body changes nothing.

The facts proved about the blocks are:

* `AltEx.mono` and `AltAll.mono`, monotonicity in the body;
* `AltAll.and`, turning `AltAll … P` and `AltAll … Q` into `AltAll … (P ∧ Q)`; this is Enayat's
  step from `λ(m) ⋏ γ(m)` to a single block, and it uses `DirectedNoLast.upper` to merge the two
  witnesses `r` and `DirectedNoLast.trans` to keep the guard;
* `altAll_altEx_contradiction`, the contradiction principle: `AltAll … P` and `AltEx … Q` with
  `P` and `Q` incompatible is absurd; this is what turns A.3 and A.4 into Enayat's final
  contradiction. It needs no hypothesis on the directed sets at all: the step instantiates the
  `∀ r` of `AltEx` at the `r` of `AltAll`, and the base case is immediate;
* `altAll_false`, the "no last element" step: `AltAll … (fun _ ↦ False)` is absurd. This one does
  use `DirectedNoLast.upper`, through `altEx_true`.

## The layout of the bound variables

`altExFormula δ ρ ks χ : SetTheorySemiformula M e` is built from a body
`χ : SetTheorySemiformula M (e + p)`, so `e` is the number of bound variables the block leaves
alone and `p` of them are consumed by the block. The de Bruijn layout is the one the nesting of
quantifiers forces: the innermost quantified variable is `#0`. Reading `χ`'s bound variables from
`#0` up, they are `s_p, s_{p-1}, …, s_1` and then the `e` variables the block does not touch. The
assignment that produces this vector out of `s : Fin p → M` (listed in Enayat's order, `s 0` for
`s₁`) and `b : Fin e → M` is `altBlockAssign`, characterised by `altBlockAssign_zero` and
`altBlockAssign_succ`; it is `b` after the reverse of `s`.

`altBlockAssign` and the two formula constructions are defined through auxiliary versions that
carry the arity as a variable `n` together with a proof of `n = e + p`. The recursion moves one
variable at a time from the `p` side to the `e` side, and `n` is what stays fixed while it does;
carrying it avoids re-associating `e + (p + 1)` to `(e + 1) + p` at every step.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

variable {M : Type u} [SetStructure M]

section Blocks

variable (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)

/-! ## The two blocks as meanings -/

/-- The block of Enayat's Lemma A.4: `∀r₁∈D_{k₁} ∃s₁∈D_{k₁} … ∀r_p ∃s_p` with the guard
`rᵢ <_{D_{k_i}} sᵢ` at each step and body `P (s₁, …, s_p)`. -/
def AltEx : (p : ℕ) → (Fin p → ℕ) → ((Fin p → M) → Prop) → Prop
  | 0, _, P => P ![]
  | p + 1, ks, P => ∀ r, dset δ (ks 0) r → ∃ s, dset δ (ks 0) s ∧ dlt ρ (ks 0) r s ∧
      AltEx p (fun i ↦ ks i.succ) (fun t ↦ P (s :> t))

/-- The block of Enayat's Lemma A.3: `∃r₁∈D_{k₁} ∀s₁∈D_{k₁} … ∃r_p ∀s_p` with the guard
`rᵢ <_{D_{k_i}} sᵢ` at each step implying the body `P (s₁, …, s_p)`. -/
def AltAll : (p : ℕ) → (Fin p → ℕ) → ((Fin p → M) → Prop) → Prop
  | 0, _, P => P ![]
  | p + 1, ks, P => ∃ r, dset δ (ks 0) r ∧ ∀ s, dset δ (ks 0) s → dlt ρ (ks 0) r s →
      AltAll p (fun i ↦ ks i.succ) (fun t ↦ P (s :> t))

@[simp] theorem altEx_zero (ks : Fin 0 → ℕ) (P : (Fin 0 → M) → Prop) :
    AltEx δ ρ 0 ks P ↔ P ![] := Iff.rfl

@[simp] theorem altAll_zero (ks : Fin 0 → ℕ) (P : (Fin 0 → M) → Prop) :
    AltAll δ ρ 0 ks P ↔ P ![] := Iff.rfl

theorem altEx_succ (p : ℕ) (ks : Fin (p + 1) → ℕ) (P : (Fin (p + 1) → M) → Prop) :
    AltEx δ ρ (p + 1) ks P ↔
      ∀ r, dset δ (ks 0) r → ∃ s, dset δ (ks 0) s ∧ dlt ρ (ks 0) r s ∧
        AltEx δ ρ p (fun i ↦ ks i.succ) (fun t ↦ P (s :> t)) := Iff.rfl

theorem altAll_succ (p : ℕ) (ks : Fin (p + 1) → ℕ) (P : (Fin (p + 1) → M) → Prop) :
    AltAll δ ρ (p + 1) ks P ↔
      ∃ r, dset δ (ks 0) r ∧ ∀ s, dset δ (ks 0) s → dlt ρ (ks 0) r s →
        AltAll δ ρ p (fun i ↦ ks i.succ) (fun t ↦ P (s :> t)) := Iff.rfl

/-! ## What the blocks do -/

/-- The `∀∃` block is monotone in its body. -/
theorem AltEx.mono : ∀ {p : ℕ} {ks : Fin p → ℕ} {P Q : (Fin p → M) → Prop},
    (∀ t, P t → Q t) → AltEx δ ρ p ks P → AltEx δ ρ p ks Q := by
  intro p
  induction p with
  | zero => intro ks P Q h hP; exact h _ hP
  | succ p ih =>
    intro ks P Q h hP
    rw [altEx_succ] at hP ⊢
    intro r hr
    obtain ⟨s, hs, hlt, hrest⟩ := hP r hr
    exact ⟨s, hs, hlt, ih (fun t ht ↦ h _ ht) hrest⟩

/-- The `∃∀` block is monotone in its body. -/
theorem AltAll.mono : ∀ {p : ℕ} {ks : Fin p → ℕ} {P Q : (Fin p → M) → Prop},
    (∀ t, P t → Q t) → AltAll δ ρ p ks P → AltAll δ ρ p ks Q := by
  intro p
  induction p with
  | zero => intro ks P Q h hP; exact h _ hP
  | succ p ih =>
    intro ks P Q h hP
    rw [altAll_succ] at hP ⊢
    obtain ⟨r, hr, hall⟩ := hP
    exact ⟨r, hr, fun s hs hlt ↦ ih (fun t ht ↦ h _ ht) (hall s hs hlt)⟩

/-- Two `∃∀` blocks over the same indices combine into one over the conjunction of their bodies.
The two witnesses `r` are merged by a common strict upper bound, and the guard of each block is
recovered from the guard of the merged one by transitivity. -/
theorem AltAll.and (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) :
    ∀ {p : ℕ} {ks : Fin p → ℕ} {P Q : (Fin p → M) → Prop},
      AltAll δ ρ p ks P → AltAll δ ρ p ks Q → AltAll δ ρ p ks (fun t ↦ P t ∧ Q t) := by
  intro p
  induction p with
  | zero => intro ks P Q hP hQ; exact ⟨hP, hQ⟩
  | succ p ih =>
    intro ks P Q hP hQ
    rw [altAll_succ] at hP hQ ⊢
    obtain ⟨r₁, hr₁, h₁⟩ := hP
    obtain ⟨r₂, hr₂, h₂⟩ := hQ
    obtain ⟨z, hz, hz₁, hz₂⟩ := (hdir (ks 0)).upper r₁ r₂ hr₁ hr₂
    refine ⟨z, hz, fun s hs hlt ↦ ?_⟩
    exact ih (h₁ s hs ((hdir (ks 0)).trans r₁ z s hr₁ hz hs hz₁ hlt))
      (h₂ s hs ((hdir (ks 0)).trans r₂ z s hr₂ hz hs hz₂ hlt))

/-- The contradiction principle: an `∃∀` block over `P` and an `∀∃` block over `Q` with the same
indices cannot both hold if `P` and `Q` are incompatible. No hypothesis on the directed sets is
needed: at each step the `∀ r` of the `∀∃` block is instantiated at the `r` of the `∃∀` block,
which produces a common `s`. -/
theorem altAll_altEx_contradiction : ∀ {p : ℕ} {ks : Fin p → ℕ} {P Q : (Fin p → M) → Prop},
    AltAll δ ρ p ks P → AltEx δ ρ p ks Q → (∀ t, P t → Q t → False) → False := by
  intro p
  induction p with
  | zero => intro ks P Q hP hQ h; exact h _ hP hQ
  | succ p ih =>
    intro ks P Q hP hQ h
    rw [altAll_succ] at hP
    rw [altEx_succ] at hQ
    obtain ⟨r, hr, hall⟩ := hP
    obtain ⟨s, hs, hlt, hex⟩ := hQ r hr
    exact ih (hall s hs hlt) hex (fun t ht ↦ h (s :> t) ht)

/-- The `∀∃` block over a body that is always true holds: this is exactly "no last element",
`DirectedNoLast.upper` at a repeated argument. -/
theorem altEx_true (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) :
    ∀ {p : ℕ} (ks : Fin p → ℕ), AltEx δ ρ p ks (fun _ ↦ True) := by
  intro p
  induction p with
  | zero => intro ks; exact trivial
  | succ p ih =>
    intro ks
    rw [altEx_succ]
    intro r hr
    obtain ⟨z, hz, hrz, _⟩ := (hdir (ks 0)).upper r r hr hr
    exact ⟨z, hz, hrz, ih _⟩

/-- An `∃∀` block over the empty body is absurd. -/
theorem altAll_false (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p : ℕ} {ks : Fin p → ℕ}
    (h : AltAll δ ρ p ks (fun _ ↦ False)) : False :=
  altAll_altEx_contradiction δ ρ h (altEx_true δ ρ hdir ks) (fun _ hP _ ↦ hP)

/-! ## The two blocks with all `r` quantifiers in front

`BlockEx` and `BlockAll` are the forms A.3 and A.4 actually hold for: the whole tuple `r⃗` is
quantified before the whole tuple `s⃗`, not one pair at a time. -/

/-- The block form of Enayat's Lemma A.4: `∀r⃗ ∈ D⃗ ∃s⃗ ∈ D⃗ [(⋀ᵢ rᵢ <_{D_{k_i}} sᵢ) ∧ P s⃗]`. -/
def BlockEx (p : ℕ) (ks : Fin p → ℕ) (P : (Fin p → M) → Prop) : Prop :=
  ∀ r : Fin p → M, (∀ i, dset δ (ks i) (r i)) →
    ∃ s : Fin p → M, (∀ i, dset δ (ks i) (s i)) ∧ (∀ i, dlt ρ (ks i) (r i) (s i)) ∧ P s

/-- The block form of Enayat's Lemma A.3: `∃r⃗ ∈ D⃗ ∀s⃗ ∈ D⃗ [(⋀ᵢ rᵢ <_{D_{k_i}} sᵢ) → P s⃗]`. -/
def BlockAll (p : ℕ) (ks : Fin p → ℕ) (P : (Fin p → M) → Prop) : Prop :=
  ∃ r : Fin p → M, (∀ i, dset δ (ks i) (r i)) ∧
    ∀ s : Fin p → M, (∀ i, dset δ (ks i) (s i)) → (∀ i, dlt ρ (ks i) (r i) (s i)) → P s

/-- The `∀⃗∃⃗` block is monotone in its body. -/
theorem BlockEx.mono {p : ℕ} {ks : Fin p → ℕ} {P Q : (Fin p → M) → Prop}
    (h : ∀ t, P t → Q t) (hP : BlockEx δ ρ p ks P) : BlockEx δ ρ p ks Q := by
  intro r hr
  obtain ⟨s, hs, hlt, hPs⟩ := hP r hr
  exact ⟨s, hs, hlt, h s hPs⟩

/-- The `∃⃗∀⃗` block is monotone in its body. -/
theorem BlockAll.mono {p : ℕ} {ks : Fin p → ℕ} {P Q : (Fin p → M) → Prop}
    (h : ∀ t, P t → Q t) (hP : BlockAll δ ρ p ks P) : BlockAll δ ρ p ks Q := by
  obtain ⟨r, hr, hall⟩ := hP
  exact ⟨r, hr, fun s hs hlt ↦ h s (hall s hs hlt)⟩

/-- Two `∃⃗∀⃗` blocks over the same indices combine into one over the conjunction of their bodies.
The two witnesses are merged coordinate by coordinate with `DirectedNoLast.upper`, and each
original guard comes back from the merged one by `DirectedNoLast.trans`. -/
theorem BlockAll.and (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p : ℕ} {ks : Fin p → ℕ}
    {P Q : (Fin p → M) → Prop} (hP : BlockAll δ ρ p ks P) (hQ : BlockAll δ ρ p ks Q) :
    BlockAll δ ρ p ks (fun t ↦ P t ∧ Q t) := by
  obtain ⟨r₁, hr₁, h₁⟩ := hP
  obtain ⟨r₂, hr₂, h₂⟩ := hQ
  choose z hz hz₁ hz₂ using fun i ↦ (hdir (ks i)).upper (r₁ i) (r₂ i) (hr₁ i) (hr₂ i)
  refine ⟨z, hz, fun s hs hlt ↦ ⟨h₁ s hs fun i ↦ ?_, h₂ s hs fun i ↦ ?_⟩⟩
  · exact (hdir (ks i)).trans _ _ _ (hr₁ i) (hz i) (hs i) (hz₁ i) (hlt i)
  · exact (hdir (ks i)).trans _ _ _ (hr₂ i) (hz i) (hs i) (hz₂ i) (hlt i)

/-- The contradiction principle for the block forms: an `∃⃗∀⃗` block over `P` and an `∀⃗∃⃗` block
over `Q` with the same indices cannot both hold when `P` and `Q` are incompatible. The `r⃗` of the
`∃⃗∀⃗` block is fed to the `∀ r⃗` of the `∀⃗∃⃗` block, which returns a tuple `s⃗` satisfying both
bodies. No hypothesis on the directed sets is needed. -/
theorem blockAll_blockEx_contradiction {p : ℕ} {ks : Fin p → ℕ} {P Q : (Fin p → M) → Prop}
    (hP : BlockAll δ ρ p ks P) (hQ : BlockEx δ ρ p ks Q) (h : ∀ t, P t → Q t → False) : False := by
  obtain ⟨r, hr, hall⟩ := hP
  obtain ⟨s, hs, hlt, hQs⟩ := hQ r hr
  exact h s (hall s hs hlt) hQs

/-- The two block forms are each other's negation, which is what makes A.3 and A.4
contrapositives of each other. -/
theorem not_blockEx_iff {p : ℕ} {ks : Fin p → ℕ} {P : (Fin p → M) → Prop} :
    ¬BlockEx δ ρ p ks P ↔ BlockAll δ ρ p ks (fun t ↦ ¬P t) := by
  classical
  constructor
  · intro h
    by_contra hc
    refine h fun r hr ↦ ?_
    by_contra hcs
    exact hc ⟨r, hr, fun s hs hlt hPs ↦ hcs ⟨s, hs, hlt, hPs⟩⟩
  · rintro ⟨r, hr, hall⟩ hEx
    obtain ⟨s, hs, hlt, hPs⟩ := hEx r hr
    exact hall s hs hlt hPs

/-- The dual of `not_blockEx_iff`. -/
theorem not_blockAll_iff {p : ℕ} {ks : Fin p → ℕ} {P : (Fin p → M) → Prop} :
    ¬BlockAll δ ρ p ks P ↔ BlockEx δ ρ p ks (fun t ↦ ¬P t) := by
  classical
  constructor
  · intro h r hr
    by_contra hc
    exact h ⟨r, hr, fun s hs hlt ↦ not_not.mp fun hnp ↦ hc ⟨s, hs, hlt, hnp⟩⟩
  · rintro hEx ⟨r, hr, hall⟩
    obtain ⟨s, hs, hlt, hnPs⟩ := hEx r hr
    exact hnPs (hall s hs hlt)

/-- The `∀⃗∃⃗` block over a body that is always true holds: `DirectedNoLast.upper` at a repeated
argument, coordinate by coordinate. -/
theorem blockEx_true (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p : ℕ}
    (ks : Fin p → ℕ) : BlockEx δ ρ p ks (fun _ ↦ True) := by
  intro r hr
  choose z hz hrz _ using fun i ↦ (hdir (ks i)).upper (r i) (r i) (hr i) (hr i)
  exact ⟨z, hz, hrz, trivial⟩

/-- An `∃⃗∀⃗` block over the empty body is absurd. -/
theorem blockAll_false (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p : ℕ}
    {ks : Fin p → ℕ} (h : BlockAll δ ρ p ks (fun _ ↦ False)) : False :=
  blockAll_blockEx_contradiction δ ρ h (blockEx_true δ ρ hdir ks) (fun _ hP _ ↦ hP)

/-- The `∀⃗∃⃗` block against a finite set of lower bounds in each coordinate: the tuple `s⃗` can be
asked to lie strictly above every member of a given finite subset `A i` of `D_{k_i}`. This is the
form the finite satisfiability half of A.4 uses. -/
theorem blockEx_upper (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) {p : ℕ}
    {ks : Fin p → ℕ} {P : (Fin p → M) → Prop} (hP : BlockEx δ ρ p ks P)
    (A : Fin p → Finset M) (hA : ∀ i, ∀ m ∈ A i, dset δ (ks i) m) :
    ∃ s : Fin p → M, (∀ i, dset δ (ks i) (s i)) ∧ (∀ i, ∀ m ∈ A i, dlt ρ (ks i) m (s i)) ∧ P s := by
  choose d hd hdA using fun i ↦ (hdir (ks i)).exists_upper_bound (A i) (hA i)
  obtain ⟨s, hs, hlt, hPs⟩ := hP d hd
  refine ⟨s, hs, fun i m hm ↦ ?_, hPs⟩
  exact (hdir (ks i)).trans m (d i) (s i) (hA i m hm) (hd i) (hs i) (hdA i m hm) (hlt i)

/-- The alternating `∀∃` block implies the block form: the `s⃗` is read off one coordinate at a
time, feeding `r i` to the `i`-th step. -/
theorem AltEx.toBlockEx : ∀ {p : ℕ} {ks : Fin p → ℕ} {P : (Fin p → M) → Prop},
    AltEx δ ρ p ks P → BlockEx δ ρ p ks P := by
  intro p
  induction p with
  | zero =>
    intro ks P hP r _
    exact ⟨![], fun i ↦ i.elim0, fun i ↦ i.elim0, by simpa [Matrix.empty_eq] using hP⟩
  | succ p ih =>
    intro ks P hP r hr
    rw [altEx_succ] at hP
    obtain ⟨s₀, hs₀, hlt₀, hrest⟩ := hP (r 0) (hr 0)
    obtain ⟨t, ht, htlt, hPt⟩ := ih hrest (fun i ↦ r i.succ) (fun i ↦ hr i.succ)
    refine ⟨s₀ :> t, fun i ↦ ?_, fun i ↦ ?_, hPt⟩
    · exact Fin.cases hs₀ (fun j ↦ ht j) i
    · exact Fin.cases hlt₀ (fun j ↦ htlt j) i

/-- The block `∃∀` form implies the alternating one: the same tuple `r⃗` works, read one
coordinate at a time. -/
theorem BlockAll.toAltAll : ∀ {p : ℕ} {ks : Fin p → ℕ} {P : (Fin p → M) → Prop},
    BlockAll δ ρ p ks P → AltAll δ ρ p ks P := by
  intro p
  induction p with
  | zero =>
    intro ks P hP
    obtain ⟨r, _, hall⟩ := hP
    exact hall ![] (fun i ↦ i.elim0) (fun i ↦ i.elim0)
  | succ p ih =>
    intro ks P hP
    obtain ⟨r, hr, hall⟩ := hP
    rw [altAll_succ]
    refine ⟨r 0, hr 0, fun s hs hlt ↦ ih ⟨fun i ↦ r i.succ, fun i ↦ hr i.succ, ?_⟩⟩
    intro t ht htlt
    refine hall (s :> t) (fun i ↦ Fin.cases hs (fun j ↦ ht j) i)
      (fun i ↦ Fin.cases hlt (fun j ↦ htlt j) i)

end Blocks

/-! ## The assignment of the bound variables

`altBlockAssign h s b` is the vector of length `n = e + p` that the block's quantifiers leave for
the body: the reverse of `s`, then `b`. -/

/-- The assignment the block's quantifiers hand to the body: `s (p-1), …, s 1, s 0` followed by
`b`, that is, the reverse of `s` followed by `b`.
The arity is carried as `n` with a proof `n = e + p` so that the step of the recursion, which
moves `s 0` from the `s` side to the `b` side, does not change it. -/
def altBlockAssign : (p : ℕ) → {e n : ℕ} → n = e + p → (Fin p → M) → (Fin e → M) → Fin n → M
  | 0, _, _, h, _, b => fun i ↦ b (i.castLE (by omega))
  | p + 1, _, _, h, s, b => altBlockAssign p (by omega) (fun i ↦ s i.succ) (s 0 :> b)

omit [SetStructure M] in
theorem altBlockAssign_zero {e n : ℕ} (h : n = e + 0) (s : Fin 0 → M) (b : Fin e → M) :
    altBlockAssign 0 h s b = fun i ↦ b (i.castLE (le_of_eq (by omega))) := rfl

omit [SetStructure M] in
theorem altBlockAssign_succ {p e n : ℕ} (h : n = e + (p + 1)) (x : M) (t : Fin p → M)
    (b : Fin e → M) :
    altBlockAssign (p + 1) h (x :> t) b =
      altBlockAssign p (show n = (e + 1) + p by omega) t (x :> b) := by
  show altBlockAssign p _ (fun i ↦ (x :> t) i.succ) ((x :> t) 0 :> b) = _
  simp

section Formulas

variable (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)

/-- `δ n` with its single bound variable replaced by the term `t`. -/
theorem eval_dset_substs {m : ℕ} (n : ℕ) (t : Semiterm ℒₛₑₜ M m) (b : Fin m → M) :
    Semiformula.Eval b id (δ n ⇜ ![t]) ↔ dset δ n (Semiterm.val b id t) := by
  rw [Semiformula.eval_substs]
  have h : (Semiterm.val (s := SetTheory.standardStructure M) b id ∘ ![t])
      = ![Semiterm.val b id t] := by
    funext i; exact Fin.cases rfl (fun j ↦ j.elim0) i
  rw [h]
  rfl

/-- `ρ n` with its two bound variables replaced by the terms `t` and `u`. -/
theorem eval_dlt_substs {m : ℕ} (n : ℕ) (t u : Semiterm ℒₛₑₜ M m) (b : Fin m → M) :
    Semiformula.Eval b id (ρ n ⇜ ![t, u]) ↔
      dlt ρ n (Semiterm.val b id t) (Semiterm.val b id u) := by
  rw [Semiformula.eval_substs]
  have h : (Semiterm.val (s := SetTheory.standardStructure M) b id ∘ ![t, u])
      = ![Semiterm.val b id t, Semiterm.val b id u] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j) i
  rw [h]
  rfl

/-- The `∀∃` block as a formula, with the arity carried as `n = e + p`. -/
def altExFormulaAux : (p : ℕ) → (Fin p → ℕ) → {e n : ℕ} → n = e + p →
    SetTheorySemiformula M n → SetTheorySemiformula M e
  | 0, _, _, _, h, χ => Rew.castLE (by omega) ▹ χ
  | p + 1, ks, e, n, h, χ =>
      ∀¹ ((δ (ks 0) ⇜ ![#0]) 🡒
        (∃¹ ((δ (ks 0) ⇜ ![#0]) ⋏ (ρ (ks 0) ⇜ ![#1, #0]) ⋏
          (altExFormulaAux p (fun i ↦ ks i.succ) (show n = (e + 1) + p by omega) χ ⇜
            (#0 :> (#·.succ.succ))))))

/-- The `∃∀` block as a formula, with the arity carried as `n = e + p`. -/
def altAllFormulaAux : (p : ℕ) → (Fin p → ℕ) → {e n : ℕ} → n = e + p →
    SetTheorySemiformula M n → SetTheorySemiformula M e
  | 0, _, _, _, h, χ => Rew.castLE (by omega) ▹ χ
  | p + 1, ks, e, n, h, χ =>
      ∃¹ ((δ (ks 0) ⇜ ![#0]) ⋏
        (∀¹ (((δ (ks 0) ⇜ ![#0]) ⋏ (ρ (ks 0) ⇜ ![#1, #0])) 🡒
          (altAllFormulaAux p (fun i ↦ ks i.succ) (show n = (e + 1) + p by omega) χ ⇜
            (#0 :> (#·.succ.succ))))))

/-- The `∀∃` block of Enayat's Lemma A.4 as a formula: `∀r₁∈D_{k₁} ∃s₁∈D_{k₁} … ∀r_p ∃s_p` with
the guards, over the body `χ`. The first `p` bound variables of `χ` are the `sᵢ`, innermost
first, and its remaining `e` bound variables are left alone. -/
def altExFormula {p : ℕ} (ks : Fin p → ℕ) {e : ℕ} (χ : SetTheorySemiformula M (e + p)) :
    SetTheorySemiformula M e :=
  altExFormulaAux δ ρ p ks rfl χ

/-- The `∃∀` block of Enayat's Lemma A.3 as a formula: `∃r₁∈D_{k₁} ∀s₁∈D_{k₁} … ∃r_p ∀s_p` with
the guards implying the body `χ`. The first `p` bound variables of `χ` are the `sᵢ`, innermost
first, and its remaining `e` bound variables are left alone. -/
def altAllFormula {p : ℕ} (ks : Fin p → ℕ) {e : ℕ} (χ : SetTheorySemiformula M (e + p)) :
    SetTheorySemiformula M e :=
  altAllFormulaAux δ ρ p ks rfl χ

theorem eval_altExFormulaAux : ∀ (p : ℕ) (ks : Fin p → ℕ) {e n : ℕ} (h : n = e + p)
    (χ : SetTheorySemiformula M n) (b : Fin e → M),
    Semiformula.Eval b id (altExFormulaAux δ ρ p ks h χ) ↔
      AltEx δ ρ p ks fun s ↦ Semiformula.Eval (altBlockAssign p h s b) id χ := by
  intro p
  induction p with
  | zero =>
    intro ks e n h χ b
    simp only [altExFormulaAux, Semiformula.eval_castLE, altEx_zero, altBlockAssign_zero]
  | succ p ih =>
    intro ks e n h χ b
    rw [altEx_succ]
    simp only [altExFormulaAux, Semiformula.eval_all, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
      eval_dset_substs, eval_dlt_substs, Semiterm.val_bvar, Matrix.cons_val_zero,
      Matrix.cons_val_one, Semiformula.eval_insert1, ih]
    refine forall_congr' fun r ↦ ?_
    refine imp_congr_right fun _ ↦ ?_
    refine exists_congr fun s ↦ ?_
    simp only [altBlockAssign_succ]
    exact Iff.rfl

theorem eval_altAllFormulaAux : ∀ (p : ℕ) (ks : Fin p → ℕ) {e n : ℕ} (h : n = e + p)
    (χ : SetTheorySemiformula M n) (b : Fin e → M),
    Semiformula.Eval b id (altAllFormulaAux δ ρ p ks h χ) ↔
      AltAll δ ρ p ks fun s ↦ Semiformula.Eval (altBlockAssign p h s b) id χ := by
  intro p
  induction p with
  | zero =>
    intro ks e n h χ b
    simp only [altAllFormulaAux, Semiformula.eval_castLE, altAll_zero, altBlockAssign_zero]
  | succ p ih =>
    intro ks e n h χ b
    rw [altAll_succ]
    simp only [altAllFormulaAux, Semiformula.eval_all, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
      eval_dset_substs, eval_dlt_substs, Semiterm.val_bvar, Matrix.cons_val_zero,
      Matrix.cons_val_one, Semiformula.eval_insert1, ih]
    refine exists_congr fun r ↦ ?_
    refine and_congr_right fun _ ↦ ?_
    refine forall_congr' fun s ↦ ?_
    simp only [altBlockAssign_succ]
    exact and_imp

/-- The `∀∃` block of Lemma A.4 means what it should: the formula holds at `b` exactly when the
block holds with the body read off `χ` at `altBlockAssign rfl s b`, the reverse of `s` followed
by `b`. -/
theorem eval_altExFormula {p : ℕ} (ks : Fin p → ℕ) {e : ℕ}
    (χ : SetTheorySemiformula M (e + p)) (b : Fin e → M) :
    Semiformula.Eval b id (altExFormula δ ρ ks χ) ↔
      AltEx δ ρ p ks fun s ↦ Semiformula.Eval (altBlockAssign p rfl s b) id χ :=
  eval_altExFormulaAux δ ρ p ks rfl χ b

/-- The `∃∀` block of Lemma A.3 means what it should. -/
theorem eval_altAllFormula {p : ℕ} (ks : Fin p → ℕ) {e : ℕ}
    (χ : SetTheorySemiformula M (e + p)) (b : Fin e → M) :
    Semiformula.Eval b id (altAllFormula δ ρ ks χ) ↔
      AltAll δ ρ p ks fun s ↦ Semiformula.Eval (altBlockAssign p rfl s b) id χ :=
  eval_altAllFormulaAux δ ρ p ks rfl χ b

/-! ## The block forms as formulas

The layout of the bound variables in `blockExFormula` and `blockAllFormula` is the one
`Semiformula.eval_exsItr` and `Semiformula.eval_allItr` produce: a block of `k` quantifiers puts
its own variables at the `k` lowest indices and moves the previous context up, which is
`Matrix.appendr`. So in the innermost context, of arity `(e + p) + p`, the `p` lowest slots hold
`s⃗`, the next `p` hold `r⃗`, and the top `e` are the outer variables. The body `χ` has arity
`e + p` and is read at `Matrix.appendr s b`: `s 0, …, s (p-1)` at the low slots and the outer
assignment `b` above them. `blockBodySubst` moves `χ` from that context into the innermost one by
stepping its outer variables over the `r⃗` block. For a concrete `p` the vector `Matrix.appendr s b`
is computed by `simp` with `Matrix.appendr_cons` and `Matrix.appendr_nil`. -/

theorem appendr_comp {α β : Type*} {n m : ℕ} (f : α → β) (u : Fin m → α) (v : Fin n → α) :
    f ∘ Matrix.appendr u v = Matrix.appendr (f ∘ u) (f ∘ v) := by
  funext i
  simp only [Function.comp_apply, Matrix.appendr, Matrix.vecAppend_eq_ite]
  split <;> rfl

/-- Peeling one coordinate off `Matrix.appendr`. With `Matrix.appendr_nil` and
`Matrix.empty_eq` this unfolds the body's assignment `Matrix.appendr s b` into
`s 0 :> s 1 :> … :> b` for a concrete `p`. -/
theorem appendr_succ {p e : ℕ} (s : Fin (p + 1) → M) (b : Fin e → M) :
    Matrix.appendr s b = s 0 :> Matrix.appendr (fun i ↦ s i.succ) b := by
  have h : s = s 0 :> (fun i ↦ s i.succ) := by
    funext i; cases i using Fin.cases <;> simp
  conv_lhs => rw [h]
  rw [Matrix.appendr_cons]

/-- The conjunction `⋀ᵢ (s i ∈ D_{k_i})` with the variable of the `i`-th conjunct given by `v i`. -/
def dsetGuard {p : ℕ} (ks : Fin p → ℕ) {m : ℕ} (v : Fin p → Fin m) : SetTheorySemiformula M m :=
  Matrix.conj fun i ↦ δ (ks i) ⇜ ![#(v i)]

/-- The conjunction `⋀ᵢ (r i <_{D_{k_i}} s i)` with the variables of the `i`-th conjunct given by
`v i` and `w i`. -/
def dltGuard {p : ℕ} (ks : Fin p → ℕ) {m : ℕ} (v w : Fin p → Fin m) : SetTheorySemiformula M m :=
  Matrix.conj fun i ↦ ρ (ks i) ⇜ ![#(v i), #(w i)]

@[simp] theorem eval_dsetGuard {p m : ℕ} (ks : Fin p → ℕ) (v : Fin p → Fin m) (b : Fin m → M) :
    Semiformula.Eval b id (dsetGuard δ ks v) ↔ ∀ i, dset δ (ks i) (b (v i)) := by
  simp only [dsetGuard, Matrix.conj_hom_prop, eval_dset_substs, Semiterm.val_bvar]

@[simp] theorem eval_dltGuard {p m : ℕ} (ks : Fin p → ℕ) (v w : Fin p → Fin m) (b : Fin m → M) :
    Semiformula.Eval b id (dltGuard ρ ks v w) ↔ ∀ i, dlt ρ (ks i) (b (v i)) (b (w i)) := by
  simp only [dltGuard, Matrix.conj_hom_prop, eval_dlt_substs, Semiterm.val_bvar]

/-- The substitution that takes the body of a block, whose `e + p` variables are `s⃗` followed by
the outer variables, into the innermost context of the block, of arity `(e + p) + p`, where the
`r⃗` block sits between the two groups. -/
def blockBodySubst (e p : ℕ) : Fin (e + p) → Semiterm ℒₛₑₜ M ((e + p) + p) :=
  Matrix.appendr (fun i : Fin p ↦ #(i.addCast (e + p))) (fun j : Fin e ↦ #((j.addNat p).addNat p))

/-- Evaluating `blockBodySubst` at the innermost assignment gives back `Matrix.appendr s b`: the
substitution drops the `r⃗` block. -/
@[simp] theorem val_blockBodySubst {e p : ℕ} (s r : Fin p → M) (b : Fin e → M) :
    Semiterm.val (s := SetTheory.standardStructure M)
        (Matrix.appendr s (Matrix.appendr r b)) id ∘ blockBodySubst e p
      = Matrix.appendr s b := by
  rw [blockBodySubst, appendr_comp]
  simp [Function.comp_def]

/-- The block form of Enayat's Lemma A.4 as a formula:
`∀r⃗ ∈ D⃗ ∃s⃗ ∈ D⃗ [(⋀ᵢ rᵢ < sᵢ) ∧ χ]`. -/
def blockExFormula {p : ℕ} (ks : Fin p → ℕ) {e : ℕ} (χ : SetTheorySemiformula M (e + p)) :
    SetTheorySemiformula M e :=
  ∀¹^[p] (dsetGuard δ ks (fun i ↦ i.addCast e) 🡒
    ∃¹^[p] (dsetGuard δ ks (fun i ↦ i.addCast (e + p)) ⋏
      (dltGuard ρ ks (fun i ↦ (i.addCast e).addNat p) (fun i ↦ i.addCast (e + p)) ⋏
        (χ ⇜ blockBodySubst e p))))

/-- The block form of Enayat's Lemma A.3 as a formula:
`∃r⃗ ∈ D⃗ ∀s⃗ ∈ D⃗ [(⋀ᵢ rᵢ < sᵢ) → χ]`. -/
def blockAllFormula {p : ℕ} (ks : Fin p → ℕ) {e : ℕ} (χ : SetTheorySemiformula M (e + p)) :
    SetTheorySemiformula M e :=
  ∃¹^[p] (dsetGuard δ ks (fun i ↦ i.addCast e) ⋏
    ∀¹^[p] ((dsetGuard δ ks (fun i ↦ i.addCast (e + p)) ⋏
        dltGuard ρ ks (fun i ↦ (i.addCast e).addNat p) (fun i ↦ i.addCast (e + p))) 🡒
      (χ ⇜ blockBodySubst e p)))

/-- `blockExFormula` means `BlockEx`, with the body read at `Matrix.appendr s b`. -/
theorem eval_blockExFormula {p : ℕ} (ks : Fin p → ℕ) {e : ℕ}
    (χ : SetTheorySemiformula M (e + p)) (b : Fin e → M) :
    Semiformula.Eval b id (blockExFormula δ ρ ks χ) ↔
      BlockEx δ ρ p ks fun s ↦ Semiformula.Eval (Matrix.appendr s b) id χ := by
  rw [blockExFormula, BlockEx]
  simp only [Semiformula.eval_allItr, Semiformula.eval_exsItr,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_imply,
    eval_dsetGuard, eval_dltGuard,
    Matrix.appeendr_addCast, Matrix.appeendr_addNat, Semiformula.eval_substs,
    val_blockBodySubst]
  exact Iff.rfl

/-- `blockAllFormula` means `BlockAll`, with the body read at `Matrix.appendr s b`. -/
theorem eval_blockAllFormula {p : ℕ} (ks : Fin p → ℕ) {e : ℕ}
    (χ : SetTheorySemiformula M (e + p)) (b : Fin e → M) :
    Semiformula.Eval b id (blockAllFormula δ ρ ks χ) ↔
      BlockAll δ ρ p ks fun s ↦ Semiformula.Eval (Matrix.appendr s b) id χ := by
  rw [blockAllFormula, BlockAll]
  simp only [Semiformula.eval_exsItr, Semiformula.eval_allItr,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_imply,
    eval_dsetGuard, eval_dltGuard,
    Matrix.appeendr_addCast, Matrix.appeendr_addNat, Semiformula.eval_substs,
    val_blockBodySubst]
  constructor
  · rintro ⟨r, hr, hall⟩
    exact ⟨r, hr, fun s hs hlt ↦ hall s ⟨hs, hlt⟩⟩
  · rintro ⟨r, hr, hall⟩
    exact ⟨r, hr, fun s hsl ↦ hall s hsl.1 hsl.2⟩

end Formulas

end ZFVP
