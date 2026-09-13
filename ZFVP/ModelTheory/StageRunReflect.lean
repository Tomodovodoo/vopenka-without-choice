import ZFVP.ModelTheory.StageRun
import ZFVP.ModelTheory.StageClubs
import ZFVP.ModelTheory.StageDefinability
import ZFVP.ModelTheory.StageObligations

/-! # The reflection clause of Enayat's ω₁-length construction

This is the reflection half of Stage 1 of the Appendix of Enayat's "Models of set theory:
extensions and dead ends", conditions (5) and (6) on page 25. Given a `ZFVP.StageRun M Ω` whose
guesses come from a diamond sequence read through the bijection `code`, and a predicate `F` on `Ω`
that is not parametrically definable, `ZFVP.StageRun.reflect` produces one index `α` at which two
things hold at once:

* every element of the poset that lies in stage `α` and is outside `F` is incompatible with some
  element of `F` that also lies in stage `α`;
* the trace of `F` on stage `α` cannot be separated from its complement in the stage by a set
  definable in `Ω`.

That is the `reflect` field of `ZFVP.RubinChain`, with two of the hypotheses of that field replaced
by exactly what the argument uses: `hcompat`, saying that an element of the poset outside `F` is
incompatible with some element of `F` somewhere in the model, and undefinability of `F`.

The proof intersects three clubs of indices with the stationary set of correct diamond guesses.

* `C₁` (`ZFVP.exists_club_code_image`): the stage is the image under `code` of the initial segment
  below the index.
* `C₂` (`ZFVP.exists_club_closed`): the stage is closed under a choice of incompatible partner,
  which gives the first conjunct.
* `C₃` (`ZFVP.exists_club_closed` again, indexed by all formulas in one free variable with a finite
  tuple of parameters): the stage is closed under a choice of witness of disagreement between a
  formula and `F`. At such an index no predicate definable with parameters from the stage agrees
  with `F` on the stage. This is the Loewenheim-Skolem step of condition (5), in the only form the
  argument needs, so no expansion of the language by a predicate symbol appears here.

At an index in the intersection the guess is exactly the trace of `F` on the stage, the guessed
pair is inseparable inside the stage by `C₃`, the field `StageRun.keep` carries inseparability to
every later stage, and `ZFVP.StageChain.inseparable_union` lifts it to `Ω`.

## Which membership structure

`↥(R.stage α).carrier` carries both the stage's own `ZFVP.stageSetStructure` and Foundation's
`submodel`; typeclass search picks the first, which is the one `StageRun.keep` is stated with, and
`ZFVP.StageChain.stageSetStructure_eq` is the bridge used inside
`ZFVP.StageChain.inseparable_union`. See the module docstring of `ZFVP.ModelTheory.StageChainUnion`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

namespace StageRun

variable {M Ω : Type u} [SetStructure M] [SetStructure Ω] [Nonempty Ω]

/-- The index type of the third club: a formula in one free variable together with the length of
its tuple of parameters. -/
private abbrev FormulaIndex : Type := (n : ℕ) × SetTheorySemiformula (Fin n) 1

/-- A stage of a run, as a subset of the carrier. -/
private def carrierAt (R : StageRun M Ω) (α : OmegaOne) : Set Ω := (R.stage α).carrier

omit [Nonempty Ω] in
private theorem carrierAt_mono (R : StageRun M Ω) : Monotone (R.carrierAt) :=
  fun _ _ h ↦ R.inc h

/-- Enayat's conditions (5) and (6) at one index: some stage of the run both computes the
incompatibility witnesses of `F` and traces `F` inseparably from its complement. -/
theorem reflect (R : StageRun M Ω) {A : OmegaOne → Set OmegaOne} (hA : IsDiamondSequence A)
    (hguess : ∀ α, R.guess α = R.code '' (A α))
    (P : Ω → Prop) (le : Ω → Ω → Prop) (F : Ω → Prop)
    (hcompat : ∀ q, P q → ¬ F q → ∃ p, F p ∧ ¬ ∃ z, P z ∧ le p z ∧ le q z)
    (hFdef : ¬ (ℒₛₑₜ-predicate[Ω] F)) :
    ∃ α : OmegaOne,
      (∀ q, q ∈ (R.stage α).carrier → P q → ¬ F q →
         ∃ p, p ∈ (R.stage α).carrier ∧ F p ∧ ¬ ∃ z, P z ∧ le p z ∧ le q z) ∧
      Inseparable Ω (fun x ↦ x ∈ (R.stage α).carrier ∧ F x)
        (fun x ↦ x ∈ (R.stage α).carrier ∧ ¬ F x) := by
  classical
  set A' : OmegaOne → Set Ω := R.carrierAt with hA'
  have hmono : Monotone A' := R.carrierAt_mono
  have hcount : ∀ α, (A' α).Countable := R.countable
  have hcover : ∀ x : Ω, ∃ α, x ∈ A' α := R.cover
  have hlim : ∀ α, IsLimitIndex α → A' α = {x | ∃ β, β < α ∧ x ∈ A' β} := R.limit_carrier
  -- Club 1: the stage is the image of the initial segment below the index.
  obtain ⟨C₁, hC₁, hC₁mem⟩ := exists_club_code_image R.code A' hmono hcount hcover hlim
  -- Club 2: closure under a choice of incompatible partner.
  have hpick : ∀ q : Ω, ∃ p : Ω,
      P q → ¬ F q → (F p ∧ ¬ ∃ z, P z ∧ le p z ∧ le q z) := by
    intro q
    by_cases h : P q ∧ ¬ F q
    · obtain ⟨p, hp⟩ := hcompat q h.1 h.2
      exact ⟨p, fun _ _ ↦ hp⟩
    · exact ⟨q, fun h1 h2 ↦ absurd ⟨h1, h2⟩ h⟩
  choose gc hgc using hpick
  obtain ⟨C₂, hC₂, hC₂mem⟩ := exists_club_closed A' hmono hcount hcover hlim
    (ι := Unit) (fun _ ↦ 1) (fun _ v ↦ gc (v 0))
  -- Club 3: closure under a choice of witness of disagreement with `F`.
  have hwit : ∀ (i : FormulaIndex) (v : Fin i.1 → Ω), ∃ z : Ω,
      (∃ z', ¬ (i.2.Eval ![z'] v ↔ F z')) → ¬ (i.2.Eval ![z] v ↔ F z) := by
    intro i v
    by_cases h : ∃ z', ¬ (i.2.Eval ![z'] v ↔ F z')
    · obtain ⟨z, hz⟩ := h
      exact ⟨z, fun _ ↦ hz⟩
    · exact ⟨Classical.arbitrary Ω, fun h' ↦ absurd h' h⟩
  choose gw hgw using hwit
  obtain ⟨C₃, hC₃, hC₃mem⟩ := exists_club_closed A' hmono hcount hcover hlim
    (ι := FormulaIndex) (fun i ↦ i.1) gw
  -- At an index of `C₃`, no predicate definable over the stage agrees with `F` on the stage.
  have hno : ∀ α ∈ C₃, ∀ D : Ω → Prop, DefinableOver (A' α) D →
      ¬ ∀ x ∈ A' α, (D x ↔ F x) := by
    rintro α hα D ⟨n, φ, f, hf, hD⟩ hagree
    by_cases hall : ∀ z, φ.Eval ![z] f ↔ F z
    · exact hFdef (DefinableOver.definable
        (⟨n, φ, f, hf, fun x ↦ (hall x).symm⟩ : DefinableOver (A' α) F))
    · have hex : ∃ z', ¬ (φ.Eval ![z'] f ↔ F z') := not_forall.mp hall
      have hz : ¬ (φ.Eval ![gw ⟨n, φ⟩ f] f ↔ F (gw ⟨n, φ⟩ f)) := hgw ⟨n, φ⟩ f hex
      have hmemz : gw ⟨n, φ⟩ f ∈ A' α := hC₃mem α hα ⟨n, φ⟩ f hf
      exact hz (((hD _).symm).trans (hagree _ hmemz))
  -- The diamond sequence guesses the code of `F` on a stationary set.
  obtain ⟨α, hαS, hαC⟩ :=
    ZFVP.IsStationary.exists_mem_club (hA.stationary_guess {β : OmegaOne | F (R.code β)})
      (ZFVP.IsClub.inter (ZFVP.IsClub.inter hC₁ hC₂) hC₃)
  obtain ⟨⟨hα₁, hα₂⟩, hα₃⟩ := hαC
  have hAα : A α = {β ∈ {β : OmegaOne | F (R.code β)} | β < α} := hαS
  -- The guess at `α` is the trace of `F` on stage `α`.
  have hguessα : R.guess α = {x | x ∈ A' α ∧ F x} := by
    have hcode : A' α = R.code '' {β : OmegaOne | β < α} := hC₁mem α hα₁
    apply Set.Subset.antisymm
    · intro x hx
      rw [hguess α, hAα] at hx
      obtain ⟨β, ⟨hFβ, hβα⟩, rfl⟩ := hx
      exact ⟨by rw [hcode]; exact ⟨β, hβα, rfl⟩, hFβ⟩
    · rintro x ⟨hxA, hxF⟩
      rw [hcode] at hxA
      obtain ⟨β, hβα, rfl⟩ := hxA
      rw [hguess α, hAα]
      exact ⟨β, ⟨hxF, hβα⟩, rfl⟩
  have hmemguess : ∀ x : Ω, x ∈ A' α → (x ∈ R.guess α ↔ F x) := by
    intro x hx
    rw [hguessα]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩
  refine ⟨α, ?_, ?_⟩
  · -- Condition (6): the incompatible partner is already in the stage.
    intro q hq hPq hFq
    exact ⟨gc q, hC₂mem α hα₂ () (fun _ ↦ q) (fun _ ↦ hq), (hgc q hPq hFq).1,
      (hgc q hPq hFq).2⟩
  · -- Condition (5): the trace of `F` is inseparable from its complement.
    have hinsα : Inseparable ↥(R.stage α).carrier (fun x ↦ (x : Ω) ∈ R.guess α)
        (fun x ↦ (x : Ω) ∉ R.guess α) := by
      rintro ⟨X, hX, hVX, hWX⟩
      obtain ⟨D, hDdef, hDX⟩ :=
        @exists_definableOver_of_definable_elementary Ω ↥(R.stage α).carrier _
          (stageSetStructure (R.stage α)) (R.stageEmbedding α) (A' α)
          (fun x ↦ x.2) (fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩) X hX
      refine hno α hα₃ D hDdef ?_
      intro x hx
      have hDx : D x ↔ X ⟨x, hx⟩ := hDX ⟨x, hx⟩
      rw [hDx]
      constructor
      · intro hXx
        by_contra hFx
        exact hWX ⟨x, hx⟩ (fun hmem ↦ hFx ((hmemguess x hx).mp hmem)) hXx
      · intro hFx
        exact hVX ⟨x, hx⟩ ((hmemguess x hx).mpr hFx)
    have hkeep := R.keep α
    have hV : {x : Ω | x ∈ A' α ∧ x ∈ R.guess α} ⊆ (R.stage α).carrier := fun _ hx ↦ hx.1
    have hW : {x : Ω | x ∈ A' α ∧ x ∉ R.guess α} ⊆ (R.stage α).carrier := fun _ hx ↦ hx.1
    have hunion := R.toStageChain.inseparable_union
      {x : Ω | x ∈ A' α ∧ x ∈ R.guess α} {x : Ω | x ∈ A' α ∧ x ∉ R.guess α} α hV hW
      (fun β hβ ↦ hkeep β hβ hinsα)
    refine hunion.congr (fun x ↦ ?_) (fun x ↦ ?_)
    · constructor
      · rintro ⟨hx, hFx⟩
        exact ⟨hx, (hmemguess x hx).mpr hFx⟩
      · rintro ⟨hx, hgx⟩
        exact ⟨hx, (hmemguess x hx).mp hgx⟩
    · constructor
      · rintro ⟨hx, hFx⟩
        exact ⟨hx, fun hgx ↦ hFx ((hmemguess x hx).mp hgx)⟩
      · rintro ⟨hx, hgx⟩
        exact ⟨hx, fun hFx ↦ hgx ((hmemguess x hx).mpr hFx)⟩

end StageRun

end ZFVP
