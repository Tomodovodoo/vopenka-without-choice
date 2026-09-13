import ZFVP.SetTheory.MagidorClosureLimitPoint

/-! # The side condition of the `Pi_1` class indexed by closure limit points

`ZFVP.SetTheory.MagidorFailureClassFormula` writes the side condition of the `Pi_1` class of
`ZFVP.SetTheory.DomainTwoMarkerRankClass` with Bagaria's index: `lam` is the least limit ordinal
above the marker `r` at which a whole interval of ordinals fails the small-embedding property.

This module writes the side condition for the other index, the one of
`ZFVP.SetTheory.MagidorClosureLimitPoint`: `lam` is the least limit point of the class of closure
points of the failure function `magidorFailure ρ` above the marker `r`. At such a `lam` one step of
an embedding is enough for the reflection, because the failure stage of any `κ ∈ lam` above `ρ`
stays below `lam`.

As in the failure-limit module every quantifier is bounded by `lam` or by the domain `A`, and the
closure point clauses go through `boundedMagidorClosurePointFormula` rather than the predicate, so
the whole side formula is bounded and in particular `Pi_1`. The relativized quantifiers are
faithful at `A = V_{lam+ω}`: every ordinal the formula quantifies over lies in `lam`, hence in
`V_{lam+ω}`.

The standing hypothesis is `MagidorFailureTotal ρ`, which is what
`eval_boundedMagidorClosurePointFormula` needs; the caller discharges it. Nothing here assumes that
no ordinal is Magidor supercompact.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `x` is a limit ordinal above `ρ` with closure points of the failure function cofinally below
it, with the closure point condition read by its bounded formula at the stage `A`. Free variables:
`ρ`, `x`, `A`. -/
def boundedMagidorClosureLimitPointFormula : SetTheorySemisentence 3 :=
  “ρ x A. !boundedLimitOrdinalFormula x ∧ ρ ∈ x ∧
    ∀ η ∈ x, ∃ d ∈ x, η ∈ d ∧ !boundedMagidorClosurePointFormula ρ d A”

theorem boundedMagidorClosureLimitPointFormula_bounded :
    IsBoundedSetFormula boundedMagidorClosureLimitPointFormula :=
  .and (boundedLimitOrdinalFormula_bounded.subst _)
    (.and (.rel _ _)
      (.all (.bvar 1) (.exs (.bvar 2)
        (.and (.rel _ _) (boundedMagidorClosurePointFormula_bounded.subst _)))))

/-- The side condition of the `Pi_1` class. Free variables: `lam`, `r`, `ρ`, `A`.

`ρ ⊆ r`, the marker `r` lies below `lam`, `lam` is a closure limit point, and no ordinal strictly
between `r` and `lam` is one. -/
def magidorClosureLimitSideFormula : SetTheorySemisentence 4 :=
  “lam r ρ A. !isSubsetOf ρ r ∧ r ∈ lam ∧ !boundedMagidorClosureLimitPointFormula ρ lam A ∧
    (∀ ξ ∈ lam, r ∈ ξ → ¬!boundedMagidorClosureLimitPointFormula ρ ξ A)”

theorem magidorClosureLimitSideFormula_bounded :
    IsBoundedSetFormula magidorClosureLimitSideFormula :=
  .and (isSubsetOf_bounded.subst _)
    (.and (.rel _ _)
      (.and (boundedMagidorClosureLimitPointFormula_bounded.subst _)
        (.all (.bvar 0) (.or (.nrel _ _)
          (boundedMagidorClosureLimitPointFormula_bounded.subst _).neg))))

theorem magidorClosureLimitSideFormula_piOne : IsPiFormula 1 magidorClosureLimitSideFormula :=
  .bounded magidorClosureLimitSideFormula_bounded

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The literal reading of the closure limit point formula, with the closure point subformula left
alone. -/
theorem eval_boundedMagidorClosureLimitPointFormula_components (ρ x A : V) :
    boundedMagidorClosureLimitPointFormula.Evalb ![ρ, x, A] ↔
      IsLimitOrdinal x ∧ ρ ∈ x ∧
        ∀ η ∈ x, ∃ d ∈ x, η ∈ d ∧ boundedMagidorClosurePointFormula.Evalb ![ρ, d, A] := by
  simp [boundedMagidorClosureLimitPointFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

/-- At the stage `V_{lam+ω}` the bounded formula says that `x` is a limit point of the closure
point class. Every closure point the formula quantifies over lies in `x ⊆ lam`, so the closure
point stage lemma applies to each of them. -/
theorem eval_boundedMagidorClosureLimitPointFormula {lam ρ x : V} [IsOrdinal lam]
    (hlim : IsLimitOrdinal lam) (htot : MagidorFailureTotal ρ) (hx : x ⊆ lam) :
    boundedMagidorClosureLimitPointFormula.Evalb ![ρ, x, hierarchy (ordinalAdd lam (ω : V))] ↔
      IsMagidorClosureLimitPoint ρ x := by
  rw [eval_boundedMagidorClosureLimitPointFormula_components]
  unfold IsMagidorClosureLimitPoint
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun η hη ↦ ?_⟩
    obtain ⟨d, hdx, hηd, hd⟩ := h3 η hη
    exact ⟨d, hdx, hηd, (eval_boundedMagidorClosurePointFormula hlim htot (hx d hdx)).mp hd⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun η hη ↦ ?_⟩
    obtain ⟨d, hdx, hηd, hd⟩ := h3 η hη
    exact ⟨d, hdx, hηd, (eval_boundedMagidorClosurePointFormula hlim htot (hx d hdx)).mpr hd⟩

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- The literal reading of the side formula. -/
theorem eval_magidorClosureLimitSideFormula_components (lam r ρ A : V) :
    magidorClosureLimitSideFormula.Evalb ![lam, r, ρ, A] ↔
      ρ ⊆ r ∧ r ∈ lam ∧ boundedMagidorClosureLimitPointFormula.Evalb ![ρ, lam, A] ∧
        ∀ ξ ∈ lam, r ∈ ξ → ¬ boundedMagidorClosureLimitPointFormula.Evalb ![ρ, ξ, A] := by
  simp [magidorClosureLimitSideFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

/-- `lam` is a limit ordinal as soon as the side formula holds of it: the limit clause sits inside
the closure limit point subformula. -/
theorem isLimitOrdinal_of_eval_magidorClosureLimitSideFormula {lam r ρ A : V}
    (h : magidorClosureLimitSideFormula.Evalb ![lam, r, ρ, A]) : IsLimitOrdinal lam :=
  ((eval_boundedMagidorClosureLimitPointFormula_components ρ lam A).mp
    ((eval_magidorClosureLimitSideFormula_components lam r ρ A).mp h).2.2.1).1

/-- At `A = V_{lam+ω}` the side formula says exactly that `ρ ⊆ r` and `lam` is the least limit
point of the closure point class above `r`. -/
theorem eval_magidorClosureLimitSideFormula {lam r ρ : V} [IsOrdinal lam]
    (hlim : IsLimitOrdinal lam) (htot : MagidorFailureTotal ρ) :
    magidorClosureLimitSideFormula.Evalb ![lam, r, ρ, hierarchy (ordinalAdd lam (ω : V))] ↔
      ρ ⊆ r ∧ IsLeastMagidorClosureLimitPoint ρ r lam := by
  rw [eval_magidorClosureLimitSideFormula_components]
  have hself : (lam : V) ⊆ lam := fun z hz ↦ hz
  have hbelow : ∀ ξ ∈ lam, (ξ : V) ⊆ lam := fun ξ hξ ↦ IsOrdinal.toIsTransitive.transitive ξ hξ
  unfold IsLeastMagidorClosureLimitPoint
  constructor
  · rintro ⟨hρr, hrlam, hlamcl, hmin⟩
    refine ⟨hρr, hrlam,
      (eval_boundedMagidorClosureLimitPointFormula hlim htot hself).mp hlamcl, ?_⟩
    intro ξ hξ hrξ hcp
    exact hmin ξ hξ hrξ
      ((eval_boundedMagidorClosureLimitPointFormula hlim htot (hbelow ξ hξ)).mpr hcp)
  · rintro ⟨hρr, hrlam, hlamcl, hmin⟩
    refine ⟨hρr, hrlam,
      (eval_boundedMagidorClosureLimitPointFormula hlim htot hself).mpr hlamcl, ?_⟩
    intro ξ hξ hrξ hcp
    exact hmin ξ hξ hrξ
      ((eval_boundedMagidorClosureLimitPointFormula hlim htot (hbelow ξ hξ)).mp hcp)

/-! ### What the class machine needs -/

/-- The marker `r` determines `lam`. Nothing is assumed about `lam₁` and `lam₂`: limit-ness comes
out of the formula itself. -/
theorem magidorClosureLimitSideFormula_functional {ρ : V} (htot : MagidorFailureTotal ρ) :
    ∀ lam₁ lam₂ r₀ : V,
      magidorClosureLimitSideFormula.Evalb ![lam₁, r₀, ρ, hierarchy (ordinalAdd lam₁ (ω : V))] →
      magidorClosureLimitSideFormula.Evalb ![lam₂, r₀, ρ, hierarchy (ordinalAdd lam₂ (ω : V))] →
      lam₁ = lam₂ := by
  intro lam₁ lam₂ r₀ h₁ h₂
  have hlim₁ : IsLimitOrdinal lam₁ := isLimitOrdinal_of_eval_magidorClosureLimitSideFormula h₁
  have hlim₂ : IsLimitOrdinal lam₂ := isLimitOrdinal_of_eval_magidorClosureLimitSideFormula h₂
  have hord₁ : IsOrdinal lam₁ := hlim₁.1
  have hord₂ : IsOrdinal lam₂ := hlim₂.1
  obtain ⟨-, hL₁⟩ := (eval_magidorClosureLimitSideFormula hlim₁ htot).mp h₁
  obtain ⟨-, hL₂⟩ := (eval_magidorClosureLimitSideFormula hlim₂ htot).mp h₂
  exact isLeastMagidorClosureLimitPoint_functional hL₁ hL₂

/-- The class is unbounded: above every ordinal there are markers satisfying the side condition. -/
theorem magidorClosureLimitSideFormula_unbounded {ρ : V} [IsOrdinal ρ]
    (htot : MagidorFailureTotal ρ) :
    ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧
      magidorClosureLimitSideFormula.Evalb
        ![lam, r, ρ, hierarchy (ordinalAdd lam (ω : V))] := by
  intro γ hγ
  have : IsOrdinal γ := hγ
  obtain ⟨c, hc, hγc, hρc⟩ := exists_ordinal_upper_bound₂ γ ρ
  have : IsOrdinal c := hc
  set r : V := succ c with hrdef
  have hrord : IsOrdinal r := inferInstance
  have hγr : γ ∈ r := by
    rcases IsOrdinal.subset_iff.mp hγc with rfl | h
    · exact mem_succ_self _
    · exact mem_succ_iff.mpr (Or.inr h)
  have hρr : ρ ⊆ r := fun z hz ↦ mem_succ_iff.mpr (Or.inr (hρc z hz))
  obtain ⟨lam, hL⟩ := exists_isLeastMagidorClosureLimitPoint htot r
  have hlim : IsLimitOrdinal lam := hL.2.1.1
  have hord : IsOrdinal lam := hlim.1
  have hrlam : r ∈ lam := hL.1
  have hγlam : γ ∈ lam := IsOrdinal.toIsTransitive.mem_trans hγr hrlam
  have hρlam : ρ ⊆ lam := fun z hz ↦ IsOrdinal.toIsTransitive.transitive r hrlam z (hρr z hz)
  exact ⟨lam, r, hord, hγlam, hρlam, hrlam,
    (eval_magidorClosureLimitSideFormula hlim htot).mpr ⟨hρr, hL⟩⟩

/-- What the main proof reads off a structure in the class. -/
theorem magidorClosureLimitSideFormula_sound {lam r ρ : V} [IsOrdinal lam]
    (htot : MagidorFailureTotal ρ)
    (h : magidorClosureLimitSideFormula.Evalb
      ![lam, r, ρ, hierarchy (ordinalAdd lam (ω : V))]) :
    ρ ⊆ r ∧ IsLimitOrdinal lam ∧ r ∈ lam ∧ IsLeastMagidorClosureLimitPoint ρ r lam := by
  have hlim : IsLimitOrdinal lam := isLimitOrdinal_of_eval_magidorClosureLimitSideFormula h
  obtain ⟨hρr, hL⟩ := (eval_magidorClosureLimitSideFormula hlim htot).mp h
  exact ⟨hρr, hlim, hL.1, hL⟩

end ZFVP
