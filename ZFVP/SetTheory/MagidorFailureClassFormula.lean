import ZFVP.SetTheory.MagidorFailureStages
import ZFVP.SetTheory.MagidorSupercompactBounded
import ZFVP.SetTheory.CnAbsoluteness

/-! # The side condition of the Pi_1 class of Bagaria's Theorem 4.3

Bagaria runs Vopenka's principle for `Pi_1` classes on the structures `⟨V_{λ+2}, ∈, α, λ⟩` where
`λ` is the least limit ordinal above `α` at which no cardinal in the interval is
`<λ`-supercompact. Clauses (5a) and (5b) of his class description are the two clauses below.

The project's class machine (`ZFVP.SetTheory.DomainTwoMarkerRankClass`) puts the structure on
`V_{lam+ω}` and hands the side condition four arguments: the marker `lam`, the marker `r` (which
is Bagaria's `α`), the base parameter `ρ` (which is `succ ξ`, the constants for the ordinals up to
`ξ`) and the domain `A = V_{lam+ω}`. Every quantifier of `magidorFailureSideFormula` is bounded by
`lam` or by `A`, and the supercompactness clauses use the bounded formula
`boundedMagidorSupercompactAtFormula` rather than the predicate, so the whole formula is bounded
and in particular `Pi_1`. That is the point of the module: read literally, Magidor's
small-embedding predicate is `Sigma_1` at best, and it appears here under a negation.

The relativized quantifiers are faithful at `A = V_{lam+ω}`: `r ∈ lam` forces every `ν` with
`ρ ⊆ ν ⊆ r` to lie in `lam`, hence in `V_{lam+ω}`, and every `γ ∈ lam` and every witnessing
embedding lies there too.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `lam` is a limit ordinal, written as "ordinal, nonempty and closed under successor". -/
def boundedLimitOrdinalFormula : SetTheorySemisentence 1 :=
  “lam. !IsOrdinal.dfn lam ∧ ¬!boundedEmptyFormula lam ∧ !boundedSuccessorClosedFormula lam”

theorem boundedLimitOrdinalFormula_bounded : IsBoundedSetFormula boundedLimitOrdinalFormula :=
  .and (isOrdinalFormula_bounded.subst _)
    (.and (boundedEmptyFormula_bounded.subst _).neg
      (boundedSuccessorClosedFormula_bounded.subst _))

/-- The side condition of the `Pi_1` class. Free variables: `lam`, `r`, `ρ`, `A`.

`lam` is a limit ordinal above `r`, `ρ ⊆ r`, and:
(a) every ordinal `ν ∈ A` with `ρ ⊆ ν ⊆ r` fails the small-embedding property at some `γ ∈ lam`
above `ν`;
(b) below every limit `μ ∈ lam` above `r` some ordinal `ν` with `ρ ⊆ ν ⊆ r` has the property at
every `γ ∈ μ` above `ν`. -/
def magidorFailureSideFormula : SetTheorySemisentence 4 :=
  “lam r ρ A. !boundedLimitOrdinalFormula lam ∧ !isSubsetOf ρ r ∧ r ∈ lam ∧
    (∀ ν ∈ A, !IsOrdinal.dfn ν → !isSubsetOf ρ ν → !isSubsetOf ν r →
      ∃ γ ∈ lam, ν ∈ γ ∧ ¬!boundedMagidorSupercompactAtFormula ν γ A) ∧
    (∀ μ ∈ lam, !boundedLimitOrdinalFormula μ → r ∈ μ →
      ∃ ν ∈ A, !IsOrdinal.dfn ν ∧ !isSubsetOf ρ ν ∧ !isSubsetOf ν r ∧
        ∀ γ ∈ μ, ν ∈ γ → !boundedMagidorSupercompactAtFormula ν γ A)”

theorem magidorFailureSideFormula_bounded : IsBoundedSetFormula magidorFailureSideFormula := by
  refine .and (boundedLimitOrdinalFormula_bounded.subst _)
    (.and (isSubsetOf_bounded.subst _) (.and (.rel _ _) (.and ?_ ?_)))
  · refine .all (.bvar 3) (.or (isOrdinalFormula_bounded.subst _).neg
      (.or (isSubsetOf_bounded.subst _).neg (.or (isSubsetOf_bounded.subst _).neg ?_)))
    exact .exs (.bvar 1) (.and (.rel _ _)
      (boundedMagidorSupercompactAtFormula_bounded.subst _).neg)
  · refine .all (.bvar 0) (.or (boundedLimitOrdinalFormula_bounded.subst _).neg
      (.or (.nrel _ _) ?_))
    refine .exs (.bvar 4) (.and (isOrdinalFormula_bounded.subst _)
      (.and (isSubsetOf_bounded.subst _) (.and (isSubsetOf_bounded.subst _) ?_)))
    exact .all (.bvar 1) (.or (.nrel _ _)
      (boundedMagidorSupercompactAtFormula_bounded.subst _))

theorem magidorFailureSideFormula_piOne : IsPiFormula 1 magidorFailureSideFormula :=
  .bounded magidorFailureSideFormula_bounded

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_boundedLimitOrdinalFormula (x : V) :
    boundedLimitOrdinalFormula.Evalb ![x] ↔ IsLimitOrdinal x := by
  have hiff : boundedLimitOrdinalFormula.Evalb ![x] ↔
      IsOrdinal x ∧ ¬ x = ∅ ∧ ∀ y ∈ x, succ y ∈ x := by
    simp [boundedLimitOrdinalFormula]
  rw [hiff]
  constructor
  · rintro ⟨hord, hne, hsucc⟩
    refine ⟨hord, hne, ?_⟩
    rintro ⟨ξ, rfl⟩
    exact mem_irrefl (succ ξ) (hsucc ξ (mem_succ_self ξ))
  · rintro ⟨hord, hne, hlim⟩
    exact ⟨hord, hne, fun y hy ↦ succ_mem_of_isLimitOrdinal' ⟨hord, hne, hlim⟩ hy⟩

/-- The literal reading of the side formula, with the bounded supercompactness formula left
alone. -/
theorem eval_magidorFailureSideFormula_components (lam r ρ A : V) :
    magidorFailureSideFormula.Evalb ![lam, r, ρ, A] ↔
      IsLimitOrdinal lam ∧ ρ ⊆ r ∧ r ∈ lam ∧
        (∀ ν ∈ A, IsOrdinal ν → ρ ⊆ ν → ν ⊆ r →
          ∃ γ ∈ lam, ν ∈ γ ∧ ¬ boundedMagidorSupercompactAtFormula.Evalb ![ν, γ, A]) ∧
        (∀ μ ∈ lam, IsLimitOrdinal μ → r ∈ μ →
          ∃ ν ∈ A, IsOrdinal ν ∧ ρ ⊆ ν ∧ ν ⊆ r ∧
            ∀ γ ∈ μ, ν ∈ γ → boundedMagidorSupercompactAtFormula.Evalb ![ν, γ, A]) := by
  simp [magidorFailureSideFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

/-! ### Ordinal arithmetic of the stage `V_{lam+ω}` -/

/-- A limit ordinal contains `ω`. -/
theorem omega_subset_of_isLimitOrdinal {lam : V} (h : IsLimitOrdinal lam) : (ω : V) ⊆ lam := by
  have : IsOrdinal lam := h.1
  have h0 : (∅ : V) ∈ lam :=
    IsOrdinal.empty_mem_iff_nonempty.mpr (ne_empty_iff_isNonempty.mp h.2.1)
  exact IsInductive.ω_subset ⟨h0, fun y hy ↦ succ_mem_of_isLimitOrdinal' h hy⟩

/-- An ordinal below or equal to `b` is a member of `b + ω`. -/
theorem mem_ordinalAdd_omega_of_subset {a b : V} [IsOrdinal a] [IsOrdinal b] (hab : a ⊆ b) :
    a ∈ ordinalAdd b (ω : V) := by
  rcases IsOrdinal.subset_iff.mp hab with rfl | hlt
  · exact ordinalAdd_omega_gt a
  · exact IsOrdinal.toIsTransitive.mem_trans hlt (ordinalAdd_omega_gt b)

/-- At the stage `V_{lam+ω}` the bounded Magidor formula says what Magidor's predicate says, for
every `γ ∈ lam` and every `ν ∈ γ`. -/
theorem eval_boundedMagidorSupercompactAt_stage {lam ν γ : V} [IsOrdinal lam]
    (hlim : IsLimitOrdinal lam)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (hνγ : ν ∈ γ) (hγlam : γ ∈ lam) :
    boundedMagidorSupercompactAtFormula.Evalb ![ν, γ, hierarchy (ordinalAdd lam (ω : V))] ↔
      IsMagidorSupercompactAt ν γ := by
  have hωlam : (ω : V) ⊆ lam := omega_subset_of_isLimitOrdinal hlim
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  have hωθ : (ω : V) ∈ ordinalAdd lam (ω : V) := mem_ordinalAdd_omega_of_subset hωlam
  have hsuccθ : ∀ ζ ∈ ordinalAdd lam (ω : V), succ ζ ∈ ordinalAdd lam (ω : V) :=
    fun _ hζ ↦ ordinalAdd_omega_succ_closed lam hζ
  have hFθ : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    hierarchy_mono (ordinalAdd_omega_subset_of_successor_closed hωθ hsuccθ) _ hF
  have hγθ : γ ∈ ordinalAdd lam (ω : V) := IsOrdinal.toIsTransitive.mem_trans hγlam hlamθ
  exact eval_boundedMagidorSupercompactAtFormula hωθ hsuccθ hFθ hνγ hγθ

/-! ### The two clauses -/

/-- Failure of the interval condition, with the witness made explicit. -/
theorem exists_of_not_noMagidorSupercompactBetween {ρ r μ : V}
    (h : ¬ NoMagidorSupercompactBetween ρ r μ) :
    ∃ ν : V, IsOrdinal ν ∧ ρ ⊆ ν ∧ ν ⊆ r ∧ IsMagidorSupercompactUpTo ν μ := by
  classical
  unfold NoMagidorSupercompactBetween at h
  push_neg at h
  obtain ⟨ν, hν, hρν, hνr, hup⟩ := h
  exact ⟨ν, hν, hρν, hνr, hup⟩

theorem magidorFailureSide_clauseA_iff {lam r ρ : V} [IsOrdinal lam] (hlim : IsLimitOrdinal lam)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (hrlam : r ∈ lam) :
    (∀ ν ∈ hierarchy (ordinalAdd lam (ω : V)), IsOrdinal ν → ρ ⊆ ν → ν ⊆ r →
        ∃ γ ∈ lam, ν ∈ γ ∧ ¬ boundedMagidorSupercompactAtFormula.Evalb
          ![ν, γ, hierarchy (ordinalAdd lam (ω : V))]) ↔
      NoMagidorSupercompactBetween ρ r lam := by
  classical
  have hrord : IsOrdinal r := IsOrdinal.of_mem hrlam
  have hmem : ∀ ν : V, IsOrdinal ν → ν ⊆ r → ν ∈ lam := by
    intro ν hν hνr
    have : IsOrdinal ν := hν
    rcases IsOrdinal.subset_iff.mp hνr with rfl | hlt
    · exact hrlam
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hrlam
  constructor
  · intro h ν hν hρν hνr hup
    have : IsOrdinal ν := hν
    have hνθ : ν ∈ ordinalAdd lam (ω : V) :=
      IsOrdinal.toIsTransitive.mem_trans (hmem ν hν hνr) (ordinalAdd_omega_gt lam)
    obtain ⟨γ, hγlam, hνγ, hfail⟩ :=
      h ν (ordinal_mem_hierarchy_iff.mpr hνθ) hν hρν hνr
    exact hfail ((eval_boundedMagidorSupercompactAt_stage hlim hF hνγ hγlam).mpr
      (hup γ hγlam (IsOrdinal.of_mem hγlam) hνγ))
  · intro h ν _ hν hρν hνr
    have : IsOrdinal ν := hν
    by_contra hcon
    push_neg at hcon
    exact h ν hν hρν hνr (fun γ hγlam hγ hνγ ↦
      (eval_boundedMagidorSupercompactAt_stage hlim hF hνγ hγlam).mp (hcon γ hγlam hνγ))

theorem magidorFailureSide_clauseB_iff {lam r ρ : V} [IsOrdinal lam] (hlim : IsLimitOrdinal lam)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (hrlam : r ∈ lam) :
    (∀ μ ∈ lam, IsLimitOrdinal μ → r ∈ μ →
        ∃ ν ∈ hierarchy (ordinalAdd lam (ω : V)), IsOrdinal ν ∧ ρ ⊆ ν ∧ ν ⊆ r ∧
          ∀ γ ∈ μ, ν ∈ γ → boundedMagidorSupercompactAtFormula.Evalb
            ![ν, γ, hierarchy (ordinalAdd lam (ω : V))]) ↔
      ∀ μ ∈ lam, IsLimitOrdinal μ → r ∈ μ → ¬ NoMagidorSupercompactBetween ρ r μ := by
  classical
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  constructor
  · intro h μ hμlam hμlim hrμ hno
    obtain ⟨ν, hνθ, hν, hρν, hνr, hup⟩ := h μ hμlam hμlim hrμ
    have : IsOrdinal ν := hν
    refine hno ν hν hρν hνr (fun γ hγμ hγ hνγ ↦ ?_)
    have hγlam : γ ∈ lam := IsOrdinal.toIsTransitive.mem_trans hγμ hμlam
    exact (eval_boundedMagidorSupercompactAt_stage hlim hF hνγ hγlam).mp (hup γ hγμ hνγ)
  · intro h μ hμlam hμlim hrμ
    obtain ⟨ν, hν, hρν, hνr, hup⟩ :=
      exists_of_not_noMagidorSupercompactBetween (h μ hμlam hμlim hrμ)
    have : IsOrdinal ν := hν
    have hrord : IsOrdinal r := IsOrdinal.of_mem hrlam
    have hνlam : ν ∈ lam := by
      rcases IsOrdinal.subset_iff.mp hνr with rfl | hlt
      · exact hrlam
      · exact IsOrdinal.toIsTransitive.mem_trans hlt hrlam
    have hνθ : ν ∈ ordinalAdd lam (ω : V) :=
      IsOrdinal.toIsTransitive.mem_trans hνlam hlamθ
    refine ⟨ν, ordinal_mem_hierarchy_iff.mpr hνθ, hν, hρν, hνr, fun γ hγμ hνγ ↦ ?_⟩
    have hγlam : γ ∈ lam := IsOrdinal.toIsTransitive.mem_trans hγμ hμlam
    exact (eval_boundedMagidorSupercompactAt_stage hlim hF hνγ hγlam).mpr
      (hup γ hγμ (IsOrdinal.of_mem hγlam) hνγ)

/-! ### The identification at the intended fourth argument -/

/-- At `A = V_{lam+ω}` the side formula says exactly that `ρ ⊆ r` and `lam` is the least limit
ordinal above `r` at which the whole interval `ρ ⊆ ν ⊆ r` fails. -/
theorem eval_magidorFailureSideFormula {lam r ρ : V} [IsOrdinal lam]
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V))) :
    magidorFailureSideFormula.Evalb ![lam, r, ρ, hierarchy (ordinalAdd lam (ω : V))] ↔
      ρ ⊆ r ∧ IsLeastMagidorFailureLimit ρ r lam := by
  rw [eval_magidorFailureSideFormula_components]
  constructor
  · rintro ⟨hlim, hρr, hrlam, ha, hb⟩
    exact ⟨hρr, hlim.1, hlim, hrlam,
      (magidorFailureSide_clauseA_iff hlim hF hrlam).mp ha,
      (magidorFailureSide_clauseB_iff hlim hF hrlam).mp hb⟩
  · rintro ⟨hρr, -, hlim, hrlam, hno, hmin⟩
    exact ⟨hlim, hρr, hrlam,
      (magidorFailureSide_clauseA_iff hlim hF hrlam).mpr hno,
      (magidorFailureSide_clauseB_iff hlim hF hrlam).mpr hmin⟩

/-! ### What the class machine needs -/

/-- The marker `r` determines `lam`. Nothing is assumed about `lam₁` and `lam₂`: the limit
ordinal clause is part of the formula. -/
theorem magidorFailureSideFormula_functional {ρ : V}
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V))) :
    ∀ lam₁ lam₂ r₀ : V,
      magidorFailureSideFormula.Evalb ![lam₁, r₀, ρ, hierarchy (ordinalAdd lam₁ (ω : V))] →
      magidorFailureSideFormula.Evalb ![lam₂, r₀, ρ, hierarchy (ordinalAdd lam₂ (ω : V))] →
      lam₁ = lam₂ := by
  intro lam₁ lam₂ r₀ h₁ h₂
  have hlim₁ : IsLimitOrdinal lam₁ :=
    ((eval_magidorFailureSideFormula_components lam₁ r₀ ρ _).mp h₁).1
  have hlim₂ : IsLimitOrdinal lam₂ :=
    ((eval_magidorFailureSideFormula_components lam₂ r₀ ρ _).mp h₂).1
  have hord₁ : IsOrdinal lam₁ := hlim₁.1
  have hord₂ : IsOrdinal lam₂ := hlim₂.1
  obtain ⟨-, hL₁⟩ := (eval_magidorFailureSideFormula hF).mp h₁
  obtain ⟨-, hL₂⟩ := (eval_magidorFailureSideFormula hF).mp h₂
  exact isLeastMagidorFailureLimit_functional hL₁ hL₂

/-- The class is unbounded: above every ordinal there are markers satisfying the side condition,
provided no ordinal above `ξ` is Magidor supercompact. -/
theorem magidorFailureSideFormula_unbounded {ξ : V} [IsOrdinal ξ]
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ) :
    ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ succ ξ ⊆ lam ∧ r ∈ lam ∧
      magidorFailureSideFormula.Evalb ![lam, r, succ ξ, hierarchy (ordinalAdd lam (ω : V))] := by
  intro γ hγ
  obtain ⟨r, lam, -, hξr, hγlam, hrlam, hξlam, -, -, hL⟩ :=
    leastMagidorFailureLimit_unbounded hno γ hγ
  have hord : IsOrdinal lam := hL.1
  exact ⟨lam, r, hord, hγlam, hξlam, hrlam, (eval_magidorFailureSideFormula hF).mpr ⟨hξr, hL⟩⟩

/-- What the main proof reads off a structure in the class. -/
theorem magidorFailureSideFormula_sound {lam r ρ : V} [IsOrdinal lam]
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (h : magidorFailureSideFormula.Evalb ![lam, r, ρ, hierarchy (ordinalAdd lam (ω : V))]) :
    ρ ⊆ r ∧ IsLimitOrdinal lam ∧ r ∈ lam ∧ IsLeastMagidorFailureLimit ρ r lam := by
  obtain ⟨hρr, hL⟩ := (eval_magidorFailureSideFormula hF).mp h
  exact ⟨hρr, hL.2.1, hL.2.2.1, hL⟩

end ZFVP
