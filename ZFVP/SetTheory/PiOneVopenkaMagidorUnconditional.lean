import ZFVP.SetTheory.DomainTwoMarkerRankClass
import ZFVP.SetTheory.MagidorClosureLimitClassFormula
import ZFVP.SetTheory.MagidorCriticalClosurePoint
import ZFVP.SetTheory.MagidorClosurePointReflection
import ZFVP.SetTheory.FormulaFamilyRank

/-! # Bagaria's Theorem 4.3(2) at `n = 1`, with no open hypothesis

The `Pi_1` fragment of Vopenka's principle gives a proper class of Magidor supercompact cardinals.
`ZFVP.SetTheory.PiOneVopenkaMagidor` proves the same statement from the extra hypothesis
`MagidorIterationReach`, which packages the step of Magidor's Lemma 3.1 that composes finite
iterates of the embedding. This module proves it outright.

The difference is the index of the `Pi_1` class. Bagaria indexes by the least limit ordinal above
the marker at which a whole interval of ordinals fails the small embedding property; there one step
of the embedding need not reach the failure stage, and the iterates are needed. Here the index is
the least limit point of the class of closure points of the failure function `magidorFailure ρ`
(`ZFVP.SetTheory.MagidorClosureLimitPoint`). At such a `lam` the failure stage of any ordinal of
`lam` above `ρ` stays inside `lam`, and the critical point `κ` of the Vopenka embedding is itself a
closure point, so `magidorFailure ρ κ` lands below `f ‘ κ` after a single step. One step of
reflection then contradicts the failure at that stage.

Kunen's theorem enters through `criticalPoint_isMagidorClosurePoint`: it is what forces the
critical sequence of `f` to climb above the least closure point over an escaping failure stage, and
that is how `κ` is shown to be a closure point at all.

Supercompactness is Magidor's small-embedding predicate `IsMagidorSupercompact`: for every ordinal
`γ` above `κ` there are `lb ∈ κ` and an elementary `e : V_lb → V_γ` sending its critical point to
`κ`. That is the form Bagaria uses. Its equivalence with the normal measure definition of
supercompactness is not formalized in this project.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The `Pi_1` fragment of Vopenka's principle gives a Magidor supercompact cardinal above every
ordinal `ξ` that contains `ω`. No open hypothesis. -/
theorem magidorSupercompact_above_of_pi_one_vopenka (hAC : InternalChoice V)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ)
    {ξ : V} [IsOrdinal ξ] (hωξ : (ω : V) ⊆ ξ) :
    ∃ κ : V, ξ ∈ κ ∧ IsMagidorSupercompact κ := by
  by_contra hcon
  have hno : ∀ κ : V, ξ ∈ κ → ¬ IsMagidorSupercompact κ := fun κ hκ hM ↦ hcon ⟨κ, hκ, hM⟩
  have htot : MagidorFailureTotal (succ ξ : V) := magidorFailureTotal_of_no_supercompact hno
  have hF : (formulaFamily membershipLanguageCode ∅ : V) ∈
      hierarchy (ordinalAdd (ω : V) (ω : V)) := formulaFamily_mem_hierarchy_omega_two
  -- `ω ∈ succ ξ`, the base of the class.
  have hωρ : (ω : V) ∈ succ ξ := by
    rcases IsOrdinal.subset_iff.mp hωξ with he | hlt
    · exact he ▸ mem_succ_self ξ
    · exact mem_succ_iff.mpr (Or.inr hlt)
  obtain ⟨lam, lam', r, r', f, κ, hlamord, hlam'ord, -, hρlam, hrlam, hψ,
      hρlam', hr'lam', hψ', hf, -, -, -, hκ, hρκsub, hκr⟩ :=
    pi_vopenka_domainTwoMarkerRank_embedding (V := V) Nat.one_pos hVP
      magidorClosureLimitSideFormula magidorClosureLimitSideFormula_piOne (succ ξ) hωρ
      (magidorClosureLimitSideFormula_functional htot)
      (magidorClosureLimitSideFormula_unbounded htot)
  have : IsOrdinal lam := hlamord
  have : IsOrdinal lam' := hlam'ord
  obtain ⟨-, hlim, -, hleast⟩ := magidorClosureLimitSideFormula_sound htot hψ
  obtain ⟨-, hlim', -, -⟩ := magidorClosureLimitSideFormula_sound htot hψ'
  have hκord : IsOrdinal κ := hκ.ordinal
  have : IsOrdinal κ := hκord
  -- `ω` lies in `lam` and in `lam'` because the base `succ ξ` does.
  have hωlam : (ω : V) ∈ lam := hρlam _ hωρ
  have hωlam' : (ω : V) ∈ lam' := hρlam' _ hωρ
  have hrord : IsOrdinal r := IsOrdinal.of_mem hrlam
  have : IsOrdinal r := hrord
  -- `κ ⊆ r ∈ lam` puts `κ` in `lam`.
  have hκlam : κ ∈ lam := by
    rcases IsOrdinal.subset_iff.mp hκr with he | hlt
    · exact he ▸ hrlam
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hrlam
  -- The base is strictly below the critical point: it is a successor ordinal, while `κ` is closed
  -- under successors.
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  have hρκ : (succ ξ : V) ∈ κ := by
    rcases IsOrdinal.subset_iff.mp hρκsub with he | hlt
    · have hξκ : ξ ∈ κ := he ▸ mem_succ_self ξ
      have : succ ξ ∈ κ := hκ.succ_closed hf hξκ
      exact absurd (he ▸ this) (mem_irrefl κ)
    · exact hlt
  -- `κ` is the least moved ordinal, so it fixes the base.
  have hfρ : f ‘ (succ ξ : V) = succ ξ := hκ.fixed_below hρκ
  -- The index `lam` is a limit of closure points, hence a closure point itself.
  have hlamlim : IsMagidorClosureLimitPoint (succ ξ : V) lam := hleast.2.1
  have hlamclos : IsMagidorClosurePoint (succ ξ : V) lam := hlamlim.closurePoint
  -- Kunen's theorem makes the critical point a closure point too.
  have hκclos : IsMagidorClosurePoint (succ ξ : V) κ :=
    criticalPoint_isMagidorClosurePoint hAC hlim hωlam hlim' hωlam' hF hf hκ htot hfρ hρκ hκlam
      hlamlim.2.2
  exact false_of_magidorClosurePoint_criticalPoint hlim hωlam hlim' hωlam' hF hf hκ htot hfρ hρκ
    hκlam hlamclos hκclos

/-- The `Pi_1` fragment of Vopenka's principle gives a proper class of Magidor supercompact
cardinals. This is Bagaria's Theorem 4.3(2) for `n = 1`, with no open hypothesis. -/
theorem magidorSupercompact_unbounded_of_pi_one_vopenka (hAC : InternalChoice V)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula 1 φ → VopenkaInstance (V := V) φ) :
    ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsMagidorSupercompact κ := by
  intro α hα
  have : IsOrdinal α := hα
  have hξord : IsOrdinal (α ∪ (ω : V)) := ordinal_union_isOrdinal α (ω : V)
  have : IsOrdinal (α ∪ (ω : V)) := hξord
  have hωξ : (ω : V) ⊆ α ∪ (ω : V) := fun x hx ↦ mem_union_iff.mpr (Or.inr hx)
  have hαξ : α ⊆ α ∪ (ω : V) := fun x hx ↦ mem_union_iff.mpr (Or.inl hx)
  obtain ⟨κ, hκ, hM⟩ :=
    magidorSupercompact_above_of_pi_one_vopenka hAC hVP (ξ := α ∪ (ω : V)) hωξ
  have : IsOrdinal κ := hM.1
  refine ⟨κ, ?_, hM⟩
  rcases IsOrdinal.subset_iff.mp hαξ with he | hlt
  · exact he ▸ hκ
  · exact IsOrdinal.toIsTransitive.mem_trans hlt hκ

end ZFVP
