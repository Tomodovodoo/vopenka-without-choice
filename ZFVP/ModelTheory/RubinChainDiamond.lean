import ZFVP.ModelTheory.StageRunConstruction
import ZFVP.ModelTheory.StageRunUpper
import ZFVP.ModelTheory.StageRunReflect
import ZFVP.ModelTheory.RubinChainCountabilityEssential

/-! # Stage 1 of Enayat's Appendix, assembled

This file discharges `ZFVP.RubinChainUnderDiamond`, the hypothesis under which
`ZFVP.ModelTheory.RubinChainCountabilityEssential` runs the chain from Enayat's Theorem 5.17 to
the model-theoretic half of the paper's countability proposition. The three theorems of that file
that carried it as a hypothesis are restated here without it.

The proof is an assembly of parts proved elsewhere. Over a countable model `M` of ZF, take the
carrier `Ω := ULift OmegaOne`, of cardinality `ℵ₁`, with `code := Equiv.ulift.symm` reading an
index of `ω₁` as a point of `Ω`, and take a diamond sequence `A` from the `◊` hypothesis with the
guess `fun α ↦ code '' (A α)`. `ZFVP.exists_stageRun` runs the `ω₁`-length recursion and returns a
membership structure on `Ω` and a `ZFVP.StageRun M Ω` with that code and that guess.
`ZFVP.StageChain.toRubinChain` turns its chain data into a `ZFVP.RubinChain`, with
`ZFVP.StageRun.upper` for clause (2) and `ZFVP.StageRun.reflect` for clauses (4) and (5); the
incompatibility hypothesis of the latter comes from
`ZFVP.IsMaximallyCompatibleOn.exists_incompatible`. `ZFVP.StageRun.embedding` puts `M`
elementarily inside `Ω`, which models ZF by `ZFVP.StageRun.models_zf`.

## What is proved and what is not

* Stage 1 of the Appendix is now a theorem, not a hypothesis: `ZFVP.rubinChainUnderDiamond`.
* `◊` is still a hypothesis of every statement below, and of everything downstream. Schmerl's
  absoluteness argument, which removes it, is not formalized anywhere in this development.
* Clause (b) of the corrected Definition 5.13 is stated for maximally compatible filters, not for
  inclusion maximal ones. That is Enayat's footnote 30 reading of clause (c) of his 5.10, and it
  is the reading his Appendix argument uses; `ZFVP.ModelTheory.MaximallyCompatibleFilters` shows
  the two readings come apart in a general poset, so the choice is not cosmetic.

There is no `sorry` and no new axiom here.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-- Stage 1 of Enayat's Appendix. Under `◊`, every countable model of ZF has an elementary
extension carrying a `ZFVP.RubinChain`: an increasing continuous `ω₁`-chain of countable
elementary submodels covering the extension, closed under upper bounds for definable directed
posets and reflecting every undefinable maximally compatible filter with a cofinal `ω₁`-chain.

The chain is the run of `ZFVP.exists_stageRun` on the carrier `ULift OmegaOne` with the guess read
off a diamond sequence; the two clauses that mention definability are `ZFVP.StageRun.upper` and
`ZFVP.StageRun.reflect`. -/
theorem rubinChainUnderDiamond : RubinChainUnderDiamond.{u} := by
  classical
  intro hdiamond M _ _ _ _
  obtain ⟨A, hA⟩ := hdiamond
  have hΩ : Cardinal.mk (ULift.{u} OmegaOne) = Cardinal.aleph 1 := by
    rw [Cardinal.mk_uLift, mk_omegaOne, Cardinal.lift_aleph, Ordinal.lift_one]
  obtain ⟨inst, R, hcode, hguess⟩ :=
    exists_stageRun (M := M) (Ω := ULift.{u} OmegaOne) hΩ Equiv.ulift.symm
      (fun α ↦ (Equiv.ulift.symm : OmegaOne ≃ ULift.{u} OmegaOne) '' A α)
  letI : SetStructure (ULift.{u} OmegaOne) := inst
  have hne : Nonempty (ULift.{u} OmegaOne) := R.nonempty_carrier
  have hzf : (ULift.{u} OmegaOne)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf
  have hgc : ∀ α, R.guess α = R.code '' (A α) := by
    intro α
    rw [hcode, hguess]
  refine ⟨ULift.{u} OmegaOne, inst, hne, hzf, ⟨?_⟩, ⟨R.embedding⟩⟩
  refine R.toStageChain.toRubinChain R.countable
    (fun α γ hαγ P le hP hle hpo hdir ↦ R.upper α γ hαγ P le hP hle hpo hdir) ?_
  intro P le _ _ _ F hmax _ hFdef
  exact R.reflect hA hgc P le F
    (fun q hq hqF ↦ hmax.exists_incompatible q hq hqF) hFdef

/-- Enayat's Theorem 5.17 under `◊`: every countable model of ZF has a weakly Rubin elementary
extension of cardinality `ℵ₁`. Schmerl's argument removing `◊` is not formalized. -/
theorem rubinShelahSchmerl_of_diamond' (hdiamond : DiamondOmegaOne) : RubinShelahSchmerl.{u} :=
  rubinShelahSchmerl_of_rubinChain rubinChainUnderDiamond hdiamond

/-- Under `◊`, a countable model of ZF has an elementary extension of cardinality `ℵ₁` with no
proper end extension to a model of ZF. -/
theorem exists_zf_dead_end_of_countable_of_diamond' (hdiamond : DiamondOmegaOne) (M : Type u)
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] :
    Nonempty (AlephOneDeadEndExtension M) :=
  exists_zf_dead_end_of_countable_of_rubinChain rubinChainUnderDiamond hdiamond M

/-- The model-theoretic half of the paper's proposition that countability is essential, under `◊`.
From a countable model of ZF satisfying every instance of the Vopenka scheme and failing internal
choice, we get a model of cardinality `ℵ₁` with the same two properties and with no proper end
extension to a model of ZF. -/
theorem countability_essential_of_diamond' (hdiamond : DiamondOmegaOne) (M : Type u)
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := M) φ)
    (hAC : ¬ InternalChoice M) :
    ∃ E : AlephOneDeadEndExtension M,
      (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := E.Model) φ) ∧
        ¬ InternalChoice E.Model :=
  countability_essential_of_rubinChain rubinChainUnderDiamond hdiamond M hVP hAC

end ZFVP
