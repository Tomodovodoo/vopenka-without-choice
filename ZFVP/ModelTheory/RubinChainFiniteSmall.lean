import ZFVP.ModelTheory.RubinChainDiamond
import ZFVP.ModelTheory.FiniteStageAmbient
import ZFVP.ModelTheory.SchmerlInfinitaryFiniteSmall

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

/-- The diamond Rubin construction with FinSmall on the same elementary extension. -/
theorem rubinChain_finSmall_of_diamond (hdiamond : DiamondOmegaOne)
    (M : Type u) [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] :
    ∃ (W : Type u) (_ : SetStructure W) (_ : Nonempty W) (_ : W↓[ℒₛₑₜ] ⊧* 𝗭𝗙),
      Nonempty (RubinChain W) ∧ Nonempty (ElementaryMap M W) ∧ Schmerl.FinSmall W := by
  classical
  obtain ⟨A, hA⟩ := hdiamond
  have hΩ : Cardinal.mk (ULift.{u} OmegaOne) = Cardinal.aleph 1 := by
    rw [Cardinal.mk_uLift, mk_omegaOne, Cardinal.lift_aleph, Ordinal.lift_one]
  obtain ⟨inst, R, hcode, hguess, hfinite⟩ :=
    exists_finite_stageRun (M := M) (Ω := ULift.{u} OmegaOne) hΩ Equiv.ulift.symm
      (fun α ↦ (Equiv.ulift.symm : OmegaOne ≃ ULift.{u} OmegaOne) '' A α)
  letI : SetStructure (ULift.{u} OmegaOne) := inst
  have hne : Nonempty (ULift.{u} OmegaOne) := R.nonempty_carrier
  have hzf : (ULift.{u} OmegaOne)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf
  have hgc : ∀ α, R.guess α = R.code '' (A α) := by
    intro α
    rw [hcode, hguess]
  refine ⟨ULift.{u} OmegaOne, inst, hne, hzf, ⟨?_⟩, ⟨R.embedding⟩, R.internallyFinite_members_countable hfinite⟩
  refine R.toStageChain.toRubinChain R.countable
    (fun α γ hαγ P le hP hle hpo hdir ↦ R.upper α γ hαγ P le hP hle hpo hdir) ?_
  intro P le _ _ _ F hmax _ hFdef
  exact R.reflect hA hgc P le F
    (fun q hq hqF ↦ hmax.exists_incompatible q hq hqF) hFdef

/-- Under diamond, the source has size aleph-one, Rubin definability, and FinSmall
simultaneously, with the original countable model embedded elementarily. -/
theorem rubin_finSmall_elementary_extension_of_diamond (hdiamond : DiamondOmegaOne)
    (M : Type u) [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] :
    ∃ (W : Type u) (_ : SetStructure W) (_ : Nonempty W) (_ : W↓[ℒₛₑₜ] ⊧* 𝗭𝗙),
      Cardinal.mk W = Cardinal.aleph 1 ∧ IsRubinDefinable W ∧
      Schmerl.FinSmall W ∧ Nonempty (ElementaryMap M W) := by
  obtain ⟨W, sw, nw, zw, ⟨C⟩, hj, hfin⟩ := rubinChain_finSmall_of_diamond hdiamond M
  exact ⟨W, sw, nw, zw, C.mk_eq_alephOne, C.isRubinDefinable, hfin, hj⟩

end ZFVP
