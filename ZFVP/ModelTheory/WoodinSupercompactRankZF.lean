import ZFVP.SetTheory.WoodinSupercompactInaccessible
import ZFVP.SetTheory.PiOneRankCriterion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.rankCriterion {δ : V} (hδ : IsWoodinSupercompact δ) :
    IsRankCriterionHeight δ :=
  ⟨hδ.1.1, hδ.omega_lt, fun _ ha ↦ regularCardinal_succ_closed hδ.regular ha,
    fun _ hX _ ↦ hδ.no_rank_cofinalMap hX⟩

theorem IsWoodinSupercompact.internalZFModel {δ : V} (hδ : IsWoodinSupercompact δ) :
    IsInternalZFModel (hierarchy δ) := hδ.rankCriterion.internalZFModel

theorem IsWoodinSupercompact.models_zf {δ : V} [Nonempty (SetDomain (hierarchy δ))]
    (hδ : IsWoodinSupercompact δ) : (SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  hδ.rankCriterion.models_zf

end ZFVP
