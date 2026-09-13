import ZFVP.ModelTheory.WoodinSourceCode
import ZFVP.SetTheory.WoodinSeedRange
import ZFVP.ModelTheory.WoodinRecursionHistory
import ZFVP.ModelTheory.WoodinConstruction
import ZFVP.ModelTheory.WoodinRecursionHistoryInduction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceCardinals_limit {θ K : V} [IsOrdinal θ]
    (hK : IsIterationTable θ K) (hseed : woodinSeedCardinal ⊆ woodinLimitCardinal K) :
    woodinLimitCardinal (woodinSourceCardinals θ K) = woodinLimitCardinal K := by
  let := hK.function
  unfold woodinSourceCardinals woodinLimitCardinal
  rw [woodinInsertSeed_union_range hK.domain_eq]
  apply mem_ext
  intro x
  exact ⟨fun hx ↦ (mem_union_iff.mp hx).elim (hseed x) id,
    fun hx ↦ mem_union_iff.mpr (Or.inr hx)⟩

theorem woodinIterationCardinalPrefix_initial {δ θ : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ (woodinHistoryCodes (woodinIterationHistory θ))
      (woodinHistoryCardinals (woodinIterationHistory θ))) (hzero : (∅ : V) ∈ θ) :
    (woodinIterationCardinalPrefix θ) ‘ ∅ = woodinStageCardinal (woodinInitialStage : V) := by
  rw [woodinIterationCardinalPrefix, h.cardinal_union_value hzero (mem_succ_self ∅),
    woodinIterationHistory_cardinal_value hzero, woodinIterationRec_initial, kpair.π₂_kpair,
    woodinInitialCardinals, forcingFamilyNext_new]

theorem woodinSourceCardinals_prefix_limit {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ)
    (h : IsWoodinIterationHistory δ θ (woodinHistoryCodes (woodinIterationHistory θ))
      (woodinHistoryCardinals (woodinIterationHistory θ))) (hzero : (∅ : V) ∈ θ) :
    woodinLimitCardinal (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) =
      woodinLimitCardinal (woodinIterationCardinalPrefix θ) := by
  apply woodinSourceCardinals_limit h.cardinal_union_table
  have hn := woodinSuccessorStep_preserves_below_supercompact
    woodinSeedStage_stage woodinSeedStage_small hδ
    (by simpa only [woodinSeedStage, woodinStageCardinal_code] using woodinSeedCardinal_lt hδ)
  have hs : woodinSeedCardinal ∈ woodinStageCardinal (woodinInitialStage : V) := by
    simpa only [woodinInitialStage, woodinSeedStage, woodinStageCardinal_code] using hn.2.2.2.1
  let : IsOrdinal (woodinStageCardinal (woodinInitialStage : V)) := hn.2.2.1.1
  have ht : IsIterationTable θ (woodinIterationCardinalPrefix θ) := h.cardinal_union_table
  let : IsFunction (woodinIterationCardinalPrefix θ) := ht.function
  have hr : woodinStageCardinal (woodinInitialStage : V) ∈ range (woodinIterationCardinalPrefix θ) := by
    apply mem_range_iff.mpr
    refine ⟨∅, kpair_mem_iff_value.mpr ⟨ht.domain_eq.symm ▸ hzero, ?_⟩⟩
    exact woodinIterationCardinalPrefix_initial h hzero
  intro x hx
  exact mem_sUnion_iff.mpr ⟨_, hr, IsOrdinal.toIsTransitive.mem_trans hx hs⟩

theorem woodinSourceCardinals_actual_prefix_limit {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ δ) (hzero : (∅ : V) ∈ θ) :
    woodinLimitCardinal (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) =
      woodinLimitCardinal (woodinIterationCardinalPrefix θ) := by
  have hx := woodinIterationExit hδ hAC
  exact woodinSourceCardinals_prefix_limit hδ
    (woodinIterationHistory_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)) hzero

end ZFVP
