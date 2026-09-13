import ZFVP.ModelTheory.WoodinSparsePoolRecovery
import ZFVP.ModelTheory.SingletonNormalizedPoolEvaluation
import ZFVP.ModelTheory.WoodinCollapseRowRecovery

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparseFirstCoordinateValues (S : V) : V :=
  repl (nameValue ({∅} : V)) (by definability) (sparseCoordinatePool S (succ (∅ : V)))

instance sparseFirstCoordinateValues_definable : ℒₛₑₜ-function₁[V] sparseFirstCoordinateValues := by
  unfold sparseFirstCoordinateValues
  definability

noncomputable def sparseRecoveredSeed (S : V) : V := collapseRowIndices (sparseFirstCoordinateValues S)

instance sparseRecoveredSeed_definable : ℒₛₑₜ-function₁[V] sparseRecoveredSeed := by
  unfold sparseRecoveredSeed
  definability

variable {Ω θ : V} [IsOrdinal θ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "B" => ({∅} : V)
local notation "T" => (B ×ˢ B)
local notation "c" => woodinPrefixCutoff B T ∅ (woodinSeedCardinal : V)

theorem woodinSparseStageCode_first_coordinate_pool
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    sparseCoordinatePool P (succ (∅ : V)) =
      normalizedNamePool ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ c
        (saturatedWoodinPrefixPosetName ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal c) := by
  have hz : (∅ : V) ∈ succ θ := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset θ))
  have ha : succ (∅ : V) ∈ succ (woodinSourceIndex (∅ : V)) := by
    rw [woodinSourceIndex_zero]
    exact mem_succ_self _
  rw [← woodinSparseStageCode_pool_restriction hΩ hAC hθ hz ha,
    (woodinSparseStageCode_initial).1]
  exact woodinSparseInitial_pool_recovery

theorem woodinSparseStageCode_first_coordinate_values
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    sparseFirstCoordinateValues P = woodinCollapse (woodinSeedCardinal : V) c := by
  unfold sparseFirstCoordinateValues
  rw [woodinSparseStageCode_first_coordinate_pool hΩ hAC hθ]
  obtain ⟨hc, hp, hκ, _⟩ := woodinNormalizationInitial_inputs hΩ
  exact singleton_normalizedWoodinPrefixPool_image hc hp hκ

theorem woodinSparseStageCode_seed_from_carrier
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    sparseRecoveredSeed P = (woodinSeedCardinal : V) := by
  unfold sparseRecoveredSeed
  rw [woodinSparseStageCode_first_coordinate_values hΩ hAC hθ]
  obtain ⟨hc, _, hκ, _⟩ := woodinNormalizationInitial_inputs hΩ
  let := hc.1
  have h1 : (1 : V) ∈ woodinSeedCardinal := woodinSeedCardinal_omega_subset 1 (by simp)
  exact collapseRowIndices_woodinCollapse h1 (hκ _ h1)

end ZFVP
