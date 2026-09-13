import ZFVP.ModelTheory.ClassForcingTowerStageModels
import ZFVP.ModelTheory.ForcingModelRank
import ZFVP.SetTheory.EndExtensionRank
import ZFVP.SetTheory.InjectionRetraction
import ZFVP.SetTheory.OrdinalDependentChoiceAC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.dcEnumeration_of_choice (A : ForcingContext V)
    (hAC : InternalChoice A.Model) (X : A.Model) :
    ∃ α : V, ∃ _hα : IsOrdinal α, InternalDependentChoiceAt (A.check α) ∧
      ∃ f ∈ X ^ (A.check α), range f = X := by
  rcases eq_empty_or_isNonempty X with rfl | hX
  · refine ⟨∅, inferInstance, ?_, ∅, ?_, ?_⟩
    · rw [A.check_empty]
      exact dependentChoiceAt_zero
    · simp [A.check_empty]
    · simp
  · obtain ⟨β, hβ, hcard⟩ := (wellOrderable_iff_cardLE_ordinal X).mp
      (wellOrderable_of_internalChoice hAC X)
    let := hβ
    obtain ⟨α, hα, rfl⟩ := A.ordinal_eq_check β
    let := hα
    exact ⟨α, hα, dependentChoiceAt_of_internalChoice hAC _, surjection_of_injection hcard hX⟩

theorem DefinableForcingTower.stage_rank_checked (T : DefinableForcingTower V)
    {G : Set V} (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (i : V) [IsOrdinal i] (x : (T.stageContext hG i).Model) :
    ∃ ρ : V, ∃ _hρ : IsOrdinal ρ,
      ∀ (j : V) [IsOrdinal j] (hij : i ⊆ j),
        rank (T.stageInclusion hG hij x) = (T.stageContext hG j).check ρ := by
  obtain ⟨ρ, hρ, hr⟩ := (T.stageContext hG i).ordinal_eq_check (rank x)
  refine ⟨ρ, hρ, ?_⟩
  intro j hj hij
  rw [← (T.stageInclusion hG hij).map_rank, hr, T.stageInclusion_check]

end ZFVP
