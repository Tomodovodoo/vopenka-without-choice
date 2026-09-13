import ZFVP.ModelTheory.ClassForcingTowerSubsetStabilization
import ZFVP.SetTheory.EndExtensionWellOrdering
import ZFVP.SetTheory.WellOrderedSurjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower
variable (T : DefinableForcingTower V) {G : Set V}
  (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

theorem classModel_choice_of_enumerations [(T.ClassModel hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (henum : T.StageSetsHaveDCEnumerations hG) : InternalChoice (T.ClassModel hG) := by
  apply internalChoice_of_all_wellOrderable
  intro x
  obtain ⟨i, a, hx⟩ := (T.directedSystem hG).stage_cover x
  change (T.boundedContext hG i.val).Model at a
  change x = T.fromBoundedStage hG i.val a at hx
  let xi := (T.stageBoundedEquiv hG i.val).symm a
  obtain ⟨j, hj, hij, α, hα, _, e, he, hr⟩ := henum i.val xi
  let := hj
  let := hα
  have hw : IsWellOrderable (T.stageInclusion hG hij xi) :=
    wellOrderable_of_surjective_function (ordinal_wellOrderable _) he hr
  have hbw := (T.stageToBounded hG j).map_wellOrderable hw
  have hcw := (T.fromBoundedStage hG j).map_wellOrderable hbw
  change IsWellOrderable (T.fromBoundedStage hG j
    (T.stageBoundedEquiv hG j (T.stageInclusion hG hij xi))) at hcw
  rw [← T.stageBoundedEquiv_commutes hG hij, T.fromBoundedStage_coherent hG hij] at hcw
  simpa only [xi, Equiv.apply_symm_apply, ← hx] using hcw

theorem classModel_models_zfc_of_enumerations [Countable V] (hT : T.IsPretame)
    (henum : T.StageSetsHaveDCEnumerations hG)
    (hclosed : ∀ (j k : V) [IsOrdinal j] [IsOrdinal k], j ⊆ k →
      ∀ (α : V) [IsOrdinal α], InternalDependentChoiceAt ((T.stageContext hG j).check α) →
      IsForcingClosedThrough ((T.stageContext hG j).projectionQuotient (T.P k) (T.projection j k))
        (forcingSeparativeOrder ((T.stageContext hG j).projectionQuotient (T.P k) (T.projection j k))
          ((T.stageContext hG j).projectionQuotientOrder (T.P k) (T.R k) (T.projection j k)))
        ((T.stageContext hG j).check α)) : (T.ClassModel hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  let := T.classModel_models_zf hG hT (T.subsetsStabilize_of_enumerations hG henum hclosed)
  let := models_ac_of_internalChoice (T.classModel_choice_of_enumerations hG henum)
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact Theory.models (T.ClassModel hG) 𝗭𝗙 hφ
  · exact Theory.models (T.ClassModel hG) 𝗔𝗖 hφ

end DefinableForcingTower
end ZFVP
