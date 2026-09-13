import ZFVP.ModelTheory.ClassForcingTowerModel
import ZFVP.SetTheory.EndExtensionCoding

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower

variable (T : DefinableForcingTower V) {G : Set V}
  (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

/-- Once subsets of a bounded-stage set stabilize, its powerset at that stage
is a powerset witness in the class extension. No set-theory axioms are assumed
for the class extension. -/
theorem classModel_powerset_of_subset_stabilization
    {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j)
    (x : (T.boundedContext hG i).Model)
    (hstable : ∀ (k : V) [IsOrdinal k] (hjk : j ⊆ k)
      (z : (T.boundedContext hG k).Model),
      z ⊆ T.boundedInclusion hG (fun a ha ↦ hjk a (hij a ha)) x →
      ∃ w : (T.boundedContext hG j).Model, T.boundedInclusion hG hjk w = z) :
    ∀ z : T.ClassModel hG,
      z ∈ T.fromBoundedStage hG j (℘ (T.boundedInclusion hG hij x)) ↔
        z ⊆ T.fromBoundedStage hG i x := by
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := (T.fromBoundedStage hG j).endExtension _ z hz
    rw [← T.fromBoundedStage_coherent hG hij x]
    exact ((T.fromBoundedStage hG j).subset_iff _ _).mpr (mem_power_iff.mp hw)
  · intro hz
    obtain ⟨l, v, hv⟩ := (T.directedSystem hG).stage_cover z
    change (T.boundedContext hG l.val).Model at v
    change z = T.fromBoundedStage hG l.val v at hv
    let k := j ∪ l.val
    have : IsOrdinal k := ordinal_union_ordinal _ _
    have hjk : j ⊆ k := subset_union_left _ _
    have hlk : l.val ⊆ k := subset_union_right _ _
    have hik : i ⊆ k := fun a ha ↦ hjk a (hij a ha)
    let u := T.boundedInclusion hG hlk v
    have hzu : z = T.fromBoundedStage hG k u :=
      hv.trans (T.fromBoundedStage_coherent hG hlk v).symm
    have hu : u ⊆ T.boundedInclusion hG hik x := by
      apply ((T.fromBoundedStage hG k).subset_iff _ _).mp
      rw [← hzu, T.fromBoundedStage_coherent hG hik x]
      exact hz
    obtain ⟨w, hw⟩ := hstable k hjk u hu
    have hwsub : w ⊆ T.boundedInclusion hG hij x := by
      apply ((T.boundedInclusion hG hjk).subset_iff _ _).mp
      rw [hw, T.boundedInclusion_comp hG hij hjk x]
      exact hu
    have hzw : z = T.fromBoundedStage hG j w := by
      rw [hzu, ← hw]
      exact T.fromBoundedStage_coherent hG hjk w
    rw [hzw]
    exact ((T.fromBoundedStage hG j).mem_iff _ _).mpr (mem_power_iff.mpr hwsub)

end DefinableForcingTower
end ZFVP
