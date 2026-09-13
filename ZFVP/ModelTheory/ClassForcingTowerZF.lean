import ZFVP.ModelTheory.ClassForcingTowerBasicAxioms
import ZFVP.ModelTheory.ClassForcingTowerPowerset
import ZFVP.ModelTheory.ClassForcingSeparation
import ZFVP.ModelTheory.ClassForcingReplacement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V) {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

/-- Every bounded-stage set eventually acquires all of its subsets in the tower.
The actual iteration must prove this preservation property. -/
def SubsetsStabilize : Prop := ∀ (i : V) [IsOrdinal i]
    (x : (T.boundedContext hG i).Model),
    ∃ j : V, ∃ hj : IsOrdinal j, ∃ hij : i ⊆ j,
      ∀ (k : V) [IsOrdinal k] (hjk : j ⊆ k)
        (z : (T.boundedContext hG k).Model),
        z ⊆ T.boundedInclusion hG (fun a ha ↦ hjk a (hij a ha)) x →
        ∃ w : @ForcingContext.Model V _ _ _ (T.boundedContext hG j),
          T.boundedInclusion hG hjk w = z

theorem classModel_power (hstable : T.SubsetsStabilize hG) (x : T.ClassModel hG) :
    ∃ b : T.ClassModel hG, ∀ z, z ∈ b ↔ z ⊆ x := by
  obtain ⟨i, a, hx⟩ := (T.directedSystem hG).stage_cover x
  change (T.boundedContext hG i.val).Model at a
  change x = T.fromBoundedStage hG i.val a at hx
  obtain ⟨j, hj, hij, hs⟩ := hstable i.val a
  have := hj
  refine ⟨T.fromBoundedStage hG j (℘ (T.boundedInclusion hG hij a)), ?_⟩
  rw [hx]
  exact T.classModel_powerset_of_subset_stabilization hG hij a hs

theorem classModel_models_power (hstable : T.SubsetsStabilize hG) :
    (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ Axiom.power := by
  simp [models_iff, Axiom.power, isSubsetOf]
  exact T.classModel_power hG hstable

/-- The forcing and preservation lemmas supply every ZF axiom in the class
extension. Neither hypothesis asserts ZF or a schema in that extension. -/
theorem classModel_models_zf [Countable V] (hT : T.IsPretame)
    (hstable : T.SubsetsStabilize hG) : (T.ClassModel hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | axiom_of_equality φ hφ => exact Theory.models (T.ClassModel hG) (𝗘𝗤 ℒₛₑₜ) hφ
  | axiom_of_empty_set => exact T.classModel_models_empty hG
  | axiom_of_extentionality => exact T.classModel_models_extensionality hG
  | axiom_of_pairing => exact T.classModel_models_pairing hG
  | axiom_of_union => exact T.classModel_models_union hG
  | axiom_of_power_set => exact T.classModel_models_power hG hstable
  | axiom_of_infinity => exact T.classModel_models_infinity hG
  | axiom_of_foundation => exact T.classModel_models_foundation hG
  | axiom_of_separation φ => exact T.classModel_models_separation hT hG φ
  | axiom_of_replacement φ => exact T.classModel_models_replacement hT hG φ

end DefinableForcingTower
end ZFVP
