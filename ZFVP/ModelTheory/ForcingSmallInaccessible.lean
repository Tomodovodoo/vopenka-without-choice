import ZFVP.ModelTheory.ForcingHierarchyCover
import ZFVP.ModelTheory.ForcingSmallCardinals
import ZFVP.SetTheory.ForcingNameHierarchyBound
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Covers of new rank segments reduce cofinal maps to maps on checked sets.
The latter are bounded using the ground input-condition decision graph. -/
theorem check_inaccessible_of_small (A : ForcingContext V) {δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) :
    IsChoicelessInaccessible (A.check δ) := by
  let := hδ.1
  refine ⟨inferInstance, ?_, ?_⟩
  · have hw := (A.check_mem_iff (ω : V) δ).mpr hδ.2.1
    rwa [show A.check ω = (ω : A.Model) from A.checkEmbedding.map_omega] at hw
  intro α hα g hg
  obtain ⟨β, hβ, rfl⟩ := (A.mem_check_iff δ α).mp hα
  let := IsOrdinal.of_mem hβ
  let E := A.hierarchyEvaluation β
  have hE : E ∈ hierarchy (A.check β) ^ A.check (forcingNameHierarchy A.P β) := A.hierarchyEvaluation_function β
  have hc : compose E g ∈ A.check δ ^ A.check (forcingNameHierarchy A.P β) := compose_function hE hg.1
  obtain ⟨ξ, hξ, hb⟩ := A.function_values_bounded_of_small hδ hP
    (forcingNameHierarchy_mem_hierarchy hδ hP hβ) hc
  obtain ⟨y, hy, hξy⟩ := hg.2 (A.check ξ) ((A.check_mem_iff _ _).mpr hξ)
  have hyE : y ∈ range E := (A.hierarchyEvaluation_range β).symm ▸ hy
  obtain ⟨x, hxy⟩ := mem_range_iff.mp hyE
  have hx : x ∈ A.check (forcingNameHierarchy A.P β) := (mem_of_mem_functions hE hxy).1
  have hval : E ‘ x = y := value_eq_of_kpair_mem hxy
  have hb' := hb x hx
  rw [value_compose_of_mem_function hE hg.1 hx, hval] at hb'
  exact mem_irrefl (g ‘ y) (hξy _ hb')

end ForcingContext
end ZFVP
