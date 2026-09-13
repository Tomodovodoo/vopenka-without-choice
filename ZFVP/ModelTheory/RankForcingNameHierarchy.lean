import ZFVP.ModelTheory.TransitiveZFOrdinalRecursion
import ZFVP.ModelTheory.TransitiveZFForcingOrders
import ZFVP.SetTheory.ForcingNameHierarchy

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_power_val (hs : ∀ β ∈ ξ, succ β ∈ ξ) (A : SetDomain (hierarchy ξ)) :
    (℘ A).val = ℘ A.val := by
  let := hierarchy_transitive ξ
  apply mem_ext
  intro x
  constructor
  · intro hx
    let x' : SetDomain (hierarchy ξ) := ⟨x, (hierarchy_transitive ξ).mem_trans hx (℘ A).property⟩
    exact mem_power_iff.mpr ((TransitiveZF.subset_val_iff (hierarchy ξ) x' A).mp (mem_power_iff.mp hx))
  · intro hx
    have hxU := subset_mem_hierarchy_limit hs A.property (mem_power_iff.mp hx)
    let x' : SetDomain (hierarchy ξ) := ⟨x, hxU⟩
    exact show x' ∈ ℘ A from mem_power_iff.mpr
      ((TransitiveZF.subset_val_iff (hierarchy ξ) x' A).mpr (mem_power_iff.mp hx))

theorem rank_forcingNameHierarchyStep_val (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (P f : SetDomain (hierarchy ξ)) :
    (forcingNameHierarchyStep P f).val = forcingNameHierarchyStep P.val f.val := by
  let := hierarchy_transitive ξ
  unfold forcingNameHierarchyStep
  rw [TransitiveZF.sUnion_val]
  have he := TransitiveZF.repl_val (hierarchy ξ) (range f) (fun X ↦ ℘ (X ×ˢ P)) (by definability)
    (fun X ↦ ℘ (X ×ˢ P.val)) (by definability) (fun X _ ↦ by
      rw [rank_power_val hs, TransitiveZF.prod_val])
  rw [he, TransitiveZF.range_val]

theorem rank_forcingNameHierarchy_val (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (P α : SetDomain (hierarchy ξ)) (hα : IsOrdinal α) :
    (forcingNameHierarchy P α).val = forcingNameHierarchy P.val α.val := by
  let := hierarchy_transitive ξ
  exact TransitiveZF.parameterRecursion_val (hierarchy ξ) forcingNameHierarchyStep forcingNameHierarchyStep_definable
    forcingNameHierarchyStep forcingNameHierarchyStep_definable P α hα (rank_forcingNameHierarchyStep_val hs P)

end ZFVP
