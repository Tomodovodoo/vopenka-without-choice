import ZFVP.ModelTheory.ForcingHierarchyEvaluation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def hierarchyEvaluation (α : V) [IsOrdinal α] : A.Model :=
  A.evaluationGraph (forcingNameHierarchy A.P α) (forcingNameHierarchy_names A.P α)

instance hierarchyEvaluation_isFunction (α : V) [IsOrdinal α] : IsFunction (A.hierarchyEvaluation α) :=
  A.evaluationGraph_isFunction _ _

theorem hierarchyEvaluation_range (α : V) [IsOrdinal α] :
    range (A.hierarchyEvaluation α) = hierarchy (A.check α) := by
  rw [← A.hierarchyName_value α]
  apply mem_ext
  intro x
  rw [mem_range_iff, A.mem_hierarchyName_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨σ, hσ, _hy, hx⟩ := (A.pair_mem_evaluationGraph_iff _ _ y x).mp hy
    exact ⟨⟨σ, forcingNameHierarchy_names A.P α σ hσ⟩, hσ, hx⟩
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨A.check τ.val, ?_⟩
    exact (A.pair_mem_evaluationGraph_iff _ _ _ _).mpr ⟨τ.val, hτ, rfl, rfl⟩

theorem hierarchyEvaluation_function (α : V) [IsOrdinal α] :
    A.hierarchyEvaluation α ∈ hierarchy (A.check α) ^ A.check (forcingNameHierarchy A.P α) := by
  have h := A.evaluationGraph_mem_function (forcingNameHierarchy A.P α) (forcingNameHierarchy_names A.P α)
  change A.hierarchyEvaluation α ∈ range (A.hierarchyEvaluation α) ^ A.check (forcingNameHierarchy A.P α) at h
  rwa [A.hierarchyEvaluation_range] at h

end ForcingContext
end ZFVP
