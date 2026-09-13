import ZFVP.SetTheory.ForcingSectionMaps
import ZFVP.SetTheory.ForcingThreadUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingDirectLimit_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingDirectLimit (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun C θ P π E U : V ↦ ∀ f,
    f ∈ C ↔ f ∈ U ^ θ ∧ (∀ i ∈ θ, f ‘ i ∈ P ‘ i) ∧
      IsCoherentThread θ π f ∧ ∃ k, IsThreadSupport θ E f k) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingDirectLimit (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [forcingDirectLimit, forcingInverseLimit, mem_sep_iff, and_assoc]

instance forcingSectionThread_uniform_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingSectionThread (V := V)) := by
  classical
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun f θ π E k p : V ↦ ∀ z, z ∈ f ↔ ∃ i ∈ θ,
    (i ∈ k ∧ z = ⟨i, (π ‘ ⟨i, k⟩ₖ) ‘ p⟩ₖ) ∨
    (i ∉ k ∧ z = ⟨i, (E ‘ ⟨k, i⟩ₖ) ‘ p⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingSectionThread (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  apply forall_congr'
  intro z
  rw [forcingSectionThread, mem_definableGraph_iff]
  apply iff_congr Iff.rfl
  apply exists_congr
  intro i
  by_cases hi : i ∈ v 4 <;> simp [forcingSectionValue, hi]

theorem forcingDirectLimit_mem_hierarchy {θ P π E U δ : V} [IsOrdinal δ]
    (hs : ∀ α ∈ δ, succ α ∈ δ) (hθ : θ ∈ hierarchy δ) (hU : U ∈ hierarchy δ) :
    forcingDirectLimit θ P π E U ∈ hierarchy δ :=
  subset_mem_hierarchy_limit hs (forcingInverseLimit_mem_hierarchy hs hθ hU) sep_subset

theorem forcingDirectLimit_small_family {θ P R π E δ : V}
    (hδ : IsChoicelessInaccessible δ) (hθ : θ ∈ hierarchy δ)
    (hP : P ∈ hierarchy δ ^ θ) :
    forcingDirectLimit θ P π E (⋃ˢ range P) ∈ hierarchy δ ∧
      forcingThreadOrder θ R (forcingDirectLimit θ P π E (⋃ˢ range P)) ∈ hierarchy δ := by
  let := hδ.1
  have hs := hδ.rankCriterion.2.2.1
  have hc := subset_mem_hierarchy_limit hs (forcingInverseLimit_small_family
    (R := R) (π := π) hδ hθ hP).1 (forcingDirectLimit_subset θ P π E (⋃ˢ range P))
  exact ⟨hc, forcingThreadOrder_mem_hierarchy hs hc⟩

theorem forcingThreadSection_mem_hierarchy {θ P π E U k δ : V} [IsOrdinal θ] [IsOrdinal δ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hs : ∀ α ∈ δ, succ α ∈ δ) (hθ : θ ∈ hierarchy δ) (hUδ : U ∈ hierarchy δ)
    (hPk : P ‘ k ∈ hierarchy δ) :
    forcingThreadSection θ P π E k ∈ hierarchy δ := by
  exact (hierarchy_transitive δ).mem_trans (forcingThreadSection_maps h hk hU)
    (function_mem_hierarchy_limit hs hPk (forcingDirectLimit_mem_hierarchy hs hθ hUδ))

end ZFVP
