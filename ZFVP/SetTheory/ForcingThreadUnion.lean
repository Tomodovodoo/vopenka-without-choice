import ZFVP.SetTheory.ForcingInverseLimit
import ZFVP.SetTheory.CodingUniverse
import ZFVP.SetTheory.InaccessibleFunctionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Compatible initial threads assemble by an internal set union. -/
theorem forcingInverseLimit_sUnion {θ P π U B : V}
    (hB : ∀ f ∈ B, f ∈ forcingInverseLimit (domain f) P π U)
    (hord : ∀ f ∈ B, IsOrdinal (domain f))
    (hdom : ∀ f ∈ B, domain f ⊆ θ)
    (hcover : ∀ i ∈ θ, ∃ f ∈ B, i ∈ domain f)
    (hcompat : CompatibleFunctionFamily B) :
    ⋃ˢ B ∈ forcingInverseLimit θ P π U := by
  have hF : ∀ f ∈ B, IsFunction f := fun f hf ↦
    IsFunction.of_mem ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hB f hf)).1
  let := isFunction_sUnion hF hcompat
  have hfun : ⋃ˢ B ∈ U ^ θ := by
    apply mem_function.intro
    · intro z hz
      obtain ⟨f, hf, hzf⟩ := mem_sUnion_iff.mp hz
      have ht := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hB f hf)).1
      obtain ⟨i, hi, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function ht z hzf)
      exact kpair_mem_iff.mpr ⟨hdom f hf i hi, hy⟩
    · intro i hi
      obtain ⟨f, hf, hif⟩ := hcover i hi
      let := hF f hf
      have hp : ⟨i, f ‘ i⟩ₖ ∈ ⋃ˢ B := mem_sUnion_iff.mpr ⟨f, hf, kpair_value_mem hif⟩
      exact ⟨f ‘ i, hp, fun y hy ↦ IsFunction.unique hy hp⟩
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  refine ⟨hfun, ?_, ?_⟩
  · intro i hi
    obtain ⟨f, hf, hif⟩ := hcover i hi
    rw [value_sUnion_of_mem hF hcompat hf hif]
    exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hB f hf)).2.1 i hif
  · intro j hj i hij _hi
    obtain ⟨f, hf, hjf⟩ := hcover j hj
    let := hord f hf
    have hif : i ∈ domain f := IsOrdinal.toIsTransitive.mem_trans hij hjf
    rw [value_sUnion_of_mem hF hcompat hf hjf, value_sUnion_of_mem hF hcompat hf hif]
    exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hB f hf)).2.2 j hjf i hij hif

theorem forcingInverseLimit_mem_hierarchy {θ P π U δ : V} [IsOrdinal δ]
    (hs : ∀ α ∈ δ, succ α ∈ δ) (hθ : θ ∈ hierarchy δ) (hU : U ∈ hierarchy δ) :
    forcingInverseLimit θ P π U ∈ hierarchy δ :=
  subset_mem_hierarchy_limit hs (function_mem_hierarchy_limit hs hθ hU) sep_subset

theorem forcingThreadOrder_mem_hierarchy {θ R C δ : V} [IsOrdinal δ]
    (hs : ∀ α ∈ δ, succ α ∈ δ) (hC : C ∈ hierarchy δ) :
    forcingThreadOrder θ R C ∈ hierarchy δ :=
  subset_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs hC hC) sep_subset

/-- A short internal family of small coordinate posets bounds its full inverse limit. -/
theorem forcingInverseLimit_small_family {θ P R π δ : V}
    (hδ : IsChoicelessInaccessible δ) (hθ : θ ∈ hierarchy δ)
    (hP : P ∈ hierarchy δ ^ θ) :
    forcingInverseLimit θ P π (⋃ˢ range P) ∈ hierarchy δ ∧
      forcingThreadOrder θ R (forcingInverseLimit θ P π (⋃ˢ range P)) ∈ hierarchy δ := by
  let := hδ.1
  have hs := hδ.rankCriterion.2.2.1
  have hr : range P ∈ hierarchy δ := hδ.rankCriterion.2.2.2.range_mem hs hθ hP
  have hc := forcingInverseLimit_mem_hierarchy (P := P) (π := π) hs hθ
    (sUnion_mem_hierarchy_limit hs hr)
  exact ⟨hc, forcingThreadOrder_mem_hierarchy hs hc⟩

end ZFVP
