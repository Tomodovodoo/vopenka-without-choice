import ZFVP.SetTheory.ForcingSectionThread
import ZFVP.SetTheory.ForcingThreadMaps
import ZFVP.ModelTheory.ForcingProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Coordinate projections from the direct limit have exact stronger lifts. -/
theorem forcingDirectLimit_coordinate_projection {θ P R π E U i : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hi : i ∈ θ)
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hπ : ∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k →
      IsForcingProjection (P ‘ j) (R ‘ j) (P ‘ k) (R ‘ k) (π ‘ ⟨j, k⟩ₖ))
    (hE : ∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k → ∀ p ∈ P ‘ j, ∀ q ∈ P ‘ j,
      ⟨p, q⟩ₖ ∈ R ‘ j → ⟨(E ‘ ⟨j, k⟩ₖ) ‘ p, (E ‘ ⟨j, k⟩ₖ) ‘ q⟩ₖ ∈ R ‘ k) :
    IsForcingProjection (P ‘ i) (R ‘ i) (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
      (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i) := by
  have hmem : ∀ f ∈ forcingDirectLimit θ P π E U, f ∈ forcingInverseLimit θ P π U :=
    forcingDirectLimit_subset _ _ _ _ _
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun f hf ↦
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hmem f hf)).2.1 i hi), ?_, ?_⟩
  · intro f hf g hg hfg
    rw [forcingThreadCoordinate_value hf, forcingThreadCoordinate_value hg]
    exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hfg).2.2 i hi
  · intro f hf p hp hpf
    rw [forcingThreadCoordinate_value hf] at hpf
    obtain ⟨k, hk, hik⟩ := forcingDirectLimit_cofinal_support h hf hi
    have hf' := hmem f hf
    have hfk := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf').2.1 k hk.1
    have hproj := forcingInverseLimit_project_subset h hf' hi hk.1 hik
    obtain ⟨q, hq, hqf, hqp⟩ := (hπ i hi k hk.1 hik).lift _ hfk p hp (hproj.symm ▸ hpf)
    let g := forcingSectionThread θ π E k q
    have hg : g ∈ forcingDirectLimit θ P π E U := forcingSectionThread_mem h hk.1 hq hU
    have hg' := hmem g hg
    have hgk : g ‘ k = q := by
      rw [forcingSectionThread_value hk.1, forcingSectionValue_self h hk.1 hq]
    refine ⟨g, hg, ?_, ?_⟩
    · apply forcingThreadOrder_of_support hg' hf' (forcingSectionThread_support h hk.1 hq) hk
      · intro j hj a ha b hb hab
        let := IsOrdinal.of_mem hk.1
        exact (hπ j (IsOrdinal.toIsTransitive.mem_trans hj hk.1) k hk.1
          (IsOrdinal.toIsTransitive.transitive _ hj)).monotone a ha b hb hab
      · exact hE k hk.1
      · rwa [hgk]
    · rw [forcingThreadCoordinate_value hg,
        ← forcingInverseLimit_project_subset h hg' hi hk.1 hik, hgk, hqp]

end ZFVP
