import ZFVP.ModelTheory.WoodinSparseLiftRow
import ZFVP.SetTheory.SparseSpliceUnion
import ZFVP.ModelTheory.ForcingThreadSpliceTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ i f p U : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "m" => woodinRecodingMaps (woodinSparseRecodingHistory θ)

theorem woodinSparseThreadSplice_union
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (ih : ∀ j ∈ θ, IsWoodinSparseLiftRow j)
    (hf : f ∈ forcingInverseLimit θ (forcingCodeP N) (forcingCodeπ N) U)
    (hi : i ∈ θ) (hp : p ∈ (forcingCodeP N) ‘ i)
    (hle : ⟨p, f ‘ i⟩ₖ ∈ (forcingCodeR N) ‘ i) :
    ⋃ˢ range (forcingThreadAction θ m (forcingThreadSplice θ (forcingCodeπ N) (forcingCodeL N) f i p)) =
      sparsePrefixReplace (succ (woodinSourceIndex i)) (⋃ˢ range (forcingThreadAction θ m f))
        ((woodinSparseStageMap i) ‘ p) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hi
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  have hv := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1
  have hpI : p ∈ (forcingCodeP (woodinNormalizedStageCode i)) ‘ i := by
    rwa [woodinNormalizedPrefix_stage_carrier hΩ hAC hθ hi (mem_succ_self i)] at hp
  let F := forcingThreadAction θ m f
  let G := forcingThreadAction θ m (forcingThreadSplice θ (forcingCodeπ N) (forcingCodeL N) f i p)
  have hF : IsFunction F := by unfold F forcingThreadAction; infer_instance
  have hG : IsFunction G := by unfold G forcingThreadAction; infer_instance
  let := hF
  let := hG
  have hFd : domain F = θ := by unfold F forcingThreadAction; exact domain_definableGraph _ _ _
  have hGd : domain G = θ := by unfold G forcingThreadAction; exact domain_definableGraph _ _ _
  apply sparsePrefixReplace_sUnion_range hFd hGd hi
  · intro j hj hji
    let := IsOrdinal.of_mem hj
    have hjsub : j ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ (hθ j hj)
    have hfj : f ‘ j ∈ (forcingCodeP (woodinNormalizedStageCode j)) ‘ j := by
      rw [← woodinNormalizedPrefix_stage_carrier hΩ hAC hθ hj (mem_succ_self j)]
      exact hv j hj
    have hsp := woodinSparseStageMap_sparse hΩ hAC hjsub hfj
    have hb : succ (woodinSourceIndex j) ⊆ succ (woodinSourceIndex i) := by
      simpa only [woodinSparseBounds_value hj, woodinSparseBounds_value hi] using woodinSparseBounds_mono hji hi
    constructor
    · simpa only [F, forcingThreadAction_value hj, woodinSparseStageMap_history hj] using subset_trans hsp.2.1 hb
    · have he := (woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)).2.2.2.1 j hji p hpI
      change ((woodinSparseStageMap i) ‘ p) ↾ (succ (woodinSourceIndex j)) =
        (woodinSparseStageMap j) ‘ (((forcingCodeπ (woodinNormalizedStageCode i)) ‘ ⟨j, i⟩ₖ) ‘ p) at he
      have hGval : G ‘ j = ((woodinSparseStageMap i) ‘ p) ↾ (succ (woodinSourceIndex j)) := by
        simp only [G, forcingThreadAction_value hj, forcingThreadSplice_value hj,
          forcingSpliceValue, ite_eq_left hji, woodinSparseStageMap_history hj,
          woodinNormalizedPrefix_stage_projection hΩ hAC hθ hi (mem_succ_iff.mpr (Or.inr hji))]
        exact he.symm
      rw [hGval]
      exact restrict_subset _ _
  · intro j hj hij
    let := IsOrdinal.of_mem hj
    have hij' : i ∈ succ j := by
      rcases IsOrdinal.subset_iff.mp hij with rfl | hij
      · exact mem_succ_self _
      · exact mem_succ_iff.mpr (Or.inr hij)
    have hji : j ∉ i := fun hji ↦ mem_irrefl j (hij j hji)
    have hfj : f ‘ j ∈ (forcingCodeP (woodinNormalizedStageCode j)) ‘ j := by
      rw [← woodinNormalizedPrefix_stage_carrier hΩ hAC hθ hj (mem_succ_self j)]
      exact hv j hj
    have hpj : p ∈ (forcingCodeP (woodinNormalizedStageCode j)) ‘ i := by
      rwa [woodinNormalizedPrefix_stage_carrier hΩ hAC hθ hj hij'] at hp
    have hlej : ⟨p, ((forcingCodeπ (woodinNormalizedStageCode j)) ‘ ⟨i, j⟩ₖ) ‘ (f ‘ j)⟩ₖ ∈
        (forcingCodeR (woodinNormalizedStageCode j)) ‘ i := by
      rw [← woodinNormalizedPrefix_stage_projection hΩ hAC hθ hj hij',
        ← woodinNormalizedPrefix_stage_order hΩ hAC hθ hj hij',
        forcingInverseLimit_project_subset hs.system.split hf hi hj hij]
      exact hle
    have he := ih j hj i hij' (f ‘ j) hfj p hpj hlej
    simpa only [G, F, forcingThreadAction_value hj, forcingThreadSplice_value hj,
      forcingSpliceValue, ite_eq_right hji, woodinSparseStageMap_history hj,
      woodinNormalizedPrefix_stage_lift hΩ hAC hθ hj hij'] using he

end ZFVP
