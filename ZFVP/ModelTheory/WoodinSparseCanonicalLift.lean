import ZFVP.ModelTheory.WoodinSparseLiftConstruction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "C" => woodinSparseStageCode θ
local notation "N" => woodinNormalizedStageCode θ

theorem woodinSparseStageCode_lift {i q b : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ succ θ) (hq : q ∈ (forcingCodeP C) ‘ θ) (hb : b ∈ (forcingCodeP C) ‘ i)
    (hle : ⟨b, ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ q⟩ₖ ∈ (forcingCodeR C) ‘ i) :
    ((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨q, b⟩ₖ = sparsePrefixReplace (succ (woodinSourceIndex i)) q b := by
  have hm := woodinSparseStageCode_family hΩ hAC hθ
  have hN := (woodinNormalizedStage_through_endpoint hΩ hAC hθ).1
  have ht := mem_succ_self θ
  have hij : i ⊆ θ := by
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code] at hq hb
  obtain ⟨z, hz, rfl⟩ := (hm θ ht).surjective q hq
  obtain ⟨p, hp, rfl⟩ := (hm i hi).surjective b hb
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeR_code, forcingCodeπ_code] at hle
  rw [forcingRecodedProjections_image hN hm hi ht hij hz,
    ← (hm i hi).2.2.2 p hp _ (hN.system.split.projMaps i hi θ ht hij z hz)] at hle
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeL_code]
  rw [forcingRecodedLifts_image hm hi ht hz hp]
  simp only [woodinSparseStageMap_history hi, woodinSparseStageMap_history ht]
  exact woodinSparseLiftRow_correct_le hΩ hAC hθ i hi z hz p hp hle

theorem woodinSparseStageCode_replace_laws {i q b : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ θ) (hq : q ∈ (forcingCodeP C) ‘ θ) (hb : b ∈ (forcingCodeP C) ‘ i)
    (hle : ⟨b, q ↾ (succ (woodinSourceIndex i))⟩ₖ ∈ (forcingCodeR C) ‘ i) :
    sparsePrefixReplace (succ (woodinSourceIndex i)) q b ∈ (forcingCodeP C) ‘ θ ∧
    ⟨sparsePrefixReplace (succ (woodinSourceIndex i)) q b, q⟩ₖ ∈ (forcingCodeR C) ‘ θ ∧
    (sparsePrefixReplace (succ (woodinSourceIndex i)) q b) ↾ (succ (woodinSourceIndex i)) = b := by
  have hle' : ⟨b, ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ q⟩ₖ ∈ (forcingCodeR C) ‘ i := by
    rwa [woodinSparseStageCode_projection hΩ hAC hθ hi hq]
  have ht := mem_succ_self θ
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hs := woodinSparseStageCode_valid hΩ hAC hθ
  have hl := hs.system.lifts.lift i hi' θ ht (IsOrdinal.toIsTransitive.transitive _ hi) q hq b hb hle'
  rw [woodinSparseStageCode_lift hΩ hAC hθ hi' hq hb hle'] at hl
  refine ⟨hl.1, hl.2.1, ?_⟩
  rw [woodinSparseStageCode_projection hΩ hAC hθ hi hl.1] at hl
  exact hl.2.2

theorem woodinSparsePrefixCode_lift {i j q b : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hq : q ∈ (forcingCodeP (woodinSparsePrefixCode θ)) ‘ j)
    (hb : b ∈ (forcingCodeP (woodinSparsePrefixCode θ)) ‘ i)
    (hle : ⟨b, ((forcingCodeπ (woodinSparsePrefixCode θ)) ‘ ⟨i, j⟩ₖ) ‘ q⟩ₖ ∈
      (forcingCodeR (woodinSparsePrefixCode θ)) ‘ i) :
    ((forcingCodeL (woodinSparsePrefixCode θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨q, b⟩ₖ =
      sparsePrefixReplace (succ (woodinSourceIndex i)) q b := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hjsub := IsOrdinal.toIsTransitive.transitive _ (hθ j hj)
  have hs := woodinSparseStageCode_valid hΩ hAC hjsub
  have ht := woodinSparsePrefixCode_valid hΩ hAC hθ
  have hi' : i ∈ succ j := by
    rcases IsOrdinal.subset_iff.mp hij with rfl | hij
    · exact mem_succ_self _
    · exact mem_succ_iff.mpr (Or.inr hij)
  have hj' := mem_succ_self j
  have he : ForcingCodeExtends (woodinSparseStageCode j) (woodinSparsePrefixCode θ) := by
    rw [woodinSparseStageCode_eq_prefix hΩ hAC (hθ j hj)]
    apply woodinSparsePrefixCode_extends hΩ hAC hθ
    intro k hk
    rcases mem_succ_iff.mp hk with rfl | hk
    · exact hj
    · exact IsOrdinal.toIsTransitive.mem_trans hk hj
  have hpair : ⟨i, j⟩ₖ ∈ succ j ×ˢ succ j := kpair_mem_iff.mpr ⟨hi', hj'⟩
  rw [← hs.tableP.value_of_subset ht.tableP he.subP hj'] at hq
  rw [← hs.tableP.value_of_subset ht.tableP he.subP hi'] at hb
  rw [← hs.tableR.value_of_subset ht.tableR he.subR hi',
    ← hs.tableπ.value_of_subset ht.tableπ he.subπ hpair] at hle
  rw [← hs.tableL.value_of_subset ht.tableL he.subL hpair]
  exact woodinSparseStageCode_lift hΩ hAC hjsub hi' hq hb hle

end ZFVP
