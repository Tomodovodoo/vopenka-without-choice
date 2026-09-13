import ZFVP.ModelTheory.WoodinSparseRelativeHomogeneity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω δ p q : V} [IsOrdinal δ]
local notation "c" => woodinSparseStageCode Ω

theorem woodinSparseStage_relative_homogeneous_family
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hδ : δ ⊆ Ω)
    (hp : p ∈ (forcingCodeP c) ‘ Ω) (hq : q ∈ (forcingCodeP c) ‘ Ω)
    (hle : ⟨((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ p,((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ q⟩ₖ
      ∈ (forcingCodeR (woodinSparseStageCode δ)) ‘ δ) :
    ∃ H W, IsCoherentAutomorphismWitnessHistory (succ Ω) c
      (woodinSparseEndpointThread Ω p) (woodinSparseEndpointThread Ω q) δ H W := by
  let := hΩ.inaccessible.1
  let a := woodinSparseEndpointThread Ω p
  let b := woodinSparseEndpointThread Ω q
  let G := woodinSparseHomogeneityRow δ a b
  have hG : ℒₛₑₜ-function₃ G := woodinSparseHomogeneityRow_definable δ a b
  have hδ' : δ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hδ)
  have hle' : ⟨a ‘ δ,b ‘ δ⟩ₖ ∈ (forcingCodeR c) ‘ δ := by
    rw [woodinSparseEndpointThread_value hδ', woodinSparseEndpointThread_value hδ',
      ← (woodinSparseStageCode_endpoint_row_values hΩ hAC hδ).2.1]
    exact hle
  let F := coherentAutomorphismWitnessBuilder G
  have hF : ℒₛₑₜ-function₁ F := coherentAutomorphismWitnessBuilder_definable G hG
  let H := automorphismWitnessMaps (coherentAutomorphismHistory F hF (succ Ω))
  let W := automorphismWitnessBounds (coherentAutomorphismHistory F hF (succ Ω))
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  have hh : IsCoherentAutomorphismWitnessHistory (succ Ω) c a b δ H W :=
    coherentAutomorphismWitnessRec_family_of_builder G hG hc
      (woodinSparseHomogeneityRow_spec hΩ hAC hδ hp hq hle') (subset_refl _)
  exact ⟨H, W, hh⟩

/-- Relative homogeneity at every row, including fixed points which need not
be supercompact. The endpoint family is restricted to the requested row. -/
theorem woodinSparseStage_row_relative_homogeneous {θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ Ω) (hδ : δ ⊆ θ)
    (hp : p ∈ (forcingCodeP c) ‘ θ) (hq : q ∈ (forcingCodeP c) ‘ θ)
    (hle : ⟨((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ p,((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ q⟩ₖ
      ∈ (forcingCodeR c) ‘ δ) :
    ∃ f, IsForcingAutomorphism ((forcingCodeP c) ‘ θ) ((forcingCodeR c) ‘ θ) f ∧
      (∀ z ∈ (forcingCodeP c) ‘ θ,
        ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ (f ‘ z) = ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ z) ∧
      ForcingCompatible ((forcingCodeP c) ‘ θ) ((forcingCodeR c) ‘ θ) (f ‘ p) q := by
  let := hΩ.inaccessible.1
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  have hθ' : θ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hθ)
  have hδΩ := subset_trans hδ hθ
  have hδ' : δ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hδΩ)
  let e := (forcingCodeE c) ‘ ⟨θ,Ω⟩ₖ
  have hep : e ‘ p ∈ (forcingCodeP c) ‘ Ω := hc.system.split.secMaps θ hθ' Ω (mem_succ_self Ω) hθ p hp
  have heq : e ‘ q ∈ (forcingCodeP c) ‘ Ω := hc.system.split.secMaps θ hθ' Ω (mem_succ_self Ω) hθ q hq
  have hsp : ((forcingCodeπ c) ‘ ⟨θ,Ω⟩ₖ) ‘ (e ‘ p) = p :=
    hc.system.split.retraction θ hθ' Ω (mem_succ_self Ω) hθ p hp
  have hsq : ((forcingCodeπ c) ‘ ⟨θ,Ω⟩ₖ) ‘ (e ‘ q) = q :=
    hc.system.split.retraction θ hθ' Ω (mem_succ_self Ω) hθ q hq
  have hlep : ((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ (e ‘ p) = ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ p := by
    rw [← hc.system.split.projComp δ hδ' θ hθ' Ω (mem_succ_self Ω) hδ hθ _ hep, hsp]
  have hleq : ((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ (e ‘ q) = ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ q := by
    rw [← hc.system.split.projComp δ hδ' θ hθ' Ω (mem_succ_self Ω) hδ hθ _ heq, hsq]
  obtain ⟨H, W, hh⟩ := woodinSparseStage_relative_homogeneous_family hΩ hAC hδΩ hep heq (by
    rw [hlep, hleq, (woodinSparseStageCode_endpoint_row_values hΩ hAC hδΩ).2.1]
    exact hle)
  refine ⟨H ‘ θ, hh.automorphism.iso θ hθ', ?_, ?_⟩
  · intro z hz
    exact hh.relative_projection hc hθ' hδ' hδ hz
  · have hhθ := hh.compatible hθ'
    simpa only [woodinSparseEndpointThread_value hθ', hsp, hsq] using hhθ

theorem woodinSparseStage_relative_homogeneous_below {θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ Ω) (hδ : δ ⊆ θ)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (hle : ⟨((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ p,
      ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ q⟩ₖ
      ∈ (forcingCodeR (woodinSparseStageCode δ)) ‘ δ) :
    ∃ f, IsForcingAutomorphism ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
        ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) f ∧
      (∀ z ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ,
        ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ (f ‘ z) =
          ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ z) ∧
      ForcingCompatible ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
        ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (f ‘ p) q := by
  let := hΩ.inaccessible.1
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  have hs := woodinSparseStageCode_valid hΩ hAC hθ
  have he := woodinSparseStageCode_extends_endpoint hΩ hAC hθ
  have hδ' : δ ∈ succ θ := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hδ)
  have hπ := hs.tableπ.value_of_subset hc.tableπ he.subπ
    (kpair_mem_iff.mpr ⟨hδ', mem_succ_self θ⟩)
  have hrow := woodinSparseStageCode_endpoint_row_values hΩ hAC hθ
  rw [hrow.1] at hp hq ⊢
  rw [hrow.2.1, hπ]
  apply woodinSparseStage_row_relative_homogeneous hΩ hAC hθ hδ hp hq
  rwa [← hπ, ← (woodinSparseStageCode_endpoint_row_values hΩ hAC (subset_trans hδ hθ)).2.1]

theorem woodinSparseStage_row_relative_homogeneous_exact {θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ Ω) (hδ : δ ⊆ θ)
    (hp : p ∈ (forcingCodeP c) ‘ θ) (hq : q ∈ (forcingCodeP c) ‘ θ)
    (hle : ⟨((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ p,((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ q⟩ₖ
      ∈ (forcingCodeR c) ‘ δ) :
    ∃ f, IsForcingAutomorphism ((forcingCodeP c) ‘ θ) ((forcingCodeR c) ‘ θ) f ∧
      (∀ z ∈ (forcingCodeP c) ‘ θ,
        ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ (f ‘ z) = ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ z) ∧
      ∃ w ∈ (forcingCodeP c) ‘ θ, ⟨w, f ‘ p⟩ₖ ∈ (forcingCodeR c) ‘ θ ∧
        ⟨w, q⟩ₖ ∈ (forcingCodeR c) ‘ θ ∧
        ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ w = ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ p := by
  let := hΩ.inaccessible.1
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  have hθ' : θ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hθ)
  have hδΩ := subset_trans hδ hθ
  have hδ' : δ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hδΩ)
  let e := (forcingCodeE c) ‘ ⟨θ,Ω⟩ₖ
  have hep : e ‘ p ∈ (forcingCodeP c) ‘ Ω := hc.system.split.secMaps θ hθ' Ω (mem_succ_self Ω) hθ p hp
  have heq : e ‘ q ∈ (forcingCodeP c) ‘ Ω := hc.system.split.secMaps θ hθ' Ω (mem_succ_self Ω) hθ q hq
  have hsp : ((forcingCodeπ c) ‘ ⟨θ,Ω⟩ₖ) ‘ (e ‘ p) = p :=
    hc.system.split.retraction θ hθ' Ω (mem_succ_self Ω) hθ p hp
  have hsq : ((forcingCodeπ c) ‘ ⟨θ,Ω⟩ₖ) ‘ (e ‘ q) = q :=
    hc.system.split.retraction θ hθ' Ω (mem_succ_self Ω) hθ q hq
  have hlep : ((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ (e ‘ p) = ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ p := by
    rw [← hc.system.split.projComp δ hδ' θ hθ' Ω (mem_succ_self Ω) hδ hθ _ hep, hsp]
  have hleq : ((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ (e ‘ q) = ((forcingCodeπ c) ‘ ⟨δ,θ⟩ₖ) ‘ q := by
    rw [← hc.system.split.projComp δ hδ' θ hθ' Ω (mem_succ_self Ω) hδ hθ _ heq, hsq]
  obtain ⟨H, W, hh⟩ := woodinSparseStage_relative_homogeneous_family hΩ hAC hδΩ hep heq (by
    rw [hlep, hleq, (woodinSparseStageCode_endpoint_row_values hΩ hAC hδΩ).2.1]
    exact hle)
  refine ⟨H ‘ θ, hh.automorphism.iso θ hθ', ?_, ?_⟩
  · intro z hz
    exact hh.relative_projection hc hθ' hδ' hδ hz
  · refine ⟨W ‘ θ, hh.mem θ hθ', ?_, ?_, ?_⟩
    · simpa only [woodinSparseEndpointThread_value hθ', hsp] using hh.left θ hθ'
    · simpa only [woodinSparseEndpointThread_value hθ', hsq] using hh.right θ hθ'
    · rw [hh.proj δ hδ' θ hθ' hδ, hh.initialWitness δ hδ' (subset_refl _),
        woodinSparseEndpointThread_value hδ', hlep]

theorem woodinSparseStage_relative_homogeneous_below_exact {θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ Ω) (hδ : δ ⊆ θ)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (hle : ⟨((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ p,
      ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ q⟩ₖ
      ∈ (forcingCodeR (woodinSparseStageCode δ)) ‘ δ) :
    ∃ f, IsForcingAutomorphism ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
        ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) f ∧
      (∀ z ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ,
        ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ (f ‘ z) =
          ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ z) ∧
      ∃ w ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ,
        ⟨w,f ‘ p⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode θ)) ‘ θ ∧
        ⟨w,q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode θ)) ‘ θ ∧
        ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ w =
          ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨δ,θ⟩ₖ) ‘ p := by
  let := hΩ.inaccessible.1
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  have hs := woodinSparseStageCode_valid hΩ hAC hθ
  have he := woodinSparseStageCode_extends_endpoint hΩ hAC hθ
  have hδ' : δ ∈ succ θ := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hδ)
  have hπ := hs.tableπ.value_of_subset hc.tableπ he.subπ
    (kpair_mem_iff.mpr ⟨hδ', mem_succ_self θ⟩)
  have hrow := woodinSparseStageCode_endpoint_row_values hΩ hAC hθ
  rw [hrow.1] at hp hq ⊢
  rw [hrow.2.1, hπ]
  apply woodinSparseStage_row_relative_homogeneous_exact hΩ hAC hθ hδ hp hq
  rwa [← hπ, ← (woodinSparseStageCode_endpoint_row_values hΩ hAC (subset_trans hδ hθ)).2.1]

end ZFVP
