import ZFVP.ModelTheory.WoodinSparseInitialAutomorphismExtension
import ZFVP.ModelTheory.WoodinSparseRelativeHomogeneityFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ p q : V} [IsOrdinal θ]
local notation "c" => woodinSparseStageCode Ω

theorem woodinSparseStage_row_weak_homogeneous
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hp : p ∈ (forcingCodeP c) ‘ θ) (hq : q ∈ (forcingCodeP c) ‘ θ) :
    ∃ f, IsForcingAutomorphism ((forcingCodeP c) ‘ θ) ((forcingCodeR c) ‘ θ) f ∧
      ForcingCompatible ((forcingCodeP c) ‘ θ) ((forcingCodeR c) ‘ θ) (f ‘ p) q := by
  let := hΩ.inaccessible.1
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  have hθ' : θ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hθ)
  have hz : (∅ : V) ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset Ω))
  have hπ := hc.system.projection hz hθ' (empty_subset θ)
  have hp0 := function_value_mem hπ.maps hp
  have hq0 := function_value_mem hπ.maps hq
  have hP0 : (forcingCodeP c) ‘ ∅ = woodinSparseInitialCarrier :=
    (woodinSparseStageCode_endpoint_row_values hΩ hAC (empty_subset Ω)).1.symm.trans woodinSparseStageCode_initial.1
  have hR0 : (forcingCodeR c) ‘ ∅ = woodinSparseInitialOrder :=
    (woodinSparseStageCode_endpoint_row_values hΩ hAC (empty_subset Ω)).2.1.symm.trans woodinSparseStageCode_initial.2
  obtain ⟨f, hf, hft, r, hr, hrp, hrq⟩ := woodinSparseInitial_weak_homogeneous_fixed_top hΩ (hP0 ▸ hp0) (hP0 ▸ hq0)
  obtain ⟨H, _, hH, hH0⟩ := woodinSparseInitialAutomorphism_extends hΩ hAC hf hft
  have hF := hH.iso θ hθ'
  have hFp := function_value_mem hF.1 hp
  have hproj : ((forcingCodeπ c) ‘ ⟨∅,θ⟩ₖ) ‘ ((H ‘ θ) ‘ p) =
      f ‘ (((forcingCodeπ c) ‘ ⟨∅,θ⟩ₖ) ‘ p) := by
    rw [hH.proj ∅ hz θ hθ' (empty_subset θ) p hp, hH0]
  obtain ⟨s, hs, hsp, hsr⟩ := hπ.lift _ hFp r (hP0.symm ▸ hr) (by rwa [hproj, hR0])
  obtain ⟨g, hg, _, t, ht, hts, htq⟩ := woodinSparseStage_row_relative_homogeneous hΩ hAC hθ
    (empty_subset θ) hs hq (by rwa [hsr, hR0])
  have hg' : IsForcingIsomorphism _ _ _ _ g := hg
  refine ⟨compose (H ‘ θ) g, hF.comp hg', t, ht, ?_, htq⟩
  rw [value_compose_of_mem_function hF.1 hg.1 hp]
  exact (hc.system.order.preorder θ hθ').2.2 _ ht _ (function_value_mem hg.1 hs)
    _ (function_value_mem hg.1 hFp) hts ((hg.2.2.2 _ hs _ hFp).mp hsp)

theorem woodinSparseStage_weak_homogeneous_below
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    ∃ f, IsForcingAutomorphism ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
        ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) f ∧
      ForcingCompatible ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
        ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (f ‘ p) q := by
  have hrow := woodinSparseStageCode_endpoint_row_values hΩ hAC hθ
  rw [hrow.1] at hp hq ⊢
  rw [hrow.2.1]
  exact woodinSparseStage_row_weak_homogeneous hΩ hAC hθ hp hq

end ZFVP
