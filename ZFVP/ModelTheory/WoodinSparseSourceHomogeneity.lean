import ZFVP.ModelTheory.WoodinSparseFullHomogeneity
import ZFVP.ModelTheory.ProjectionQuotientHomogeneity
import ZFVP.ModelTheory.WoodinSparseSourceSubgeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ j p q : V} [IsOrdinal θ]
local notation "c" => woodinSparseSourceStageCode θ
local notation "Q" => (forcingCodeP c) ‘ (woodinSourceIndex θ)
local notation "S" => (forcingCodeR c) ‘ (woodinSourceIndex θ)
local notation "π" => (forcingCodeπ c) ‘ ⟨j,woodinSourceIndex θ⟩ₖ

theorem woodinSparseSource_all_row_relative_homogeneous_exact
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hj : j ∈ succ (woodinSourceIndex θ)) (hp : p ∈ Q) (hq : q ∈ Q)
    (hle : ⟨π ‘ p,π ‘ q⟩ₖ ∈ (forcingCodeR c) ‘ j) :
    ∃ f, IsForcingAutomorphism Q S f ∧ (∀ z ∈ Q, π ‘ (f ‘ z) = π ‘ z) ∧
      ∃ w ∈ Q, ⟨w,f ‘ p⟩ₖ ∈ S ∧ ⟨w,q⟩ₖ ∈ S ∧ π ‘ w = π ‘ p := by
  have hc := woodinSparseSourceStageCode_valid hΩ hAC hθ
  have hQ := (woodinSparseSourceStageCode_row (mem_succ_self θ)).1
  have hS := (woodinSparseSourceStageCode_row (mem_succ_self θ)).2
  have hj' : j ∈ woodinSourceIndex (succ θ) := by simpa only [woodinSourceIndex_successor] using hj
  rcases woodinSourceIndex_cases hj' with rfl | ⟨δ,hδ,rfl⟩
  · have hπ := (hc.system.projection hj (mem_succ_self _) (empty_subset _)).maps
    have hz : ∀ z ∈ Q, ((forcingCodeπ c) ‘ ⟨∅,woodinSourceIndex θ⟩ₖ) ‘ z = ∅ := by
      intro z hz
      have hh := function_value_mem hπ hz
      rw [(woodinSparseSourceStageCode_seed (θ := θ)).1] at hh
      exact mem_singleton_iff.mp hh
    obtain ⟨f,hf,w,hw,hwf,hwq⟩ := woodinSparseStage_weak_homogeneous_below hΩ hAC hθ (hQ ▸ hp) (hQ ▸ hq)
    rw [← hQ,← hS] at hf
    rw [← hQ] at hw
    rw [← hS] at hwf hwq
    exact ⟨f,hf,fun z hz' ↦ (hz _ (function_value_mem hf.1 hz')).trans (hz z hz').symm,
      w,hw,hwf,hwq,(hz w hw).trans (hz p hp).symm⟩
  · let := IsOrdinal.of_mem hδ
    have hδsub : δ ⊆ θ := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hδ)
    have hπ := (woodinSparseSourceStageCode_matrices hδ (mem_succ_self θ)).1
    have hR := (woodinSparseSourceStageCode_row hδ).2.trans (woodinSparseStage_old_row hδ).2
    rw [hQ,hS,hπ]
    apply woodinSparseStage_relative_homogeneous_below_exact hΩ hAC hθ hδsub (hQ ▸ hp) (hQ ▸ hq)
    rwa [hπ,hR] at hle

theorem ForcingContext.woodinSparseSource_all_quotient_weak_homogeneous
    (A : ForcingContext V) (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ Ω) (hj : j ∈ succ (woodinSourceIndex θ))
    (hP : A.P = (forcingCodeP c) ‘ j) (hR : A.R = (forcingCodeR c) ‘ j) :
    ∀ x ∈ A.projectionQuotient Q π, ∀ y ∈ A.projectionQuotient Q π,
      ∃ f, IsForcingAutomorphism (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) f ∧
        ForcingCompatible (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) (f ‘ x) y := by
  have hc := woodinSparseSourceStageCode_valid hΩ hAC hθ
  let := IsOrdinal.of_mem hj
  have hsub : j ⊆ woodinSourceIndex θ := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hj)
  have hπ := hc.system.projection hj (mem_succ_self _) hsub
  rw [← hP,← hR] at hπ
  apply A.projectionQuotient_weak_homogeneous (hc.system.order.preorder _ (mem_succ_self _)) hπ
  intro p hp q hq hle
  rw [hR] at hle
  exact woodinSparseSource_all_row_relative_homogeneous_exact hΩ hAC hθ hj hp hq hle

end ZFVP
