import ZFVP.ModelTheory.ForcingLSHullPreparation
import ZFVP.ModelTheory.ForcingHullNormalization
import ZFVP.ModelTheory.WeaklyLSTwoHullFunctionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem hullImage_contains_evaluation (A : ForcingContext V) {B D Y : V}
    (hB : ∀ τ ∈ B, IsForcingName A.P τ) (hD : ∀ τ ∈ D, IsForcingName A.P τ)
    (hBY : B ⊆ Y) (hBD : B ⊆ D) :
    range (A.evaluationGraph B hB) ⊆ A.hullImage D hD Y := by
  intro x hx
  obtain ⟨τ, hτ, rfl⟩ := (A.mem_range_evaluationGraph_iff B hB x).mp hx
  exact (A.mem_hullImage_iff D hD Y _).mpr
    ⟨τ, mem_inter_iff.mpr ⟨hBY τ hτ, hBD τ hτ⟩, rfl⟩

/-- Equality-table normalization bounds the output names before the
second hull supplies a small support for a new function. -/
theorem lowRank_hullImage_closed (A : ForcingContext V)
    {Y ζ β η δ ν α γ : V} [IsOrdinal ζ] [IsOrdinal α] [IsOrdinal γ]
    (hY : IsElementaryInclusion Y (hierarchy ζ))
    (hβ : Cn 1 β) (hη : Cn 1 η) (hηβ : η ∈ β)
    (hηζ : succ η ⊆ ζ) (hαη : α ⊆ η)
    (hδ : IsWeaklyLSCardinal δ)
    (hclosure : (Y ∩ hierarchy η) ^ hierarchy δ ⊆ Y) (hzero : (∅ : V) ∈ Y)
    (hν : ν ∈ δ) (hνη : ν ⊆ η) (hνY : hierarchy ν ⊆ Y)
    (hBν : forcingNameHierarchy A.P γ ⊆ hierarchy ν) (hPν : A.P ⊆ hierarchy ν)
    (hPη : A.P ∈ hierarchy η)
    (hT : forcingNameEqualityTable A.P A.R (lowRankNameSet A.P β)
      (lowRankNameSet A.P η) ∈ Y) :
    ((A.hullImage (lowRankNameSet A.P β) (A.lowRankNameSet_names β) Y) ∩
      hierarchy (A.check α)) ^ hierarchy (A.check γ) ⊆
        A.hullImage (lowRankNameSet A.P β) (A.lowRankNameSet_names β) Y := by
  let := hβ.ordinal
  let := hη.ordinal
  let := hδ.1.1
  let := hierarchy_transitive ζ
  intro f hf
  obtain ⟨F, rfl⟩ := A.ofName_surjective f
  let := IsFunction.of_mem hf
  let B := forcingNameHierarchy A.P γ
  let C := Y ∩ lowRankNameSet A.P η
  have hB : ∀ τ ∈ B, IsForcingName A.P τ := forcingNameHierarchy_names A.P γ
  have hC : ∀ τ ∈ C, IsForcingName A.P τ :=
    fun τ hτ ↦ A.lowRankNameSet_names η τ (mem_inter_iff.mp hτ).2
  have hdom : domain (A.ofName F) ⊆ range (A.evaluationGraph B hB) := by
    rw [domain_eq_of_mem_function hf, A.lsInputNameEvaluation_range γ]
  have hPX : A.P ⊆ Y := subset_trans hPν hνY
  have hnormalize := A.lowRank_hullImage_normalize hY hPX
    (A.lowRankNameSet_names β) hη hPη hT
  have hcheckαη : A.check α ⊆ A.check η := (A.checkEmbedding.subset_iff _ _).mpr hαη
  have hran : range (A.ofName F) ⊆ range (A.evaluationGraph C hC) := by
    intro y hy
    have hmem := range_subset_of_mem_function hf y hy
    apply hnormalize
    exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp hmem).1,
      hierarchy_mono hcheckαη y (mem_inter_iff.mp hmem).2⟩
  have hCY : C ⊆ Y ∩ hierarchy η := by
    intro τ hτ
    exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp hτ).1,
      lowRankNameSet_subset A.P η τ (mem_inter_iff.mp hτ).2⟩
  have hδsucc : ∀ ξ ∈ δ, succ ξ ∈ δ := fun _ hξ ↦
    initial_succ_mem hδ.1 (IsOrdinal.toIsTransitive.transitive _ hδ.2.1) hξ
  obtain ⟨τ, hτY, hτeval, hτrank⟩ := A.weaklyLS_two_hull_function_name hY hηζ
    hη.successor_closed hδ hδsucc hclosure hzero hν hνη hνY hBν hPν hCY hB hC F hdom hran
  have hsηβ : succ η ⊆ β := by
    intro z hz
    rcases mem_succ_iff.mp hz with rfl | hz
    · exact hηβ
    · exact IsOrdinal.toIsTransitive.mem_trans hz hηβ
  have hτβ : τ.val ∈ hierarchy β := by
    apply hierarchy_mono hsηβ
    rw [hierarchy_succ, mem_power_iff]
    exact hτrank
  apply (A.mem_hullImage_iff _ _ Y _).mpr
  exact ⟨τ.val, mem_inter_iff.mpr ⟨hτY,
    (mem_lowRankNameSet A.P β τ.val).mpr ⟨hτβ, τ.property⟩⟩, hτeval.symm⟩

end ForcingContext
end ZFVP
