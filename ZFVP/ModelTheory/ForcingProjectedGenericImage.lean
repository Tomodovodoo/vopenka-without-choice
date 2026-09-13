import ZFVP.ModelTheory.ProjectionInclusion
import ZFVP.SetTheory.EndExtensionRank
import ZFVP.SetTheory.RankEnumerationInaccessible
import ZFVP.SetTheory.RegularCofinalSurjection
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def checkedMapGraph (A : ForcingContext V) (f : V) (H : A.Model) : A.Model :=
  definableGraph H (fun x ↦ (A.check f) ‘ x) (by definability)

noncomputable def checkedMapImage (A : ForcingContext V) (f : V) (H : A.Model) : A.Model :=
  range (A.checkedMapGraph f H)

theorem mem_checkedMapImage_iff (A : ForcingContext V) (f : V) (H x : A.Model) :
    x ∈ A.checkedMapImage f H ↔ ∃ y ∈ H, x = (A.check f) ‘ y := by
  unfold checkedMapImage checkedMapGraph
  simp only [mem_range_iff, pair_mem_definableGraph_iff]

theorem checkedMapGraph_function (A : ForcingContext V) (f : V) (H : A.Model) :
    A.checkedMapGraph f H ∈ A.checkedMapImage f H ^ H := by
  have hf : IsFunction (A.checkedMapGraph f H) := by unfold checkedMapGraph; infer_instance
  simpa only [checkedMapImage, checkedMapGraph, domain_definableGraph] using
    IsFunction.mem_function (A.checkedMapGraph f H)

theorem mem_projectedGeneric_image_iff (C A : ForcingContext V) {π E : V}
    (hπ : IsForcingSplitProjection C.P C.R A.P A.R π E)
    (he : forcingProjectionGeneric C.P C.R π A.G = C.G) (f : V) (x : A.Model) :
    x ∈ A.checkedMapImage f (C.projectedGenericSet A E) ↔
      ∃ p ∈ C.G, x = A.check (f ‘ p) := by
  rw [A.mem_checkedMapImage_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨p, _, rfl⟩ := (A.mem_check_iff C.P y).mp (mem_sep_iff.mp hy).1
    exact ⟨p, (C.check_mem_projectedGenericSet A hπ he p).mp hy,
      (A.checkEmbedding.map_value_total f p).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨A.check p, (C.check_mem_projectedGenericSet A hπ he p).mpr hp,
      A.checkEmbedding.map_value_total f p⟩

/-- A projected generic can have full rank at its own stage. Its members still
lie in that rank, so the later rank-enumeration invariant enumerates the set. -/
theorem projectedGeneric_shortEnumeration (C A : ForcingContext V) {π E γ δ : V}
    [IsOrdinal γ] [IsOrdinal δ]
    (hπ : IsForcingSplitProjection C.P C.R A.P A.R π E)
    (he : forcingProjectionGeneric C.P C.R π A.G = C.G)
    (hP : rank C.P ⊆ γ) (hγδ : γ ∈ δ)
    (henum : HasShortRankEnumerations (A.check δ) (A.check δ)) :
    ∃ ν ∈ A.check δ, ∃ s ∈ (C.projectedGenericSet A E) ^ ν,
      range s = C.projectedGenericSet A E := by
  have hr : rank (A.check C.P) ⊆ A.check γ := by
    change rank (A.checkEmbedding C.P) ⊆ A.checkEmbedding γ
    rw [← MembershipEndExtension.map_rank]
    exact (A.checkEmbedding.subset_iff _ _).mpr hP
  have hH : C.projectedGenericSet A E ⊆ hierarchy (A.check γ) :=
    subset_trans (fun _ hx ↦ (mem_sep_iff.mp hx).1)
      (subset_trans (subset_hierarchy_rank (A.check C.P)) (hierarchy_mono hr))
  obtain ⟨ν, hν, g, hg, hgr⟩ := henum (A.check γ) ((A.check_mem_iff _ _).mpr hγδ)
  let := IsOrdinal.of_mem hν
  have hcard := (cardLE_of_subset hH).trans
    (cardLE_of_surjective_function (ordinal_wellOrderable ν) hg hgr)
  have hn : IsNonempty (C.projectedGenericSet A E) := by
    obtain ⟨p, hp⟩ := C.generic.1.2.1
    exact ⟨A.check p, (C.check_mem_projectedGenericSet A hπ he p).mpr hp⟩
  obtain ⟨s, hs, hsr⟩ := surjection_of_injection hcard hn
  exact ⟨ν, hν, s, hs, hsr⟩

theorem projectedGeneric_image_shortEnumeration (C A : ForcingContext V) {π E γ δ : V}
    [IsOrdinal γ] [IsOrdinal δ]
    (hπ : IsForcingSplitProjection C.P C.R A.P A.R π E)
    (he : forcingProjectionGeneric C.P C.R π A.G = C.G)
    (hP : rank C.P ⊆ γ) (hγδ : γ ∈ δ)
    (henum : HasShortRankEnumerations (A.check δ) (A.check δ)) (f : V) :
    ∃ ν ∈ A.check δ, ∃ s ∈ (A.checkedMapImage f (C.projectedGenericSet A E)) ^ ν,
      range s = A.checkedMapImage f (C.projectedGenericSet A E) := by
  obtain ⟨ν, hν, s, hs, hsr⟩ := C.projectedGeneric_shortEnumeration A hπ he hP hγδ henum
  have hg := A.checkedMapGraph_function f (C.projectedGenericSet A E)
  exact ⟨ν, hν, compose s (A.checkedMapGraph f (C.projectedGenericSet A E)),
    compose_function hs hg, range_compose_surjective hs hg hsr rfl⟩

end ForcingContext
end ZFVP
