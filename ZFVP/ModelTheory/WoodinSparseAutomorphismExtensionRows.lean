import ZFVP.ModelTheory.WoodinSparseActualAutomorphisms
import ZFVP.ModelTheory.CoherentAutomorphismCodeTransport
import ZFVP.ModelTheory.CoherentAutomorphismSuccessorRow
import ZFVP.ModelTheory.WoodinSparseCompletedFamilyAutomorphism
import ZFVP.ModelTheory.WoodinSparseLimitAutomorphismSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseSuccessorAutomorphism_row {Ω k H : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
    (hm : IsCoherentForcingAutomorphismFamily (succ k) (woodinSparsePrefixCode (succ k)) H)
    (ht : ∀ i ∈ succ k, (H ‘ i) ‘ ((forcingCodet (woodinSparsePrefixCode (succ k))) ‘ i) =
      (forcingCodet (woodinSparsePrefixCode (succ k))) ‘ i) :
    IsCoherentAutomorphismRow (succ k) (woodinSparseStageCode (succ k)) H
      (woodinSparseSuccessorAutomorphism k (H ‘ k)) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hc := woodinSparsePrefixCode_valid hΩ hAC hsub
  have hs := woodinSparseStageCode_valid hΩ hAC hsub
  have he := woodinSparseStageCode_extends hΩ hAC hsub
  have hP := fun i hi ↦ hc.tableP.value_of_subset hs.tableP he.subP (x := i) hi
  have hR := fun i hi ↦ hc.tableR.value_of_subset hs.tableR he.subR (x := i) hi
  have hms := hm.of_code_values hP hR
    (fun _ hi _ hj ↦ hc.tableπ.value_of_subset hs.tableπ he.subπ (kpair_mem_iff.mpr ⟨hi,hj⟩))
    (fun _ hi _ hj ↦ hc.tableE.value_of_subset hs.tableE he.subE (kpair_mem_iff.mpr ⟨hi,hj⟩))
  have hf := hm.iso k (mem_succ_self k)
  have hft := ht k (mem_succ_self k)
  have hg := woodinSparseSuccessorAutomorphism_automorphism hΩ hAC hk hf hft
  apply coherentAutomorphismRow_of_successor hs (mem_succ_self _) hms hg
  · rw [woodinSparseStageCode_top hΩ hAC hsub]
    exact woodinSparseSuccessorAutomorphism_top hΩ hAC hk hf hft
  · intro p hp
    rw [woodinSparseStageCode_projection hΩ hAC hsub (mem_succ_self k) (function_value_mem hg.1 hp),
      woodinSparseStageCode_projection hΩ hAC hsub (mem_succ_self k) hp]
    simpa only [woodinSourceIndex_successor] using woodinSparseSuccessorAutomorphism_restrict hΩ hAC hk hf hft hp
  · intro p hp
    rw [woodinSparseStageCode_section hΩ hAC hsub (mem_succ_self k) hp,
      woodinSparseStageCode_section hΩ hAC hsub (mem_succ_self k) (function_value_mem (hms.iso k (mem_succ_self k)).1 hp)]
    exact woodinSparseSuccessorAutomorphism_base hΩ hAC hk hf hft ((hP k (mem_succ_self k)).symm ▸ hp)

theorem woodinSparseDirectAutomorphism_row {Ω θ H : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hm : IsCoherentForcingAutomorphismFamily θ (woodinSparsePrefixCode θ) H)
    (ht : ∀ i ∈ θ, (H ‘ i) ‘ ∅ = ∅) :
    IsCoherentAutomorphismRow θ (woodinSparseStageCode θ) H
      (woodinSparseDirectAutomorphism θ (woodinSparsePrefixCode θ) H) := by
  have hc := woodinSparsePrefixCode_valid hΩ hAC hθ
  have hs := woodinSparseStageCode_valid hΩ hAC hθ
  have he := woodinSparseStageCode_extends hΩ hAC hθ
  have h00 : ∅ ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hll := ordinal_limit_of_not_successor hlim
  have hf := woodinSparseActualDirectAutomorphism hΩ hAC hθ hm h00 hll
  have hfs : IsForcingAutomorphism ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (woodinSparseDirectAutomorphism θ (woodinSparsePrefixCode θ) H) := by
    rw [(woodinSparseStageCode_direct h0 hlim hn).1, (woodinSparseStageCode_direct h0 hlim hn).2]
    exact hf
  refine ⟨hfs, ?_, ?_, ?_⟩
  · rw [woodinSparseStageCode_top hΩ hAC hθ]
    exact (woodinSparseActualDirectAutomorphism_top hΩ hAC hθ hm h00 hll (ht ∅ h00)).2
  · intro i hi p hp
    rw [woodinSparseStageCode_projection hΩ hAC hθ hi (function_value_mem hfs.1 hp),
      woodinSparseStageCode_projection hΩ hAC hθ hi hp]
    exact woodinSparseActualDirectAutomorphism_restrict hΩ hAC hθ hm h00 hll
      ((woodinSparseStageCode_direct h0 hlim hn).1 ▸ hp) hi
  · intro i hi p hp
    have hP := hc.tableP.value_of_subset hs.tableP he.subP hi
    have hpc := hP.symm ▸ hp
    have hmp : (H ‘ i) ‘ p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ i :=
      hP ▸ function_value_mem (hm.iso i hi).1 hpc
    rw [woodinSparseStageCode_section hΩ hAC hθ hi hp, woodinSparseStageCode_section hΩ hAC hθ hi hmp]
    exact (woodinSparseActualDirectAutomorphism_section hΩ hAC hθ hm h00 hll hi hpc).2

theorem woodinSparseCompletedFamilyAutomorphism_row {Ω θ H : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hm : IsCoherentForcingAutomorphismFamily θ (woodinSparsePrefixCode θ) H)
    (ht : ∀ i ∈ θ, (H ‘ i) ‘ ∅ = ∅) :
    IsCoherentAutomorphismRow θ (woodinSparseStageCode θ) H (woodinSparseCompletedFamilyAutomorphism θ H) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hc := woodinSparsePrefixCode_valid hΩ hAC hsub
  have hs := woodinSparseStageCode_valid hΩ hAC hsub
  have he := woodinSparseStageCode_extends hΩ hAC hsub
  have hf := woodinSparseCompletedFamilyAutomorphism_automorphism hΩ hAC hθ h0 hlim hn hm ht
  refine ⟨hf, ?_, ?_, ?_⟩
  · rw [woodinSparseStageCode_top hΩ hAC hsub]
    exact woodinSparseCompletedFamilyAutomorphism_top hΩ hAC hθ h0 hlim hn hm ht
  · intro i hi p hp
    rw [woodinSparseStageCode_projection hΩ hAC hsub hi (function_value_mem hf.1 hp),
      woodinSparseStageCode_projection hΩ hAC hsub hi hp]
    exact woodinSparseCompletedFamilyAutomorphism_restrict_earlier hΩ hAC hθ h0 hlim hn hm ht hp hi
  · intro i hi p hp
    have hP := hc.tableP.value_of_subset hs.tableP he.subP hi
    have hpc := hP.symm ▸ hp
    have hmp : (H ‘ i) ‘ p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ i :=
      hP ▸ function_value_mem (hm.iso i hi).1 hpc
    rw [woodinSparseStageCode_section hΩ hAC hsub hi hp, woodinSparseStageCode_section hΩ hAC hsub hi hmp]
    exact (woodinSparseCompletedFamilyAutomorphism_section_earlier hΩ hAC hθ h0 hlim hn hm ht hi hpc).2

end ZFVP
