import ZFVP.ModelTheory.WoodinIterationInvariant
import ZFVP.SetTheory.ForcingIterationHistory
import ZFVP.SetTheory.ForcingBoundCodeExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsWoodinIterationHistory (δ θ H J : V) : Prop where
  codes : IsForcingIterationHistory θ H
  cardinals : IsIterationTable θ J
  stage : (∀ i ∈ θ, IsWoodinIteration δ (succ i) (H ‘ i) (J ‘ i))
  increasing : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → J ‘ i ⊆ J ‘ j)

noncomputable def woodinHistoryCardinalUnion (θ J : V) : V :=
  iterationTableUnion θ (fun i ↦ J ‘ i) (by definability)

theorem IsWoodinIterationHistory.cardinal_directed {δ θ H J : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ H J) :
    ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ, J ‘ i ⊆ J ‘ k ∧ J ‘ j ⊆ J ‘ k := by
  intro i hi j hj
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
  · exact ⟨j, hj, h.increasing i hi j hj (IsOrdinal.toIsTransitive.transitive _ hij), subset_refl _⟩
  · exact ⟨i, hi, subset_refl _, subset_refl _⟩
  · exact ⟨i, hi, subset_refl _, h.increasing j hj i hi (IsOrdinal.toIsTransitive.transitive _ hji)⟩

theorem IsWoodinIterationHistory.cardinal_union_table {δ θ H J : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ H J) :
    IsIterationTable θ (woodinHistoryCardinalUnion θ J) :=
  iterationTableUnion_family (by definability) (fun i hi ↦ (h.stage i hi).cardinals)
    h.cardinal_directed

theorem IsWoodinIterationHistory.cardinal_union_value {δ θ H J i j : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ H J) (hi : i ∈ θ) (hj : j ∈ succ i) :
    (woodinHistoryCardinalUnion θ J) ‘ j = (J ‘ i) ‘ j :=
  iterationTableUnion_value (by definability) (fun i hi ↦ (h.stage i hi).cardinals.function)
    h.cardinal_directed hi ((h.stage i hi).cardinals.domain_eq.symm ▸ hj)

theorem IsWoodinIterationHistory.union_stage {δ θ H J i j : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ H J) (hi : i ∈ θ) (hj : j ∈ succ i) :
    woodinIterationStage (forcingIterationCodeUnion θ H) (woodinHistoryCardinalUnion θ J) j =
      woodinIterationStage (H ‘ i) (J ‘ i) j := by
  have he := forcingIterationCodeUnion_extends (H := H) hi
  have hs := (h.stage i hi).code
  have hu := h.codes.union_code
  unfold woodinIterationStage
  rw [← hs.tableP.value_of_subset hu.tableP he.subP hj,
    ← hs.tableR.value_of_subset hu.tableR he.subR hj,
    ← hs.tablet.value_of_subset hu.tablet he.subt hj, h.cardinal_union_value hi hj]

theorem IsWoodinIterationHistory.union_iteration {δ θ H J : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ H J) :
    IsWoodinIteration δ θ (forcingIterationCodeUnion θ H) (woodinHistoryCardinalUnion θ J) := by
  refine ⟨h.codes.union_code, h.cardinal_union_table, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [h.union_stage hi (mem_succ_self i)]
    exact (h.stage i hi).stage i (mem_succ_self i)
  · intro i hi
    rw [h.union_stage hi (mem_succ_self i)]
    exact (h.stage i hi).small i (mem_succ_self i)
  · intro i hi
    rw [h.cardinal_union_value hi (mem_succ_self i)]
    exact (h.stage i hi).inaccessible i (mem_succ_self i)
  · intro i hi
    rw [h.cardinal_union_value hi (mem_succ_self i)]
    exact (h.stage i hi).bounded i (mem_succ_self i)
  · intro i hi j hj hij
    have hi' : i ∈ succ j := mem_succ_iff.mpr (Or.inr hij)
    rw [h.cardinal_union_value hj hi', h.cardinal_union_value hj (mem_succ_self j)]
    exact (h.stage j hj).increasing i hi' j (mem_succ_self j) hij

theorem woodinHistoryCardinalUnion_extends {θ J i : V} (hi : i ∈ θ) :
    J ‘ i ⊆ woodinHistoryCardinalUnion θ J := by
  intro x hx
  exact mem_sUnion_iff.mpr ⟨J ‘ i, (repl_spec (by definability)).mpr ⟨i, hi, rfl⟩, hx⟩

theorem IsWoodinIterationHistory.next {δ θ H J s K : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ H J)
    (hs : IsWoodinIteration δ (succ θ) s K)
    (he : ForcingCodeExtends (forcingIterationCodeUnion θ H) s)
    (hK : woodinHistoryCardinalUnion θ J ⊆ K) :
    IsWoodinIterationHistory δ (succ θ) (forcingFamilyNext θ H s) (forcingFamilyNext θ J K) := by
  have oldH (i : V) (hi : i ∈ θ) : (forcingFamilyNext θ H s) ‘ i = H ‘ i :=
    forcingFamilyNext_old hi
  have oldJ (i : V) (hi : i ∈ θ) : (forcingFamilyNext θ J K) ‘ i = J ‘ i :=
    forcingFamilyNext_old hi
  have past (i : V) (hi : i ∈ θ) : ForcingCodeExtends (H ‘ i) s :=
    (forcingIterationCodeUnion_extends hi).trans he
  have pastK (i : V) (hi : i ∈ θ) : J ‘ i ⊆ K :=
    subset_trans (woodinHistoryCardinalUnion_extends hi) hK
  refine ⟨⟨forcingFamilyNext_table _ _ _, ?_, ?_⟩, forcingFamilyNext_table _ _ _, ?_, ?_⟩
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [forcingFamilyNext_new]; exact hs.code
    · rw [oldH i hi]; exact (h.stage i hi).code
  · intro i hi j hj hij
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingFamilyNext_new]
      rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingFamilyNext_new]; exact ForcingCodeExtends.refl _
      · rw [oldH i hi]; exact past i hi
    · let := IsOrdinal.of_mem hi
      let := IsOrdinal.of_mem hj
      have hi' : i ∈ θ := ordinal_mem_of_subset_mem hij hj
      rw [oldH i hi', oldH j hj]
      exact h.codes.increasing i hi' j hj hij
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [forcingFamilyNext_new, forcingFamilyNext_new]; exact hs
    · rw [oldH i hi, oldJ i hi]; exact h.stage i hi
  · intro i hi j hj hij
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingFamilyNext_new]
      rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingFamilyNext_new]
      · rw [oldJ i hi]; exact pastK i hi
    · let := IsOrdinal.of_mem hi
      let := IsOrdinal.of_mem hj
      have hi' : i ∈ θ := ordinal_mem_of_subset_mem hij hj
      rw [oldJ i hi', oldJ j hj]
      exact h.increasing i hi' j hj hij

end ZFVP
