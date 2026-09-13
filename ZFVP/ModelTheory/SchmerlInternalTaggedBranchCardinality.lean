import ZFVP.ModelTheory.SchmerlInternalTaggedTrees
import ZFVP.ModelTheory.SchmerlInternalWeakSpecialization
import ZFVP.SetTheory.RegularUnions

/-! The actual branch set of a tagged tree sum has the expected internal bound. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def taggedComponentBranches (D S κ r j : V) : V :=
  repl (fun B ↦ ({j} : V) ×ˢ B) (by definability)
    (internalCofinalBranches (D ‘ j) (S ‘ j) κ (r ‘ j))

theorem mem_taggedComponentBranches {D S κ r j B : V} :
    B ∈ taggedComponentBranches D S κ r j ↔
      ∃ C, IsInternalCofinalBranch (D ‘ j) (S ‘ j) κ (r ‘ j) C ∧ B = ({j} : V) ×ˢ C := by
  simp only [taggedComponentBranches, repl_spec, mem_internalCofinalBranches]

theorem taggedComponentBranches_definable (D S κ r : V) :
    ℒₛₑₜ-function₁[V] (taggedComponentBranches D S κ r) := by
  have hh : ℒₛₑₜ-relation[V] (fun X j ↦ ∀ B, B ∈ X ↔
      ∃ C, IsInternalCofinalBranch (D ‘ j) (S ‘ j) κ (r ‘ j) C ∧ B = ({j} : V) ×ˢ C) := by
    unfold IsInternalCofinalBranch
    definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_taggedComponentBranches]
  rfl

theorem taggedComponentBranches_cardLE (hAC : InternalChoice V) (D S κ r j : V) :
    taggedComponentBranches D S κ r j ≤# internalCofinalBranches (D ‘ j) (S ‘ j) κ (r ‘ j) :=
  cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC _)
    (definableGraph_mem_function _ (fun B ↦ ({j} : V) ×ˢ B) (by definability))
    (range_definableGraph _ _ _)

theorem internalTaggedTree_branches_cardLE (hAC : InternalChoice V) {J D S κ r : V}
    (hκ : IsInitialOrdinal κ) (hω : (ω : V) ⊆ κ) (hJ : J ≤# κ)
    (hB : ∀ j ∈ J, internalCofinalBranches (D ‘ j) (S ‘ j) κ (r ‘ j) ≤# κ) :
    internalCofinalBranches (internalTaggedTree J D) (internalTaggedTreeOrder J D S) κ
      (internalTaggedTreeRank J D r) ≤# κ := by
  let q := definableGraph J (taggedComponentBranches D S κ r) (taggedComponentBranches_definable D S κ r)
  have hq : ∀ j ∈ J, q ‘ j ≤# κ := by
    intro j hj
    rw [value_definableGraph _ _ _ hj]
    exact (taggedComponentBranches_cardLE hAC D S κ r j).trans (hB j hj)
  have hsub : internalCofinalBranches (internalTaggedTree J D) (internalTaggedTreeOrder J D S) κ
      (internalTaggedTreeRank J D r) ⊆ ⋃ˢ range q := by
    intro B hB
    obtain ⟨j, hj, C, hC, he⟩ := tagged_branch_decomposition
      (show IsNonempty κ from ⟨∅, hω _ empty_mem_ω⟩) ((mem_internalCofinalBranches _ _ _ _ _).mp hB)
    refine mem_sUnion_iff.mpr ⟨q ‘ j, ?_, ?_⟩
    · exact mem_range_of_kpair_mem (kpair_value_mem (by simpa only [q, domain_definableGraph] using hj))
    · rw [value_definableGraph _ _ _ hj]
      exact mem_taggedComponentBranches.mpr ⟨C, hC, he⟩
  exact ((cardLE_of_subset hsub).trans (sUnion_range_cardLE_prod hAC (domain_definableGraph _ _ _) hq)).trans
    (prod_cardLE_of_cardLE_initial hκ hω hJ (CardLE.refl _))

theorem internalTaggedTree_branches_hartogsOmega (hAC : InternalChoice V) {J D S r : V}
    (hJ : J ≤# hartogsNumber (ω : V))
    (hB : ∀ j ∈ J, internalCofinalBranches (D ‘ j) (S ‘ j) (hartogsNumber (ω : V)) (r ‘ j) ≤# hartogsNumber (ω : V)) :
    internalCofinalBranches (internalTaggedTree J D) (internalTaggedTreeOrder J D S) (hartogsNumber (ω : V))
      (internalTaggedTreeRank J D r) ≤# hartogsNumber (ω : V) :=
  internalTaggedTree_branches_cardLE hAC (hartogsNumber_initial _) (hartogs_omega_subset (CardLE.refl _)) hJ hB

end ZFVP.Schmerl
