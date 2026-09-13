import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.Hartogs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The rank-map definition of inaccessibility bounds Hartogs numbers of all
sets in the inaccessible rank, without an internal choice assumption. -/
theorem IsChoicelessInaccessible.hartogsNumber_mem {κ A : V}
    (hκ : IsChoicelessInaccessible κ) (hA : A ∈ hierarchy κ) : hartogsNumber A ∈ κ := by
  classical
  let := hκ.1
  by_contra hn
  have hsub : κ ⊆ hartogsNumber A := by
    rcases IsOrdinal.mem_trichotomy (hartogsNumber A) κ with hlt | he | hgt
    · exact False.elim (hn hlt)
    · rw [he]
    · exact IsOrdinal.toIsTransitive.transitive _ hgt
  have hs : ∀ β ∈ κ, succ β ∈ κ := fun _ ↦ regularCardinal_succ_closed hκ.regular
  have hB : (℘ A ×ˢ ℘ (A ×ˢ A)) ∈ hierarchy κ :=
    prod_mem_hierarchy_limit hs (power_mem_hierarchy_limit hs hA)
      (power_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs hA hA))
  have hC : wellOrderCodes A ∈ hierarchy κ :=
    (hierarchy_transitive κ).mem_trans (mem_power_iff.mpr (show wellOrderCodes A ⊆ ℘ A ×ˢ ℘ (A ×ˢ A) from sep_subset))
      (power_mem_hierarchy_limit hs hB)
  let F : V → V := fun z ↦
    if internalOrderType (kpair.π₂ z) (kpair.π₁ z) ∈ κ then internalOrderType (kpair.π₂ z) (kpair.π₁ z) else ∅
  have hF : ℒₛₑₜ-function₁ F := by
    have hd : ℒₛₑₜ-relation (fun y z : V ↦
      (internalOrderType (kpair.π₂ z) (kpair.π₁ z) ∈ κ ∧ y = internalOrderType (kpair.π₂ z) (kpair.π₁ z)) ∨
      (internalOrderType (kpair.π₂ z) (kpair.π₁ z) ∉ κ ∧ y = ∅)) := by definability
    apply Language.Definable.of_iff hd
    intro v
    by_cases hh : internalOrderType (kpair.π₂ (v 1)) (kpair.π₁ (v 1)) ∈ κ <;> simp [F, hh]
  let f := definableGraph (wellOrderCodes A) F hF
  have hf : f ∈ κ ^ wellOrderCodes A := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro z _
    dsimp only [F]
    split_ifs with hh
    · exact hh
    · exact hκ.regular.2.1 ∅ (by simp))
  apply hκ.no_rank_cofinalMap hC (g := f)
  refine ⟨hf, ?_⟩
  intro α hα
  let := IsOrdinal.of_mem hα
  obtain ⟨D, R, hD, hR, he⟩ := (mem_orderTypesOfSubsets A α).mp
    (ordinal_cardLE_mem_orderTypes (cardLE_of_mem_hartogsNumber (hsub α hα)))
  have hc := (pair_mem_wellOrderCodes A D R).mpr ⟨hD, hR⟩
  refine ⟨⟨D, R⟩ₖ, hc, ?_⟩
  rw [show f ‘ ⟨D, R⟩ₖ = F ⟨D, R⟩ₖ from value_definableGraph _ _ _ hc]
  simp only [F, kpair.π₁_kpair, kpair.π₂_kpair, he, ite_eq_left hα]
  exact subset_refl _

end ZFVP
