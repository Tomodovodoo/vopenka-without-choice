import ZFVP.ModelTheory.WoodinSparseCoordinateComparison

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ p q : V} [IsOrdinal θ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ

theorem woodinSparseStageCode_coordinate_outside
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {a : V} [IsOrdinal a] (hp : p ∈ P) (hpd : domain p ⊆ a) (hqd : domain q ⊆ a) :
    SparseCoordinateComparison P R a p q :=
  woodinSparseStageCode_coordinate_empty hΩ hAC hθ hp
    (value_eq_empty_of_not_mem_domain (fun h ↦ mem_irrefl a (hpd a h)))
    (value_eq_empty_of_not_mem_domain (fun h ↦ mem_irrefl a (hqd a h)))

private theorem ordinal_subset_of_outside {a b : V} [IsOrdinal a] [IsOrdinal b]
    (h : a ∉ b) : b ⊆ a := by
  rcases IsOrdinal.mem_trichotomy b a with hba | he | hab
  · exact IsOrdinal.toIsTransitive.transitive _ hba
  · exact he ▸ subset_refl b
  · exact (h hab).elim

theorem woodinSparseStageCode_coordinates_cut_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {a : V} [IsOrdinal a] (hp : p ∈ sparseCarrierCut P a) (hq : q ∈ sparseCarrierCut P a) :
    SparseOrderCoordinates P R (succ (woodinSourceIndex θ)) p q ↔ SparseOrderCoordinates P R a p q := by
  have hp' := mem_sparseCarrierCut_iff.mp hp
  have hq' := mem_sparseCarrierCut_iff.mp hq
  have hpd := (woodinSparseStageCode_sparse hΩ hAC hθ hp'.1).2.1
  have hqd := (woodinSparseStageCode_sparse hΩ hAC hθ hq'.1).2.1
  constructor
  · intro h b hb
    let := IsOrdinal.of_mem hb
    by_cases hbc : b ∈ succ (woodinSourceIndex θ)
    · exact h b hbc
    · exact woodinSparseStageCode_coordinate_outside hΩ hAC hθ hp'.1
        (subset_trans hpd (ordinal_subset_of_outside hbc))
        (subset_trans hqd (ordinal_subset_of_outside hbc))
  · intro h b hb
    let := IsOrdinal.of_mem hb
    by_cases hba : b ∈ a
    · exact h b hba
    · exact woodinSparseStageCode_coordinate_outside hΩ hAC hθ hp'.1
        (subset_trans hp'.2 (ordinal_subset_of_outside hba))
        (subset_trans hq'.2 (ordinal_subset_of_outside hba))

end ZFVP
