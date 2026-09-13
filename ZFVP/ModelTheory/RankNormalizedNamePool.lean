import ZFVP.ModelTheory.ForcingLeastRankNameLocal
import ZFVP.ModelTheory.NormalizedTwoStepComparison
import ZFVP.ModelTheory.TransitiveZFRankOperations
import ZFVP.ModelTheory.TransitiveZFWoodinStage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF
variable (ξ : V) [IsOrdinal ξ]
  [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem normalizedNamePool_val_rank (P R one δ Q : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hR : IsForcingPreorder P.val R.val) (hone : one.val ∈ P.val) :
    (normalizedNamePool P R one δ Q).val =
      normalizedNamePool P.val R.val one.val δ.val Q.val := by
  let := hierarchy_transitive ξ
  unfold normalizedNamePool
  rw [← rank_hierarchy_val δ hδ]
  apply sep_val (hierarchy ξ)
  intro τ _
  rw [forcingName_iff (hierarchy ξ) P τ]
  apply and_congr_right
  intro hτ
  have he : forcingLeastRankName P R one τ = τ ↔
      forcingLeastRankName P.val R.val one.val τ.val = τ.val := by
    rw [← forcingLeastRankName_val_rank ξ P R one τ hR hone hτ]
    exact ⟨congrArg Subtype.val, Subtype.ext⟩
  rw [he]
  change (_ ∧ one.val ∈ (atomicMembership P R τ Q).val) ↔ _
  rw [atomicMembership_val (hierarchy ξ)]

theorem normalizedNameTwoStep_val_rank (P R one δ Q : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hR : IsForcingPreorder P.val R.val) (hone : one.val ∈ P.val) :
    (normalizedNameTwoStep P R one δ Q).val =
      normalizedNameTwoStep P.val R.val one.val δ.val Q.val := by
  let := hierarchy_transitive ξ
  unfold normalizedNameTwoStep
  rw [prod_val (hierarchy ξ), normalizedNamePool_val_rank ξ P R one δ Q hδ hR hone]

theorem boundedNameTwoStep_val_rank (P R δ Q : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) :
    (boundedNameTwoStep P R δ Q).val = boundedNameTwoStep P.val R.val δ.val Q.val := by
  let := hierarchy_transitive ξ
  unfold boundedNameTwoStep
  rw [← rank_hierarchy_val δ hδ, ← prod_val (hierarchy ξ)]
  apply sep_val (hierarchy ξ)
  intro z _
  rw [forcingName_iff (hierarchy ξ) P (kpair.π₂ z), kpair_second_val (hierarchy ξ)]
  change (_ ∧ (kpair.π₁ z).val ∈ (atomicMembership P R (kpair.π₂ z) Q).val) ↔ _
  rw [atomicMembership_val (hierarchy ξ), kpair_first_val (hierarchy ξ), kpair_second_val (hierarchy ξ)]

end TransitiveZF
end ZFVP
