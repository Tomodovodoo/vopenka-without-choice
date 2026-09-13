import ZFVP.ModelTheory.TransitiveZFNormalizedRecodedCode
import ZFVP.ModelTheory.NormalizedBaseTwoStep
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (ξ : V) [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem retractedBaseTwoStepCode_val_rank (P m z : SetDomain (hierarchy ξ))
    (hτ : IsForcingName P (kpair.π₂ z)) :
    (retractedBaseTwoStepCode m z).val = retractedBaseTwoStepCode m.val z.val := by
  let := hierarchy_transitive ξ
  unfold retractedBaseTwoStepCode
  rw [kpair_val (hierarchy ξ), value_val_total (hierarchy ξ),
    nameAction_val (hierarchy ξ) P m _ hτ,
    kpair_first_val (hierarchy ξ), kpair_second_val (hierarchy ξ)]

theorem retractedBaseTwoStepMap_val_rank (P R δ Q m : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) :
    (retractedBaseTwoStepMap P R δ Q m).val =
      retractedBaseTwoStepMap P.val R.val δ.val Q.val m.val := by
  let := hierarchy_transitive ξ
  unfold retractedBaseTwoStepMap
  rw [← boundedNameTwoStep_val_rank ξ P R δ Q hδ]
  apply definableGraph_val (hierarchy ξ)
  intro z hz
  exact retractedBaseTwoStepCode_val_rank ξ P m z (mem_sep_iff.mp hz).2.1

theorem normalizedBaseTwoStepMap_val_rank (P R N T one δ Q m : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hT : IsForcingPreorder N.val T.val) (hone : one.val ∈ N.val)
    (hQ : IsForcingName P.val Q.val) :
    (normalizedBaseTwoStepMap P R N T one δ Q m).val =
      normalizedBaseTwoStepMap P.val R.val N.val T.val one.val δ.val Q.val m.val := by
  let := hierarchy_transitive ξ
  unfold normalizedBaseTwoStepMap
  rw [compose_val (hierarchy ξ), retractedBaseTwoStepMap_val_rank ξ P R δ Q m hδ,
    normalizedTwoStepRetraction_val_rank ξ N T one δ (nameAction m Q) hδ hT hone,
    nameAction_val (hierarchy ξ) P m Q ((forcingName_iff (hierarchy ξ) P Q).mpr hQ)]
end TransitiveZF
end ZFVP
