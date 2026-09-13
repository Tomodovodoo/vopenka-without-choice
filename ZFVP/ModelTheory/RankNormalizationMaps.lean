import ZFVP.ModelTheory.RankNormalizedNamePool
import ZFVP.ModelTheory.TransitiveZFSparsePair
import ZFVP.ModelTheory.NormalizedTwoStepExtension
import ZFVP.ModelTheory.NormalizedTwoStepIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
section Transitive
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingRestrictedName_val (P R p τ : SetDomain U) :
    (forcingRestrictedName P R p τ).val = forcingRestrictedName P.val R.val p.val τ.val := by
  unfold forcingRestrictedName
  rw [← domain_val U, ← prod_val U]
  apply sep_val U
  intro z _
  rw [kpair_mem_val_iff U, kpair_second_val U]
  apply and_congr_right
  intro _
  apply exists_mem_val_iff U
  intro q
  rw [kpair_mem_val_iff U, kpair_mem_val_iff U, kpair_first_val U, kpair_second_val U]

theorem equivalentSuborderFix_val (N f q : SetDomain U) :
    (equivalentSuborderFix N f q).val = equivalentSuborderFix N.val f.val q.val := by
  classical
  by_cases h : q ∈ N
  · simp only [equivalentSuborderFix, h, show q.val ∈ N.val from h, ↓reduceIte]
  · simp only [equivalentSuborderFix, h, show q.val ∉ N.val from h, ↓reduceIte, value_val_total U]

theorem equivalentSuborderRetraction_val (P N f : SetDomain U) :
    (equivalentSuborderRetraction P N f).val = equivalentSuborderRetraction P.val N.val f.val := by
  unfold equivalentSuborderRetraction
  apply definableGraph_val U
  intro q _
  exact equivalentSuborderFix_val U N f q
end Transitive

variable (ξ : V) [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingGuardedNormalization_val_rank (P R one p τ : SetDomain (hierarchy ξ))
    (hR : IsForcingPreorder P.val R.val) (hone : one.val ∈ P.val)
    (hτ : IsForcingName P.val τ.val) :
    (forcingGuardedNormalization P R one p τ).val =
      forcingGuardedNormalization P.val R.val one.val p.val τ.val := by
  let := hierarchy_transitive ξ
  unfold forcingGuardedNormalization
  rw [forcingLeastRankName_val_rank ξ P R one (forcingRestrictedName P R p τ) hR hone,
    forcingRestrictedName_val (hierarchy ξ)]
  rw [forcingRestrictedName_val (hierarchy ξ)]
  exact forcingRestrictedName_isName hτ

theorem guardedTwoStepCode_val_rank (P R one z : SetDomain (hierarchy ξ))
    (hR : IsForcingPreorder P.val R.val) (hone : one.val ∈ P.val)
    (hτ : IsForcingName P.val (kpair.π₂ z.val)) :
    (guardedTwoStepCode P R one z).val = guardedTwoStepCode P.val R.val one.val z.val := by
  let := hierarchy_transitive ξ
  unfold guardedTwoStepCode
  rw [kpair_val (hierarchy ξ), forcingGuardedNormalization_val_rank ξ P R one _ _ hR hone,
    kpair_first_val (hierarchy ξ), kpair_second_val (hierarchy ξ)]
  rwa [kpair_second_val (hierarchy ξ)]

theorem guardedTwoStepMap_val_rank (P R one δ Q : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hR : IsForcingPreorder P.val R.val) (hone : one.val ∈ P.val) :
    (guardedTwoStepMap P R one δ Q).val = guardedTwoStepMap P.val R.val one.val δ.val Q.val := by
  let := hierarchy_transitive ξ
  unfold guardedTwoStepMap
  rw [← boundedNameTwoStep_val_rank ξ P R δ Q hδ]
  apply definableGraph_val (hierarchy ξ)
  intro z hz
  apply guardedTwoStepCode_val_rank ξ P R one z hR hone
  have hn := (mem_sep_iff.mp hz).2.1
  rw [forcingName_iff (hierarchy ξ), kpair_second_val (hierarchy ξ)] at hn
  exact hn

theorem normalizedTwoStepRetraction_val_rank (P R one δ Q : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hR : IsForcingPreorder P.val R.val) (hone : one.val ∈ P.val) :
    (normalizedTwoStepRetraction P R one δ Q).val =
      normalizedTwoStepRetraction P.val R.val one.val δ.val Q.val := by
  let := hierarchy_transitive ξ
  unfold normalizedTwoStepRetraction
  rw [equivalentSuborderRetraction_val (hierarchy ξ), boundedNameTwoStep_val_rank ξ P R δ Q hδ,
    normalizedNameTwoStep_val_rank ξ P R one δ Q hδ hR hone,
    guardedTwoStepMap_val_rank ξ P R one δ Q hδ hR hone]

theorem normalizedIsomorphismName_val_rank (P Q S top f τ : SetDomain (hierarchy ξ))
    (hf : f.val ∈ Q.val ^ P.val) (hS : IsForcingPreorder Q.val S.val)
    (ht : top.val ∈ Q.val) (hτ : IsForcingName P.val τ.val) :
    (normalizedIsomorphismName Q S top f τ).val =
      normalizedIsomorphismName Q.val S.val top.val f.val τ.val := by
  let := hierarchy_transitive ξ
  have hn := (forcingName_iff (hierarchy ξ) P τ).mpr hτ
  unfold normalizedIsomorphismName
  rw [forcingLeastRankName_val_rank ξ Q S top (nameAction f τ) hS ht,
    nameAction_val (hierarchy ξ) P f τ hn]
  rw [nameAction_val (hierarchy ξ) P f τ hn]
  exact nameAction_isName hf hτ

theorem normalizedTwoStepIsoValue_val_rank (P A B top f z : SetDomain (hierarchy ξ))
    (hf : f.val ∈ A.val ^ P.val) (hB : IsForcingPreorder A.val B.val)
    (ht : top.val ∈ A.val) (hτ : IsForcingName P.val (kpair.π₂ z.val)) :
    (normalizedTwoStepIsoValue A B top f z).val =
      normalizedTwoStepIsoValue A.val B.val top.val f.val z.val := by
  let := hierarchy_transitive ξ
  unfold normalizedTwoStepIsoValue
  rw [kpair_val (hierarchy ξ), value_val_total (hierarchy ξ),
    normalizedIsomorphismName_val_rank ξ P A B top f _ hf hB ht,
    kpair_first_val (hierarchy ξ), kpair_second_val (hierarchy ξ)]
  rwa [kpair_second_val (hierarchy ξ)]

theorem normalizedTwoStepIsoMap_val_rank (P R one δ U A B top f : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hR : IsForcingPreorder P.val R.val) (hone : one.val ∈ P.val)
    (hf : f.val ∈ A.val ^ P.val) (hB : IsForcingPreorder A.val B.val)
    (ht : top.val ∈ A.val) :
    (normalizedTwoStepIsoMap P R one δ U A B top f).val =
      normalizedTwoStepIsoMap P.val R.val one.val δ.val U.val A.val B.val top.val f.val := by
  let := hierarchy_transitive ξ
  unfold normalizedTwoStepIsoMap
  rw [← normalizedNameTwoStep_val_rank ξ P R one δ U hδ hR hone]
  apply definableGraph_val (hierarchy ξ)
  intro z hz
  apply normalizedTwoStepIsoValue_val_rank ξ P A B top f z hf hB ht
  obtain ⟨p, _, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  have hn := (mem_sep_iff.mp hτ).2.1
  rw [forcingName_iff (hierarchy ξ)] at hn
  simpa only [kpair_val (hierarchy ξ), kpair.π₂_kpair] using hn
end TransitiveZF
end ZFVP

