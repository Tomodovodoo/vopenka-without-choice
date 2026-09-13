import ZFVP.ModelTheory.RankNormalizedNamePool
import ZFVP.ModelTheory.TransitiveZFSparsePair
import ZFVP.ModelTheory.SparseNormalizedTwoStep
import ZFVP.ModelTheory.TransitiveZFBoundedForcing
import ZFVP.ModelTheory.NormalizedReverseOrderComparison

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF

set_option maxHeartbeats 600000 in
theorem nameTwoStepOrderOn_val (U : V) [IsTransitive U] [Nonempty (SetDomain U)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (P R S C : SetDomain U) (hR : IsForcingPreorder P R)
    (hS : IsForcingName P S) (hC : ∀ z ∈ C, IsForcingName P (kpair.π₂ z)) :
    (nameTwoStepOrderOn P R S C).val = nameTwoStepOrderOn P.val R.val S.val C.val := by
  unfold nameTwoStepOrderOn
  rw [← prod_val U]
  apply sep_val U
  intro z hz
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, kpair_val U]
  have he := bounded_forcing_iff U P R (kpair.π₁ p) hR boundedPairMemberFormula_bounded
    ![S, kpair.π₂ p, kpair.π₂ q] (by simpa only [Fin.forall_fin_succ, Fin.forall_fin_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, and_true] using And.intro hS ⟨hC p hp, hC q hq⟩)
  change _ ↔ (kpair.π₁ p).val ∈ forcingFormula P.val R.val boundedPairMemberFormula
    (standardTuple ![S.val, (kpair.π₂ p).val, (kpair.π₂ q).val]) at he
  rw [kpair_first_val U, kpair_second_val U, kpair_second_val U] at he
  have hf : ⟨kpair.π₁ p, kpair.π₁ q⟩ₖ ∈ R ↔
      ⟨kpair.π₁ p.val, kpair.π₁ q.val⟩ₖ ∈ R.val := by
    change (⟨kpair.π₁ p, kpair.π₁ q⟩ₖ : SetDomain U).val ∈ R.val ↔ _
    rw [kpair_val U, kpair_first_val U, kpair_first_val U]
  exact and_congr hf he

variable (ξ : V) [IsOrdinal ξ]
  [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparseNormalizedTwoStep_val_rank (a P R one δ Q : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hR : IsForcingPreorder P.val R.val) (hone : one.val ∈ P.val) :
    (sparseNormalizedTwoStep a P R one δ Q).val =
      sparseNormalizedTwoStep a.val P.val R.val one.val δ.val Q.val := by
  let := hierarchy_transitive ξ
  unfold sparseNormalizedTwoStep
  rw [sparsePairCarrier_val (hierarchy ξ), normalizedNamePool_val_rank ξ P R one δ Q hδ hR hone]

theorem sparseNormalizedTwoStepOrder_val_rank (a P R one δ Q S : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hR : IsForcingPreorder P.val R.val) (hone : one.val ∈ P.val)
    (hS : IsForcingName P S) :
    (sparseNormalizedTwoStepOrder a P R one δ Q S).val =
      sparseNormalizedTwoStepOrder a.val P.val R.val one.val δ.val Q.val S.val := by
  let := hierarchy_transitive ξ
  have hC : ∀ z ∈ normalizedNameTwoStep P R one δ Q, IsForcingName P (kpair.π₂ z) := by
    intro z hz
    obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
    simpa only [kpair.π₂_kpair] using (mem_sep_iff.mp hτ).2.1
  unfold sparseNormalizedTwoStepOrder
  rw [forcingPullbackOrder_val (hierarchy ξ),
    sparseNormalizedTwoStep_val_rank ξ a P R one δ Q hδ hR hone,
    nameTwoStepOrderOn_val (hierarchy ξ) P R S _ ((forcingPreorder_iff (hierarchy ξ) P R).mpr hR) hS hC,
    normalizedNameTwoStep_val_rank ξ P R one δ Q hδ hR hone,
    sparsePairDecode_val (hierarchy ξ), normalizedNamePool_val_rank ξ P R one δ Q hδ hR hone]

/-- Canonical reverse-inclusion order agrees on normalized conditions even
without identifying the two models' raw order names. -/
theorem normalizedReverseOrder_val_rank (P R one δ Q : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hQ : IsForcingName P Q) :
    (nameTwoStepOrderOn P R (reverseInclusionOrderName P R Q)
      (normalizedNameTwoStep P R one δ Q)).val =
    nameTwoStepOrderOn P.val R.val (reverseInclusionOrderName P.val R.val Q.val)
      (normalizedNameTwoStep P.val R.val one.val δ.val Q.val) := by
  let := hierarchy_transitive ξ
  let C := normalizedNameTwoStep P R one δ Q
  let D := normalizedNameTwoStep P.val R.val one.val δ.val Q.val
  have hR' := (forcingPreorder_iff (hierarchy ξ) P R).mp hR
  have ht' := (forcingTop_iff (hierarchy ξ) P R one).mp ht
  have hQ' := (forcingName_iff (hierarchy ξ) P Q).mp hQ
  have hC : C.val = D := normalizedNameTwoStep_val_rank ξ P R one δ Q hδ hR' ht'.1
  have hi (z w : SetDomain (hierarchy ξ)) (hz : z ∈ C) (hw : w ∈ C) :
      ⟨z, w⟩ₖ ∈ nameTwoStepOrderOn P R (reverseInclusionOrderName P R Q) C ↔
      ⟨z.val, w.val⟩ₖ ∈ nameTwoStepOrderOn P.val R.val (reverseInclusionOrderName P.val R.val Q.val) D := by
    obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨q, hq, σ, hσ, rfl⟩ := mem_prod_iff.mp hw
    have hpool := normalizedNamePool_val_rank ξ P R one δ Q hδ hR' ht'.1
    have hτ' : τ.val ∈ normalizedNamePool P.val R.val one.val δ.val Q.val := hpool ▸ hτ
    have hσ' : σ.val ∈ normalizedNamePool P.val R.val one.val δ.val Q.val := hpool ▸ hσ
    dsimp only [C, D]
    rw [kpair_val (hierarchy ξ), kpair_val (hierarchy ξ),
      normalizedNameTwoStep_reverse_order_comparison hR ht hQ hp hq hτ hσ,
      normalizedNameTwoStep_reverse_order_comparison hR' ht' hQ' hp hq hτ' hσ']
    apply and_congr (kpair_mem_val_iff (hierarchy ξ) p q R)
    have hb := bounded_forcing_iff (hierarchy ξ) P R p hR isSubsetOf_bounded ![σ, τ]
      (by simpa only [Fin.forall_fin_succ, Fin.forall_fin_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, and_true] using And.intro (mem_sep_iff.mp hσ).2.1 (mem_sep_iff.mp hτ).2.1)
    exact hb
  apply mem_ext
  intro x
  constructor
  · intro hx
    let x' : SetDomain (hierarchy ξ) := ⟨x, (hierarchy_transitive ξ).mem_trans hx
      (nameTwoStepOrderOn P R (reverseInclusionOrderName P R Q) C).property⟩
    have hx' : x' ∈ nameTwoStepOrderOn P R (reverseInclusionOrderName P R Q) C := hx
    obtain ⟨z, hz, w, hw, he⟩ := mem_prod_iff.mp (mem_sep_iff.mp hx').1
    have hh := (hi z w hz hw).mp (he ▸ hx')
    have he' : x = ⟨z.val, w.val⟩ₖ := by simpa only [kpair_val (hierarchy ξ)] using congrArg Subtype.val he
    rwa [he']
  · intro hx
    obtain ⟨z, hz, w, hw, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hx).1
    have hz' : z ∈ C.val := hC.symm ▸ hz
    have hw' : w ∈ C.val := hC.symm ▸ hw
    let z' : SetDomain (hierarchy ξ) := ⟨z, (hierarchy_transitive ξ).mem_trans hz' C.property⟩
    let w' : SetDomain (hierarchy ξ) := ⟨w, (hierarchy_transitive ξ).mem_trans hw' C.property⟩
    have hh := (hi z' w' hz' hw').mpr hx
    change (⟨z', w'⟩ₖ : SetDomain (hierarchy ξ)).val ∈ _ at hh
    simpa only [kpair_val (hierarchy ξ)] using hh

theorem sparseNormalizedReverseOrder_val_rank (a P R one δ Q : SetDomain (hierarchy ξ))
    (hδ : IsOrdinal δ) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hQ : IsForcingName P Q) :
    (sparseNormalizedTwoStepOrder a P R one δ Q (reverseInclusionOrderName P R Q)).val =
      sparseNormalizedTwoStepOrder a.val P.val R.val one.val δ.val Q.val
        (reverseInclusionOrderName P.val R.val Q.val) := by
  let := hierarchy_transitive ξ
  have hR' := (forcingPreorder_iff (hierarchy ξ) P R).mp hR
  have ht' := (forcingTop_iff (hierarchy ξ) P R one).mp ht
  unfold sparseNormalizedTwoStepOrder
  rw [forcingPullbackOrder_val (hierarchy ξ),
    sparseNormalizedTwoStep_val_rank ξ a P R one δ Q hδ hR' ht'.1,
    normalizedReverseOrder_val_rank ξ P R one δ Q hδ hR ht hQ,
    sparsePairDecode_val (hierarchy ξ), normalizedNamePool_val_rank ξ P R one δ Q hδ hR' ht'.1]

end TransitiveZF
end ZFVP
