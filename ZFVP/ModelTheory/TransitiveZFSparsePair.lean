import ZFVP.ModelTheory.SparsePairPresentation
import ZFVP.ModelTheory.TransitiveZFRankOperations
import ZFVP.ModelTheory.TransitiveZFWoodinSourceCode
import ZFVP.ModelTheory.TransitiveZFBoundedQuantifiers

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem isSparseFunctionOn_iff (a p : SetDomain U) :
    IsSparseFunctionOn a p ↔ IsSparseFunctionOn a.val p.val := by
  unfold IsSparseFunctionOn
  rw [isFunction_iff U, ← domain_val U, ← subset_val_iff U]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_mem_val_iff U
  intro x
  rw [← value_val_total U]
  have he : p ‘ x = ∅ ↔ (p ‘ x).val = (∅ : V) := by
    rw [← empty_val U]
    exact ⟨congrArg Subtype.val, Subtype.ext⟩
  exact not_congr he

theorem sparseAppend_val (a p τ : SetDomain U) :
    (sparseAppend a p τ).val = sparseAppend a.val p.val τ.val := by
  classical
  have he : τ = ∅ ↔ τ.val = (∅ : V) := by
    rw [← empty_val U]
    exact ⟨congrArg Subtype.val, Subtype.ext⟩
  by_cases hτ : τ = ∅
  · simp only [sparseAppend, hτ, empty_val U, ↓reduceIte]
  · simp only [sparseAppend, hτ, mt he.mpr hτ, ↓reduceIte, insert_val U, kpair_val U]

theorem mem_sparsePairCarrier_val_iff (a P W q : SetDomain U) :
    q ∈ sparsePairCarrier a P W ↔ q.val ∈ sparsePairCarrier a.val P.val W.val := by
  rw [mem_sparsePairCarrier_iff, mem_sparsePairCarrier_iff,
    isSparseFunctionOn_iff U, succ_val U]
  change (_ ∧ (q ↾ a).val ∈ P.val ∧ (q ‘ a).val ∈ W.val) ↔ _
  rw [restrict_val U, value_val_total U]

/-- Sparse conditions reconstruct from a prefix and coordinate already in the
model, so comparison does not require absoluteness of its power-set operation. -/
theorem sparsePairCarrier_val (a P W : SetDomain U) :
    (sparsePairCarrier a P W).val = sparsePairCarrier a.val P.val W.val := by
  apply mem_ext
  intro q
  constructor
  · intro hq
    let q' : SetDomain U := ⟨q, (inferInstance : IsTransitive U).mem_trans hq (sparsePairCarrier a P W).property⟩
    exact (mem_sparsePairCarrier_val_iff U a P W q').mp hq
  · intro hq
    obtain ⟨hs, hp, hτ⟩ := mem_sparsePairCarrier_iff.mp hq
    let p : SetDomain U := ⟨q ↾ a.val, (inferInstance : IsTransitive U).mem_trans hp P.property⟩
    let τ : SetDomain U := ⟨q ‘ a.val, (inferInstance : IsTransitive U).mem_trans hτ W.property⟩
    have he : (sparseAppend a p τ).val = q := by
      rw [sparseAppend_val U]
      exact sparseAppend_reconstruct hs
    have hh := (mem_sparsePairCarrier_val_iff U a P W (sparseAppend a p τ)).mpr (he.symm ▸ hq)
    change (sparseAppend a p τ).val ∈ (sparsePairCarrier a P W).val at hh
    rwa [he] at hh

theorem sparsePairDecodeValue_val (a q : SetDomain U) :
    (sparsePairDecodeValue a q).val = sparsePairDecodeValue a.val q.val := by
  unfold sparsePairDecodeValue
  rw [kpair_val U, restrict_val U, value_val_total U]

theorem sparsePairDecode_val (a P W : SetDomain U) :
    (sparsePairDecode a P W).val = sparsePairDecode a.val P.val W.val := by
  unfold sparsePairDecode
  rw [← sparsePairCarrier_val U]
  apply definableGraph_val U
  intro q _
  exact sparsePairDecodeValue_val U a q

theorem converseGraph_val (f : SetDomain U) :
    (converseGraph f).val = converseGraph f.val := by
  unfold converseGraph
  rw [← range_val U, ← domain_val U, ← prod_val U]
  apply sep_val U
  intro z _
  change (⟨kpair.π₂ z, kpair.π₁ z⟩ₖ : SetDomain U).val ∈ f.val ↔ _
  rw [kpair_val U, kpair_second_val U, kpair_first_val U]

theorem sparsePairEncode_val (a P W : SetDomain U) :
    (sparsePairEncode a P W).val = sparsePairEncode a.val P.val W.val := by
  unfold sparsePairEncode
  rw [converseGraph_val U, sparsePairDecode_val U]

theorem forcingPullbackOrder_val (Q R π : SetDomain U) :
    (forcingPullbackOrder Q R π).val = forcingPullbackOrder Q.val R.val π.val := by
  unfold forcingPullbackOrder
  rw [← prod_val U]
  apply sep_val U
  intro z _
  change (⟨π ‘ (kpair.π₁ z), π ‘ (kpair.π₂ z)⟩ₖ : SetDomain U).val ∈ R.val ↔ _
  rw [kpair_val U, value_val_total U, value_val_total U, kpair_first_val U, kpair_second_val U]

end TransitiveZF
end ZFVP
