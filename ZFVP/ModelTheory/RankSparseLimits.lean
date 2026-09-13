import ZFVP.ModelTheory.TransitiveZFSparsePair
import ZFVP.ModelTheory.TransitiveZFLimitColumns
import ZFVP.ModelTheory.WoodinSparseDirectBase

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparseThreadCarrier_val (θ A b P B : SetDomain U)
    (hpow : (℘ (⋃ˢ B)).val = ℘ (⋃ˢ B.val)) :
    (sparseThreadCarrier θ A b P B).val = sparseThreadCarrier θ.val A.val b.val P.val B.val := by
  unfold sparseThreadCarrier
  rw [← hpow]
  apply sep_val U
  intro q _
  apply and_congr (isSparseFunctionOn_iff U A q)
  apply forall_mem_val_iff U θ
  intro i
  change (q ↾ (b ‘ i)).val ∈ (P ‘ i).val ↔ _
  rw [restrict_val U, value_val_total U, value_val_total U]

theorem sparseThreadOrder_val (θ b R C : SetDomain U) :
    (sparseThreadOrder θ b R C).val = sparseThreadOrder θ.val b.val R.val C.val := by
  unfold sparseThreadOrder
  rw [← prod_val U]
  apply sep_val U
  intro z _
  apply forall_mem_val_iff U θ
  intro i
  change (⟨(kpair.π₁ z) ↾ (b ‘ i), (kpair.π₂ z) ↾ (b ‘ i)⟩ₖ : SetDomain U).val ∈ (R ‘ i).val ↔ _
  simp only [kpair_val U, restrict_val U, value_val_total U, kpair_first_val U, kpair_second_val U]

theorem sparseThreadDecodeValue_val (θ b q : SetDomain U) :
    (sparseThreadDecodeValue θ b q).val = sparseThreadDecodeValue θ.val b.val q.val := by
  unfold sparseThreadDecodeValue
  apply definableGraph_val U
  intro i _
  rw [restrict_val U, value_val_total U]

theorem sparseThreadDecode_val (θ A b P B : SetDomain U)
    (hpow : (℘ (⋃ˢ B)).val = ℘ (⋃ˢ B.val)) :
    (sparseThreadDecode θ A b P B).val = sparseThreadDecode θ.val A.val b.val P.val B.val := by
  unfold sparseThreadDecode
  rw [← sparseThreadCarrier_val U θ A b P B hpow]
  apply definableGraph_val U
  intro q _
  exact sparseThreadDecodeValue_val U θ b q
theorem sparseRestrictionThreads_val (θ b P B : SetDomain U)
    (hfun : (B ^ θ).val = B.val ^ θ.val) :
    (sparseRestrictionThreads θ b P B).val = sparseRestrictionThreads θ.val b.val P.val B.val := by
  unfold sparseRestrictionThreads
  rw [← hfun]
  apply sep_val U
  intro t _
  apply and_congr
  · apply forall_mem_val_iff U θ
    intro i
    rw [isSparseFunctionOn_iff U]
    change (_ ∧ (t ‘ i).val ∈ (P ‘ i).val) ↔ _
    simp only [value_val_total U]
  · apply forall_mem_val_iff U θ
    intro i
    apply forall_mem_val_iff U θ
    intro j
    have he (x y : SetDomain U) : x = y ↔ x.val = y.val := ⟨congrArg Subtype.val, Subtype.ext⟩
    rw [he]
    simp only [restrict_val U, value_val_total U]

theorem sparseThreadEncode_val (θ b P B : SetDomain U)
    (hfun : (B ^ θ).val = B.val ^ θ.val) :
    (sparseThreadEncode θ b P B).val = sparseThreadEncode θ.val b.val P.val B.val := by
  unfold sparseThreadEncode
  rw [← sparseRestrictionThreads_val U θ b P B hfun]
  apply definableGraph_val U
  intro t _
  rw [sUnion_val U, range_val U]

theorem woodinSparseBounds_val (θ : SetDomain U) [IsOrdinal θ] :
    (woodinSparseBounds θ).val = woodinSparseBounds θ.val := by
  unfold woodinSparseBounds
  apply definableGraph_val U
  intro i hi
  rw [succ_val U, woodinSourceIndex_val U i (IsOrdinal.of_mem hi)]

variable (ξ : V) [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparseThreadCarrier_val_rank (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ A b P B : SetDomain (hierarchy ξ)) :
    (sparseThreadCarrier θ A b P B).val = sparseThreadCarrier θ.val A.val b.val P.val B.val := by
  let := hierarchy_transitive ξ
  apply sparseThreadCarrier_val (hierarchy ξ)
  rw [rank_power_val hs, sUnion_val (hierarchy ξ)]

theorem woodinSparseInverseBase_val_rank (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ c : SetDomain (hierarchy ξ)) [IsOrdinal θ] :
    (woodinSparseInverseBase θ c).val = woodinSparseInverseBase θ.val c.val := by
  let := hierarchy_transitive ξ
  unfold woodinSparseInverseBase
  rw [sparseThreadCarrier_val_rank ξ hs, woodinSparseBounds_val (hierarchy ξ),
    forcingCodeP_val (hierarchy ξ), forcingCodeUniverse_val (hierarchy ξ)]

theorem woodinSparseInverseOrder_val_rank (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ c : SetDomain (hierarchy ξ)) [IsOrdinal θ] :
    (woodinSparseInverseOrder θ c).val = woodinSparseInverseOrder θ.val c.val := by
  let := hierarchy_transitive ξ
  unfold woodinSparseInverseOrder
  rw [sparseThreadOrder_val (hierarchy ξ), woodinSparseBounds_val (hierarchy ξ),
    forcingCodeR_val (hierarchy ξ), woodinSparseInverseBase_val_rank ξ hs]

theorem woodinSparseInverseFlatten_val_rank (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ c : SetDomain (hierarchy ξ)) [IsOrdinal θ] :
    (woodinSparseInverseFlatten θ c).val = woodinSparseInverseFlatten θ.val c.val := by
  let := hierarchy_transitive ξ
  unfold woodinSparseInverseFlatten
  rw [sparseThreadEncode_val (hierarchy ξ) _ _ _ _ (rank_functionSet_val hs _ _),
    woodinSparseBounds_val (hierarchy ξ), forcingCodeP_val (hierarchy ξ), forcingCodeUniverse_val (hierarchy ξ)]

theorem woodinSparseDirectBase_val_rank (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ c : SetDomain (hierarchy ξ)) [IsOrdinal θ] :
    (woodinSparseDirectBase θ c).val = woodinSparseDirectBase θ.val c.val := by
  let := hierarchy_transitive ξ
  unfold woodinSparseDirectBase
  rw [← woodinSparseInverseBase_val_rank ξ hs]
  apply sep_val (hierarchy ξ)
  intro q _
  have he (i : SetDomain (hierarchy ξ)) (hi : i ∈ θ) :
      domain q ⊆ succ (woodinSourceIndex i) ↔ domain q.val ⊆ succ (woodinSourceIndex i.val) := by
    rw [subset_val_iff (hierarchy ξ), domain_val (hierarchy ξ), succ_val (hierarchy ξ),
      woodinSourceIndex_val (hierarchy ξ) i (IsOrdinal.of_mem hi)]
  constructor
  · rintro ⟨i, hi, hq⟩
    exact ⟨i.val, hi, (he i hi).mp hq⟩
  · rintro ⟨i, hi, hq⟩
    let i' : SetDomain (hierarchy ξ) := ⟨i, (hierarchy_transitive ξ).mem_trans hi θ.property⟩
    exact ⟨i', hi, (he i' hi).mpr hq⟩

theorem woodinSparseDirectOrder_val_rank (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ c : SetDomain (hierarchy ξ)) [IsOrdinal θ] :
    (woodinSparseDirectOrder θ c).val = woodinSparseDirectOrder θ.val c.val := by
  let := hierarchy_transitive ξ
  unfold woodinSparseDirectOrder
  rw [sparseThreadOrder_val (hierarchy ξ), woodinSparseBounds_val (hierarchy ξ),
    forcingCodeR_val (hierarchy ξ), woodinSparseDirectBase_val_rank ξ hs]

theorem woodinSparseDirectDecode_val_rank (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ c : SetDomain (hierarchy ξ)) [IsOrdinal θ] :
    (woodinSparseDirectDecode θ c).val = woodinSparseDirectDecode θ.val c.val := by
  let := hierarchy_transitive ξ
  unfold woodinSparseDirectDecode
  rw [← woodinSparseDirectBase_val_rank ξ hs]
  apply definableGraph_val (hierarchy ξ)
  intro q _
  rw [sparseThreadDecodeValue_val (hierarchy ξ), woodinSparseBounds_val (hierarchy ξ)]

theorem woodinSparseDirectFlatten_val_rank (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ c : SetDomain (hierarchy ξ)) :
    (woodinSparseDirectFlatten θ c).val = woodinSparseDirectFlatten θ.val c.val := by
  let := hierarchy_transitive ξ
  unfold woodinSparseDirectFlatten
  have hd := rank_forcingDirectLimit_val hs θ (forcingCodeP c) (forcingCodeπ c)
    (forcingCodeE c) (forcingCodeUniverse c)
  rw [forcingCodeP_val (hierarchy ξ), forcingCodeπ_val (hierarchy ξ),
    forcingCodeE_val (hierarchy ξ), forcingCodeUniverse_val (hierarchy ξ)] at hd
  rw [← hd]
  apply definableGraph_val (hierarchy ξ)
  intro t _
  rw [sUnion_val (hierarchy ξ), range_val (hierarchy ξ)]

end TransitiveZF
end ZFVP



