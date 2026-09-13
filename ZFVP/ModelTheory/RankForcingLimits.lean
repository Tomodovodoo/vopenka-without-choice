import ZFVP.ModelTheory.TransitiveZFIterationHistory
import ZFVP.ModelTheory.RankForcingNameHierarchy

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_functionSet_val {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
    [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (A B : SetDomain (hierarchy ξ)) :
    (B ^ A).val = B.val ^ A.val := by
  let := hierarchy_transitive ξ
  apply mem_ext
  intro f
  constructor
  · intro hf
    let f' : SetDomain (hierarchy ξ) := ⟨f, (hierarchy_transitive ξ).mem_trans hf (B ^ A).property⟩
    exact (TransitiveZF.function_iff (hierarchy ξ) f' A B).mp hf
  · intro hf
    let f' : SetDomain (hierarchy ξ) := ⟨f, (hierarchy_transitive ξ).mem_trans hf
      (function_mem_hierarchy_limit hs A.property B.property)⟩
    exact show f' ∈ B ^ A from (TransitiveZF.function_iff (hierarchy ξ) f' A B).mpr hf

namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [IsTransitive U]
  [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eq_iff_val (a b : SetDomain U) : a = b ↔ a.val = b.val :=
  ⟨congrArg Subtype.val, Subtype.ext⟩

theorem coherentThread_iff (θ π f : SetDomain U) :
    IsCoherentThread θ π f ↔ IsCoherentThread θ.val π.val f.val := by
  unfold IsCoherentThread
  apply forall_mem_val_iff U θ
  intro j
  apply forall_mem_val_iff U j
  intro i
  apply imp_congr_right
  intro _
  simp only [eq_iff_val U, value_val_total U, kpair_val U]

theorem threadSupport_iff (θ E f k : SetDomain U) :
    IsThreadSupport θ E f k ↔ IsThreadSupport θ.val E.val f.val k.val := by
  unfold IsThreadSupport
  apply and_congr Iff.rfl
  apply forall_mem_val_iff U θ
  intro j
  apply imp_congr (subset_val_iff U k j)
  simp only [eq_iff_val U, value_val_total U, kpair_val U]

theorem forcingInverseLimit_val (θ P π A : SetDomain U)
    (hfun : (A ^ θ).val = A.val ^ θ.val) :
    (forcingInverseLimit θ P π A).val = forcingInverseLimit θ.val P.val π.val A.val := by
  unfold forcingInverseLimit
  rw [← hfun]
  apply sep_val U
  intro f _
  apply and_congr ?_ (coherentThread_iff U θ π f)
  apply forall_mem_val_iff U θ
  intro i
  change (f ‘ i).val ∈ (P ‘ i).val ↔ _
  rw [value_val_total U, value_val_total U]

theorem forcingDirectLimit_val (θ P π E A : SetDomain U)
    (hfun : (A ^ θ).val = A.val ^ θ.val) :
    (forcingDirectLimit θ P π E A).val = forcingDirectLimit θ.val P.val π.val E.val A.val := by
  unfold forcingDirectLimit
  rw [← forcingInverseLimit_val U θ P π A hfun]
  apply sep_val U
  intro f _
  change (∃ k, k ∈ θ ∧ _) ↔ (∃ k, k ∈ θ.val ∧ _)
  apply exists_mem_val_iff U θ
  intro k
  apply forall_mem_val_iff U θ
  intro j
  apply imp_congr (subset_val_iff U k j)
  simp only [eq_iff_val U, value_val_total U, kpair_val U]

theorem forcingThreadOrder_val (θ R C : SetDomain U) :
    (forcingThreadOrder θ R C).val = forcingThreadOrder θ.val R.val C.val := by
  unfold forcingThreadOrder
  rw [← prod_val U]
  apply sep_val U
  intro z _
  apply forall_mem_val_iff U θ
  intro i
  change (⟨(kpair.π₁ z) ‘ i, (kpair.π₂ z) ‘ i⟩ₖ : SetDomain U).val ∈ (R ‘ i).val ↔ _
  simp only [kpair_val U, value_val_total U, kpair_first_val U, kpair_second_val U]

end TransitiveZF

theorem rank_forcingInverseLimit_val {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
    [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (θ P π A : SetDomain (hierarchy ξ)) :
    (forcingInverseLimit θ P π A).val = forcingInverseLimit θ.val P.val π.val A.val := by
  let := hierarchy_transitive ξ
  exact TransitiveZF.forcingInverseLimit_val (hierarchy ξ) θ P π A (rank_functionSet_val hs θ A)

theorem rank_forcingDirectLimit_val {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
    [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (θ P π E A : SetDomain (hierarchy ξ)) :
    (forcingDirectLimit θ P π E A).val = forcingDirectLimit θ.val P.val π.val E.val A.val := by
  let := hierarchy_transitive ξ
  exact TransitiveZF.forcingDirectLimit_val (hierarchy ξ) θ P π E A (rank_functionSet_val hs θ A)

end ZFVP
