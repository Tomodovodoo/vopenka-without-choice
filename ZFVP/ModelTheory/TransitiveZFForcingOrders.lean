import ZFVP.ModelTheory.GroundForcingGeneric

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem prod_val (A B : SetDomain U) : (A ×ˢ B).val = A.val ×ˢ B.val := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  constructor
  · intro hz
    let z' : SetDomain U := ⟨z, (inferInstance : IsTransitive U).mem_trans hz (A ×ˢ B).property⟩
    obtain ⟨x, hx, y, hy, he⟩ := mem_prod_iff.mp (show z' ∈ A ×ˢ B from hz)
    exact mem_prod_iff.mpr ⟨x.val, hx, y.val, hy, (congrArg Subtype.val he).trans (kpair_val U x y)⟩
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hz
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx A.property⟩
    let y' : SetDomain U := ⟨y, (inferInstance : IsTransitive U).mem_trans hy B.property⟩
    have hm : (⟨x', y'⟩ₖ : SetDomain U) ∈ A ×ˢ B := kpair_mem_iff.mpr ⟨hx, hy⟩
    change (⟨x', y'⟩ₖ : SetDomain U).val ∈ (A ×ˢ B).val at hm
    simpa only [kpair_val U] using hm

theorem forcingPreorder_iff (P R : SetDomain U) :
    IsForcingPreorder P R ↔ IsForcingPreorder P.val R.val := by
  unfold IsForcingPreorder
  rw [subset_val_iff U, prod_val U]
  apply and_congr Iff.rfl
  apply and_congr
  · apply forall_mem_val_iff U P
    intro p
    exact kpair_mem_val_iff U p p R
  · apply forall_mem_val_iff U P
    intro p
    apply forall_mem_val_iff U P
    intro q
    apply forall_mem_val_iff U P
    intro r
    simp only [kpair_mem_val_iff U]

theorem forcingTop_iff (P R one : SetDomain U) :
    IsForcingTop P R one ↔ IsForcingTop P.val R.val one.val := by
  unfold IsForcingTop
  apply and_congr Iff.rfl
  apply forall_mem_val_iff U P
  intro p
  exact kpair_mem_val_iff U p one R

theorem forcingPoset_iff (P R : SetDomain U) :
    IsForcingPoset P R ↔ IsForcingPoset P.val R.val := by
  unfold IsForcingPoset
  rw [forcingPreorder_iff U]
  apply and_congr Iff.rfl
  apply forall_mem_val_iff U P
  intro p
  apply forall_mem_val_iff U P
  intro q
  simp only [kpair_mem_val_iff U]
  constructor
  · intro h hpq hqp
    exact congrArg Subtype.val (h hpq hqp)
  · intro h hpq hqp
    exact Subtype.ext (h hpq hqp)

end TransitiveZF
end ZFVP
