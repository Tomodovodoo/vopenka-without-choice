import ZFVP.ModelTheory.TransitiveZFBoundedQuantifiers
import ZFVP.ModelTheory.TransitiveZFValues
import ZFVP.SetTheory.WoodinSuccessorCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sInter_val (A : SetDomain U) : (⋂ˢ A).val = ⋂ˢ A.val := by
  unfold sInter
  rw [← sUnion_val U A]
  apply sep_val U
  intro x _
  exact forall_mem_val_iff U A (fun y ↦ x ∈ y) (fun y ↦ x.val ∈ y) (fun _ ↦ Iff.rfl)

theorem kpair_first_val (x : SetDomain U) : (kpair.π₁ x).val = kpair.π₁ x.val := by
  simp only [kpair.π₁, sUnion_val U, sInter_val U]

theorem kpair_second_val (x : SetDomain U) : (kpair.π₂ x).val = kpair.π₂ x.val := by
  unfold kpair.π₂
  rw [sUnion_val U]
  congr 1
  rw (config := {occs := .pos [1]}) [← sUnion_val U x]
  apply sep_val U
  intro z _
  change (z.val ∈ (⋂ˢ x).val → ⋃ˢ x = ⋂ˢ x) ↔ _
  rw [sInter_val U]
  apply imp_congr_right
  intro _
  constructor
  · intro he
    simpa only [sUnion_val U, sInter_val U] using congrArg Subtype.val he
  · intro he
    apply Subtype.ext
    simpa only [sUnion_val U, sInter_val U] using he

theorem woodinStageCode_val (P R one κ : SetDomain U) :
    (woodinStageCode P R one κ).val = woodinStageCode P.val R.val one.val κ.val := by
  simp only [woodinStageCode, kpair_val U]

theorem woodinStagePoset_val (x : SetDomain U) : (woodinStagePoset x).val = woodinStagePoset x.val := by
  simp only [woodinStagePoset, kpair_first_val U]

theorem woodinStageOrder_val (x : SetDomain U) : (woodinStageOrder x).val = woodinStageOrder x.val := by
  simp only [woodinStageOrder, kpair_first_val U, kpair_second_val U]

theorem woodinStageTop_val (x : SetDomain U) : (woodinStageTop x).val = woodinStageTop x.val := by
  simp only [woodinStageTop, kpair_first_val U, kpair_second_val U]

theorem woodinStageCardinal_val (x : SetDomain U) : (woodinStageCardinal x).val = woodinStageCardinal x.val := by
  simp only [woodinStageCardinal, kpair_second_val U]

end TransitiveZF
end ZFVP
