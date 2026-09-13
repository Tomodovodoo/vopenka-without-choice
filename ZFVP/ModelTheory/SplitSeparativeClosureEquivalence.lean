import ZFVP.ModelTheory.SplitClosureDownward

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsForcingSplitProjection
variable {P R Q S π E : V} (h : IsForcingSplitProjection P R Q S π E)
  (ho : ∀ a ∈ Q, ∀ b ∈ Q, ⟨π ‘ a, π ‘ b⟩ₖ ∈ R ↔ ⟨a, b⟩ₖ ∈ S)

include h ho in
theorem compatible_iff_of_order_reflecting {a b : V} (ha : a ∈ Q) (hb : b ∈ Q) :
    ForcingCompatible Q S a b ↔ ForcingCompatible P R (π ‘ a) (π ‘ b) := by
  constructor
  · rintro ⟨c, hc, hca, hcb⟩
    exact ⟨π ‘ c, function_value_mem h.projection.maps hc,
      (ho c hc a ha).mpr hca, (ho c hc b hb).mpr hcb⟩
  · rintro ⟨p, hp, hpa, hpb⟩
    have he := function_value_mem h.maps hp
    refine ⟨E ‘ p, he, (ho _ he a ha).mp ?_, (ho _ he b hb).mp ?_⟩
    · rwa [h.right_inverse p hp]
    · rwa [h.right_inverse p hp]

include h ho in
theorem separative_iff_of_order_reflecting {a b : V} (ha : a ∈ Q) (hb : b ∈ Q) :
    ⟨a, b⟩ₖ ∈ forcingSeparativeOrder Q S ↔
      ⟨π ‘ a, π ‘ b⟩ₖ ∈ forcingSeparativeOrder P R :=
  h.projection.separative_iff
    (fun _ ha _ hb ↦ h.compatible_iff_of_order_reflecting ho ha hb) ha hb

include h ho in
theorem separative_closedAt_iff_of_order_reflecting {α : V} [IsOrdinal α] :
    IsForcingClosedAt Q (forcingSeparativeOrder Q S) α ↔
      IsForcingClosedAt P (forcingSeparativeOrder P R) α := by
  constructor
  · exact h.separative_closedAt_base
  · exact h.projection.separative_closedAt
      (fun _ ha _ hb ↦ h.compatible_iff_of_order_reflecting ho ha hb)
      (fun p hp ↦ ⟨E ‘ p, function_value_mem h.maps hp, h.right_inverse p hp⟩)

include h ho in
theorem separative_closedBelow_iff_of_order_reflecting {κ : V} [IsOrdinal κ] :
    IsForcingClosedBelow Q (forcingSeparativeOrder Q S) κ ↔
      IsForcingClosedBelow P (forcingSeparativeOrder P R) κ := by
  apply forall₂_congr
  intro α hα
  let := IsOrdinal.of_mem hα
  exact h.separative_closedAt_iff_of_order_reflecting ho

end IsForcingSplitProjection
end ZFVP

