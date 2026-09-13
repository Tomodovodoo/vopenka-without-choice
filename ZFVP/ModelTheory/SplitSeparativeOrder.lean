import ZFVP.ModelTheory.ForcingSplitProjection
import ZFVP.ModelTheory.ProjectionSeparativeClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingProjection.separative_monotone {P R Q S π a b : V}
    (h : IsForcingProjection P R Q S π)
    (hab : ⟨a, b⟩ₖ ∈ forcingSeparativeOrder Q S) :
    ⟨π ‘ a, π ‘ b⟩ₖ ∈ forcingSeparativeOrder P R := by
  obtain ⟨ha, hb, hab⟩ := (kpair_mem_forcingSeparativeOrder _ _ _ _).mp hab
  refine (kpair_mem_forcingSeparativeOrder _ _ _ _).mpr
    ⟨function_value_mem h.maps ha, function_value_mem h.maps hb, ?_⟩
  intro p hp hpa
  obtain ⟨c, hc, hca, he⟩ := h.lift a ha p hp hpa
  obtain ⟨d, hd, hdc, hdb⟩ := hab c hc hca
  refine ⟨π ‘ d, function_value_mem h.maps hd, ?_, h.monotone d hd b hb hdb⟩
  simpa only [he] using h.monotone d hd c hc hdc

theorem IsForcingSplitProjection.compatible_section_iff {P R Q S π E q p : V}
    (h : IsForcingSplitProjection P R Q S π E) (hq : q ∈ Q) (hp : p ∈ P) :
    ForcingCompatible Q S q (E ‘ p) ↔ ForcingCompatible P R (π ‘ q) p := by
  constructor
  · rintro ⟨r, hr, hrq, hrp⟩
    exact ⟨π ‘ r, function_value_mem h.projection.maps hr,
      h.projection.monotone r hr q hq hrq, (h.below r hr p hp).mp hrp⟩
  · rintro ⟨a, ha, haq, hap⟩
    obtain ⟨r, hr, hrq, he⟩ := h.projection.lift q hq a ha haq
    exact ⟨r, hr, hrq, (h.below r hr p hp).mpr (he.symm ▸ hap)⟩

/-- The adjunction with a section survives passage to the separative orders. -/
theorem IsForcingSplitProjection.separative_below {P R Q S π E q p : V}
    (h : IsForcingSplitProjection P R Q S π E) (hq : q ∈ Q) (hp : p ∈ P) :
    ⟨q, E ‘ p⟩ₖ ∈ forcingSeparativeOrder Q S ↔
      ⟨π ‘ q, p⟩ₖ ∈ forcingSeparativeOrder P R := by
  constructor
  · intro hqp
    simpa only [h.right_inverse p hp] using h.projection.separative_monotone hqp
  · intro hqp
    refine (kpair_mem_forcingSeparativeOrder _ _ _ _).mpr
      ⟨hq, function_value_mem h.maps hp, ?_⟩
    intro r hr hrq
    apply (h.compatible_section_iff hr hp).mpr
    exact ((kpair_mem_forcingSeparativeOrder _ _ _ _).mp hqp).2.2 _
      (function_value_mem h.projection.maps hr) (h.projection.monotone r hr q hq hrq)

/-- A sequence lying in the range of a split section can be bounded by taking
one lower bound of its projected sequence. -/
theorem IsForcingSplitProjection.separative_bound_of_range {P R Q S π E α f : V}
    [IsOrdinal α] (h : IsForcingSplitProjection P R Q S π E)
    (hc : IsForcingClosedAt P (forcingSeparativeOrder P R) α)
    (hf : IsForcingDescending Q (forcingSeparativeOrder Q S) α f)
    (hrange : ∀ i ∈ α, ∃ p ∈ P, E ‘ p = f ‘ i) :
    ∃ q ∈ Q, ∀ i ∈ α, ⟨q, f ‘ i⟩ₖ ∈ forcingSeparativeOrder Q S := by
  have hcomp := compose_function hf.1 h.projection.maps
  have hdesc : IsForcingDescending P (forcingSeparativeOrder P R) α (compose f π) := by
    refine ⟨hcomp, ?_⟩
    intro i hi j hj
    rw [value_compose_of_mem_function hf.1 h.projection.maps hi,
      value_compose_of_mem_function hf.1 h.projection.maps
        (IsOrdinal.toIsTransitive.mem_trans hj hi)]
    exact h.projection.separative_monotone (hf.2 i hi j hj)
  obtain ⟨p, hp, hb⟩ := hc _ hdesc
  refine ⟨E ‘ p, function_value_mem h.maps hp, ?_⟩
  intro i hi
  obtain ⟨a, ha, hea⟩ := hrange i hi
  rw [← hea]
  apply (h.separative_below (function_value_mem h.maps hp) ha).mpr
  rw [h.right_inverse p hp]
  have hbi := hb i hi
  rwa [value_compose_of_mem_function hf.1 h.projection.maps hi,
    ← hea, h.right_inverse a ha] at hbi

end ZFVP
