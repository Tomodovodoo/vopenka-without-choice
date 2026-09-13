import ZFVP.ModelTheory.ForcingProjectionComposition
import ZFVP.ModelTheory.TwoStepProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An exact forcing projection together with its order-adjoint section. -/
structure IsForcingSplitProjection (P R Q S π E : V) : Prop where
  projection : IsForcingProjection P R Q S π
  maps : E ∈ Q ^ P
  right_inverse : ∀ p ∈ P, π ‘ (E ‘ p) = p
  below : ∀ q ∈ Q, ∀ p ∈ P, ⟨q, E ‘ p⟩ₖ ∈ S ↔ ⟨π ‘ q, p⟩ₖ ∈ R

theorem IsForcingSplitProjection.monotone {P R Q S π E p q : V}
    (h : IsForcingSplitProjection P R Q S π E) (hp : p ∈ P) (hq : q ∈ P)
    (hpq : ⟨p, q⟩ₖ ∈ R) : ⟨E ‘ p, E ‘ q⟩ₖ ∈ S := by
  apply (h.below _ (function_value_mem h.maps hp) q hq).mpr
  rwa [h.right_inverse p hp]

theorem IsForcingSplitProjection.comp {P R Q S U T π E ρ F : V}
    (h : IsForcingSplitProjection P R Q S π E)
    (g : IsForcingSplitProjection Q S U T ρ F) :
    IsForcingSplitProjection P R U T (compose ρ π) (compose E F) := by
  refine ⟨h.projection.comp g.projection, compose_function h.maps g.maps, ?_, ?_⟩
  · intro p hp
    rw [value_compose_of_mem_function h.maps g.maps hp,
      value_compose_of_mem_function g.projection.maps h.projection.maps
        (function_value_mem g.maps (function_value_mem h.maps hp)),
      g.right_inverse _ (function_value_mem h.maps hp), h.right_inverse p hp]
  · intro u hu p hp
    rw [value_compose_of_mem_function h.maps g.maps hp,
      g.below u hu _ (function_value_mem h.maps hp),
      h.below _ (function_value_mem g.projection.maps hu) p hp,
      value_compose_of_mem_function g.projection.maps h.projection.maps hu]

theorem IsForcingSplitProjection.generic_iff_section {P R Q S π E p : V}
    (h : IsForcingSplitProjection P R Q S π E) (hR : IsForcingPreorder P R)
    {G : Set V} (hG : IsExternalForcingFilter Q S G) (hp : p ∈ P) :
    p ∈ forcingProjectionGeneric P R π G ↔ E ‘ p ∈ G := by
  constructor
  · rintro ⟨_, q, hq, hqp⟩
    exact hG.2.2.1 q hq _ (function_value_mem h.maps hp)
      ((h.below q (hG.1 q hq) p hp).mpr hqp)
  · intro he
    exact ⟨hp, E ‘ p, he, (h.right_inverse p hp).symm ▸ hR.2.1 p hp⟩

noncomputable def twoStepSection (P t : V) : V :=
  definableGraph P (fun p ↦ ⟨p, t⟩ₖ) (by definability)

theorem twoStepSection_value {P t p : V} (hp : p ∈ P) :
    (twoStepSection P t) ‘ p = ⟨p, t⟩ₖ := value_definableGraph _ _ _ hp

theorem twoStep_splitProjection {P R Q S t one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) :
    IsForcingSplitProjection P R (twoStepConditions P R Q t) (twoStepOrder P R Q S t)
      (twoStepProjection P R Q t) (twoStepSection P t) := by
  refine ⟨twoStep_projection hR htop h,
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hp ↦ twoStep_section_mem hR htop h hp), ?_, ?_⟩
  · intro p hp
    rw [twoStepSection_value hp, twoStepProjection_value (twoStep_section_mem hR htop h hp),
      kpair.π₁_kpair]
  · intro q hq p hp
    rw [twoStepSection_value hp, twoStepProjection_value hq]
    exact twoStep_below_section hR htop h hq hp

end ZFVP
