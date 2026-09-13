import ZFVP.ModelTheory.RelativeAutomorphismGeneric
import ZFVP.SetTheory.WoodinCollapseDisplacement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An actual collapse generic can be moved to contain any specified condition.
The inverse ground automorphism recovers the original generic. -/
theorem woodinCollapse_generic_movement {κ δ t : V} {G : Set V}
    (hκ : IsRegularCardinal κ) (ht : t ∈ woodinCollapse κ δ)
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    ∃ f, IsForcingAutomorphism (woodinCollapse κ δ) (woodinCollapseOrder κ δ) f ∧
      IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
        (forcingProjectionGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) f G) ∧
      t ∈ forcingProjectionGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) f G ∧
      forcingProjectionGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) (converseGraph f)
        (forcingProjectionGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) f G) = G := by
  obtain ⟨a, ha⟩ := hG.1.2.1
  have hR := (woodinCollapse_poset κ δ).1
  have hA : ∀ f ∈ forcingAutomorphisms (woodinCollapse κ δ) (woodinCollapseOrder κ δ),
      IsForcingAutomorphism (woodinCollapse κ δ) (woodinCollapseOrder κ δ) f :=
    fun f hf ↦ (mem_forcingAutomorphisms_iff _ _ f).mp hf
  have hmove : ∀ p ∈ woodinCollapse κ δ, ⟨p, a⟩ₖ ∈ woodinCollapseOrder κ δ →
      ∃ f ∈ forcingAutomorphisms (woodinCollapse κ δ) (woodinCollapseOrder κ δ),
        ForcingCompatible (woodinCollapse κ δ) (woodinCollapseOrder κ δ) (f ‘ p) t := by
    intro p hp _
    obtain ⟨f, hf, hcompat⟩ := woodinCollapse_weak_homogeneous hκ hp ht
    exact ⟨f, (mem_forcingAutomorphisms_iff _ _ _).mpr hf, hcompat⟩
  obtain ⟨f, hfA, hfG, htG⟩ := externalGeneric_move_automorphism hR hG ht ha hA hmove
  have hf : IsForcingIsomorphism (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      (woodinCollapse κ δ) (woodinCollapseOrder κ δ) f := hA f hfA
  exact ⟨f, hf, hfG, htG, hf.generic_inverse_image hG.1 hR hR⟩

end ZFVP
