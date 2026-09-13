import ZFVP.SetTheory.FunctionValue
import ZFVP.SetTheory.ForcingOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The order induced on a set of representatives by their map to conditions. -/
noncomputable def forcingPullbackOrder (Q R π : V) : V :=
  {z ∈ Q ×ˢ Q ; ⟨π ‘ (kpair.π₁ z), π ‘ (kpair.π₂ z)⟩ₖ ∈ R}

theorem mem_forcingPullbackOrder_iff (Q R π p q : V) :
    ⟨p, q⟩ₖ ∈ forcingPullbackOrder Q R π ↔
      p ∈ Q ∧ q ∈ Q ∧ ⟨π ‘ p, π ‘ q⟩ₖ ∈ R := by
  simp only [forcingPullbackOrder, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem forcingPullbackOrder_preorder {P R Q π : V}
    (hR : IsForcingPreorder P R) (hπ : π ∈ P ^ Q) :
    IsForcingPreorder Q (forcingPullbackOrder Q R π) := by
  refine ⟨fun z hz ↦ (mem_sep_iff.mp hz).1, ?_, ?_⟩
  · intro p hp
    exact (mem_forcingPullbackOrder_iff _ _ _ _ _).mpr
      ⟨hp, hp, hR.2.1 _ (function_value_mem hπ hp)⟩
  · intro p hp q hq r hr hpq hqr
    have hpq' := (mem_forcingPullbackOrder_iff _ _ _ _ _).mp hpq
    have hqr' := (mem_forcingPullbackOrder_iff _ _ _ _ _).mp hqr
    exact (mem_forcingPullbackOrder_iff _ _ _ _ _).mpr ⟨hp, hr,
      hR.2.2 _ (function_value_mem hπ hp) _ (function_value_mem hπ hq)
        _ (function_value_mem hπ hr) hpq'.2.2 hqr'.2.2⟩

theorem forcingPullbackOrder_compatible_iff {P R Q π p q : V}
    (hπ : π ∈ P ^ Q) (hs : ∀ f ∈ P, ∃ z ∈ Q, π ‘ z = f)
    (hp : p ∈ Q) (hq : q ∈ Q) :
    ForcingCompatible Q (forcingPullbackOrder Q R π) p q ↔
      ForcingCompatible P R (π ‘ p) (π ‘ q) := by
  constructor
  · rintro ⟨z, hz, hzp, hzq⟩
    exact ⟨π ‘ z, function_value_mem hπ hz,
      ((mem_forcingPullbackOrder_iff _ _ _ _ _).mp hzp).2.2,
      ((mem_forcingPullbackOrder_iff _ _ _ _ _).mp hzq).2.2⟩
  · rintro ⟨f, hf, hfp, hfq⟩
    obtain ⟨z, hz, he⟩ := hs f hf
    refine ⟨z, hz, (mem_forcingPullbackOrder_iff _ _ _ _ _).mpr ⟨hz, hp, ?_⟩,
      (mem_forcingPullbackOrder_iff _ _ _ _ _).mpr ⟨hz, hq, ?_⟩⟩ <;> rwa [he]

end ZFVP
