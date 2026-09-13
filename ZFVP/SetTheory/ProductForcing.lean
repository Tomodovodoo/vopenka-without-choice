import ZFVP.SetTheory.ForcingOrder

/-! Product forcing: the componentwise order on `P ×ˢ Q`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The componentwise order on the product `P ×ˢ Q`. -/
noncomputable def productOrder (P R Q S : V) : V :=
  {z ∈ (P ×ˢ Q) ×ˢ (P ×ˢ Q) ;
    ⟨kpair.π₁ (kpair.π₁ z), kpair.π₁ (kpair.π₂ z)⟩ₖ ∈ R ∧
    ⟨kpair.π₂ (kpair.π₁ z), kpair.π₂ (kpair.π₂ z)⟩ₖ ∈ S}

theorem pair_mem_productOrder_iff (P R Q S p q p' q' : V) :
    ⟨⟨p, q⟩ₖ, ⟨p', q'⟩ₖ⟩ₖ ∈ productOrder P R Q S ↔
      p ∈ P ∧ q ∈ Q ∧ p' ∈ P ∧ q' ∈ Q ∧ ⟨p, p'⟩ₖ ∈ R ∧ ⟨q, q'⟩ₖ ∈ S := by
  simp only [productOrder, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem productOrder_subset (P R Q S : V) : productOrder P R Q S ⊆ (P ×ˢ Q) ×ˢ (P ×ˢ Q) :=
  fun z hz ↦ (mem_sep_iff.mp hz).1

theorem productOrder_preorder {P R Q S : V} (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S) :
    IsForcingPreorder (P ×ˢ Q) (productOrder P R Q S) := by
  refine ⟨productOrder_subset P R Q S, ?_, ?_⟩
  · intro z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp, hq, hp, hq, hR.2.1 p hp, hS.2.1 q hq⟩
  · intro x hx y hy z hz hxy hyz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_prod_iff.mp hy
    obtain ⟨p'', hp'', q'', hq'', rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨_, _, _, _, h1, h2⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hxy
    obtain ⟨_, _, _, _, h3, h4⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hyz
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp, hq, hp'', hq'',
      hR.2.2 p hp p' hp' p'' hp'' h1 h3, hS.2.2 q hq q' hq' q'' hq'' h2 h4⟩

theorem product_top {P R Q S one one' : V} (htop : IsForcingTop P R one) (htop' : IsForcingTop Q S one') :
    IsForcingTop (P ×ˢ Q) (productOrder P R Q S) ⟨one, one'⟩ₖ := by
  refine ⟨kpair_mem_iff.mpr ⟨htop.1, htop'.1⟩, ?_⟩
  intro z hz
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
  exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp, hq, htop.1, htop'.1, htop.2 p hp, htop'.2 q hq⟩

theorem product_compatible_iff {P R Q S p q p' q' : V} (hp : p ∈ P) (hq : q ∈ Q) (hp' : p' ∈ P) (hq' : q' ∈ Q) :
    ForcingCompatible (P ×ˢ Q) (productOrder P R Q S) ⟨p, q⟩ₖ ⟨p', q'⟩ₖ ↔
      ForcingCompatible P R p p' ∧ ForcingCompatible Q S q q' := by
  constructor
  · rintro ⟨z, hz, h1, h2⟩
    obtain ⟨r, hr, s, hs, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨_, _, _, _, hrp, hsq⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp h1
    obtain ⟨_, _, _, _, hrp', hsq'⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp h2
    exact ⟨⟨r, hr, hrp, hrp'⟩, ⟨s, hs, hsq, hsq'⟩⟩
  · rintro ⟨⟨r, hr, hrp, hrp'⟩, ⟨s, hs, hsq, hsq'⟩⟩
    exact ⟨⟨r, s⟩ₖ, kpair_mem_iff.mpr ⟨hr, hs⟩,
      (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hr, hs, hp, hq, hrp, hsq⟩,
      (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hr, hs, hp', hq', hrp', hsq'⟩⟩

end ZFVP
