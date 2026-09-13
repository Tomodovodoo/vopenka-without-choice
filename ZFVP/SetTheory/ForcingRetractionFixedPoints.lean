import ZFVP.SetTheory.ForcingRetraction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingMapFixedPoints (P m : V) : V := {p ∈ P ; m ‘ p = p}

instance forcingMapFixedPoints_definable : ℒₛₑₜ-function₂[V] forcingMapFixedPoints := by
  have h : ℒₛₑₜ-relation₃[V] (fun N P m ↦ ∀ p, p ∈ N ↔ p ∈ P ∧ m ‘ p = p) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingMapFixedPoints (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingMapFixedPoints, mem_sep_iff]

noncomputable def forcingOrderRestriction (N R : V) : V := {z ∈ N ×ˢ N ; z ∈ R}

instance forcingOrderRestriction_definable : ℒₛₑₜ-function₂[V] forcingOrderRestriction := by
  have h : ℒₛₑₜ-relation₃[V] (fun S N R ↦ ∀ z, z ∈ S ↔ z ∈ N ×ˢ N ∧ z ∈ R) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingOrderRestriction (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingOrderRestriction, mem_sep_iff]

theorem pair_mem_forcingOrderRestriction (N R p q : V) :
    ⟨p, q⟩ₖ ∈ forcingOrderRestriction N R ↔ p ∈ N ∧ q ∈ N ∧ ⟨p, q⟩ₖ ∈ R := by
  simp only [forcingOrderRestriction, mem_sep_iff, kpair_mem_iff, and_assoc]

theorem forcingOrderRestriction_preorder {P R N : V} (hR : IsForcingPreorder P R) (hN : N ⊆ P) :
    IsForcingPreorder N (forcingOrderRestriction N R) := by
  refine ⟨sep_subset, ?_, ?_⟩
  · intro p hp
    exact (pair_mem_forcingOrderRestriction _ _ _ _).mpr ⟨hp, hp, hR.2.1 p (hN p hp)⟩
  · intro p hp q hq r hr hpq hqr
    exact (pair_mem_forcingOrderRestriction _ _ _ _).mpr ⟨hp, hr,
      hR.2.2 p (hN p hp) q (hN q hq) r (hN r hr)
        ((pair_mem_forcingOrderRestriction _ _ _ _).mp hpq).2.2
        ((pair_mem_forcingOrderRestriction _ _ _ _).mp hqr).2.2⟩

theorem IsForcingRetraction.fixedPoints_eq {P R N T m : V} (hr : IsForcingRetraction N T P R m) :
    forcingMapFixedPoints P m = N := by
  apply mem_ext
  intro p
  rw [forcingMapFixedPoints, mem_sep_iff]
  exact ⟨fun hp ↦ hp.2 ▸ function_value_mem hr.maps hp.1, fun hp ↦ ⟨hr.inclusion p hp, hr.fixes p hp⟩⟩

theorem IsForcingRetraction.orderRestriction_eq {P R N T m : V}
    (hr : IsForcingRetraction N T P R m) (hT : IsForcingPreorder N T) :
    forcingOrderRestriction N R = T := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    have hh := (hr.below p (hr.inclusion p hp) q hq).mp (mem_sep_iff.mp hz).2
    rwa [hr.fixes p hp] at hh
  · intro hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (hT.1 z hz)
    exact (pair_mem_forcingOrderRestriction _ _ _ _).mpr ⟨hp, hq,
      (hr.below p (hr.inclusion p hp) q hq).mpr (by rwa [hr.fixes p hp])⟩

end ZFVP
