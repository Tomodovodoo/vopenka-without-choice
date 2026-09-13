import ZFVP.SetTheory.ForcingOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The separative preorder on the original set of conditions. -/
noncomputable def forcingSeparativeOrder (P R : V) : V :=
  {z ∈ P ×ˢ P ; ∀ r ∈ P, ⟨r, kpair.π₁ z⟩ₖ ∈ R → ForcingCompatible P R r (kpair.π₂ z)}

theorem kpair_mem_forcingSeparativeOrder (P R p q : V) :
    ⟨p, q⟩ₖ ∈ forcingSeparativeOrder P R ↔
      p ∈ P ∧ q ∈ P ∧ ∀ r ∈ P, ⟨r, p⟩ₖ ∈ R → ForcingCompatible P R r q := by
  simp only [forcingSeparativeOrder, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    and_assoc]

instance forcingSeparativeOrder_definable : ℒₛₑₜ-function₂[V] forcingSeparativeOrder := by
  have h : ℒₛₑₜ-relation₃ (fun S P R : V ↦ ∀ z, z ∈ S ↔ z ∈ P ×ˢ P ∧
      ∀ r ∈ P, ⟨r, kpair.π₁ z⟩ₖ ∈ R → ForcingCompatible P R r (kpair.π₂ z)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingSeparativeOrder (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingSeparativeOrder, mem_sep_iff]

theorem forcingOrder_subset_separative {P R : V} (hR : IsForcingPreorder P R) :
    R ⊆ forcingSeparativeOrder P R := by
  intro z hz
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (hR.1 z hz)
  apply (kpair_mem_forcingSeparativeOrder P R p q).mpr
  refine ⟨hp, hq, ?_⟩
  intro r hr hrp
  exact ⟨r, hr, hR.2.1 r hr, hR.2.2 r hr p hp q hq hrp hz⟩

theorem forcingSeparativeOrder_preorder {P R : V} (hR : IsForcingPreorder P R) :
    IsForcingPreorder P (forcingSeparativeOrder P R) := by
  refine ⟨fun z hz ↦ (mem_sep_iff.mp hz).1,
    fun p hp ↦ forcingOrder_subset_separative hR _ (hR.2.1 p hp), ?_⟩
  intro p hp q hq s hs hpq hqs
  have hpq' := ((kpair_mem_forcingSeparativeOrder P R p q).mp hpq).2.2
  have hqs' := ((kpair_mem_forcingSeparativeOrder P R q s).mp hqs).2.2
  refine (kpair_mem_forcingSeparativeOrder P R p s).mpr ⟨hp, hs, ?_⟩
  intro r hr hrp
  obtain ⟨u, hu, hur, huq⟩ := hpq' r hr hrp
  obtain ⟨v, hv, hvu, hvs⟩ := hqs' u hu huq
  exact ⟨v, hv, hR.2.2 v hv u hu r hr hvu hur, hvs⟩

theorem forcingSeparativeOrder_compatible {P R p q : V} (hR : IsForcingPreorder P R)
    (hpq : ⟨p, q⟩ₖ ∈ forcingSeparativeOrder P R) : ForcingCompatible P R p q := by
  obtain ⟨hp, _, h⟩ := (kpair_mem_forcingSeparativeOrder P R p q).mp hpq
  exact h p hp (hR.2.1 p hp)

theorem forcingSeparativeOrder_compatible_iff {P R p q : V} (hR : IsForcingPreorder P R) :
    ForcingCompatible P (forcingSeparativeOrder P R) p q ↔ ForcingCompatible P R p q := by
  constructor
  · rintro ⟨r, hr, hrp, hrq⟩
    obtain ⟨u, hu, hur, hup⟩ := forcingSeparativeOrder_compatible hR hrp
    obtain ⟨v, hv, hvu, hvq⟩ := ((kpair_mem_forcingSeparativeOrder P R r q).mp hrq).2.2 u hu hur
    exact ⟨v, hv, hR.2.2 v hv u hu p
      ((kpair_mem_forcingSeparativeOrder P R r p).mp hrp).2.1 hvu hup, hvq⟩
  · rintro ⟨r, hr, hrp, hrq⟩
    exact ⟨r, hr, forcingOrder_subset_separative hR _ hrp, forcingOrder_subset_separative hR _ hrq⟩

theorem forcingSeparativeOrder_top {P R one : V} (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) : IsForcingTop P (forcingSeparativeOrder P R) one :=
  ⟨ht.1, fun p hp ↦ forcingOrder_subset_separative hR _ (ht.2 p hp)⟩

end ZFVP
