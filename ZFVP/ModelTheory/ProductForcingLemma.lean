import ZFVP.SetTheory.ProductForcing
import ZFVP.ModelTheory.QuotientEquivalence

/-! The product lemma: if `G` is generic for `P₁ × P₂`, its first projection `G₁` is `P₁`-generic
and its second projection is generic for `P₂` over `V[G₁]`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The first projection of a set of pairs. -/
def firstProjectionGeneric (G : Set V) : Set V := {p | ∃ q, ⟨p, q⟩ₖ ∈ G}

/-- The second projection of a set of pairs. -/
def secondProjectionGeneric (G : Set V) : Set V := {q | ∃ p, ⟨p, q⟩ₖ ∈ G}

section

variable {P₁ R₁ one₁ P₂ R₂ one₂ : V} (h₁ : IsForcingPreorder P₁ R₁) (t₁ : IsForcingTop P₁ R₁ one₁)
  (h₂ : IsForcingPreorder P₂ R₂) (t₂ : IsForcingTop P₂ R₂ one₂) {G : Set V}
  (hG : IsExternalForcingGeneric (P₁ ×ˢ P₂) (productOrder P₁ R₁ P₂ R₂) G)

include h₁ h₂ hG in
theorem pair_mem_product_generic_iff (p q : V) :
    ⟨p, q⟩ₖ ∈ G ↔ p ∈ firstProjectionGeneric G ∧ q ∈ secondProjectionGeneric G := by
  constructor
  · intro h
    exact ⟨⟨q, h⟩, ⟨p, h⟩⟩
  · rintro ⟨⟨q', hq'⟩, ⟨p', hp'⟩⟩
    obtain ⟨z, hz, hz1, hz2⟩ := hG.1.2.2.2 _ hq' _ hp'
    obtain ⟨hp, _⟩ := kpair_mem_iff.mp (hG.1.1 _ hq')
    obtain ⟨_, hq⟩ := kpair_mem_iff.mp (hG.1.1 _ hp')
    obtain ⟨r, hr, s, hs, rfl⟩ := mem_prod_iff.mp (hG.1.1 z hz)
    obtain ⟨_, _, _, _, hrp, _⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hz1
    obtain ⟨_, _, _, _, _, hsq⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hz2
    exact hG.1.2.2.1 _ hz _ (kpair_mem_iff.mpr ⟨hp, hq⟩)
      ((pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hr, hs, hp, hq, hrp, hsq⟩)

include h₁ h₂ hG in
theorem firstProjection_generic : IsExternalForcingGeneric P₁ R₁ (firstProjectionGeneric G) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro p ⟨q, hpq⟩
    exact (kpair_mem_iff.mp (hG.1.1 _ hpq)).1
  · obtain ⟨z, hz⟩ := hG.1.2.1
    obtain ⟨p, _, q, _, rfl⟩ := mem_prod_iff.mp (hG.1.1 z hz)
    exact ⟨p, q, hz⟩
  · rintro p ⟨q, hpq⟩ p' hp' hpp'
    obtain ⟨hp, hq⟩ := kpair_mem_iff.mp (hG.1.1 _ hpq)
    exact ⟨q, hG.1.2.2.1 _ hpq _ (kpair_mem_iff.mpr ⟨hp', hq⟩)
      ((pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp, hq, hp', hq, hpp', h₂.2.1 q hq⟩)⟩
  · rintro p ⟨q, hpq⟩ p' ⟨q', hpq'⟩
    obtain ⟨z, hz, hz1, hz2⟩ := hG.1.2.2.2 _ hpq _ hpq'
    obtain ⟨r, _, s, _, rfl⟩ := mem_prod_iff.mp (hG.1.1 z hz)
    obtain ⟨_, _, _, _, hrp, _⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hz1
    obtain ⟨_, _, _, _, hrp', _⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hz2
    exact ⟨r, ⟨s, hz⟩, hrp, hrp'⟩
  · intro D hD
    have hD' : ForcingDense (P₁ ×ˢ P₂) (productOrder P₁ R₁ P₂ R₂) (D ×ˢ P₂) := by
      refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
      · obtain ⟨d, hd, q, hq, rfl⟩ := mem_prod_iff.mp hz
        exact kpair_mem_iff.mpr ⟨hD.1 d hd, hq⟩
      · obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
        obtain ⟨d, hd, hdp⟩ := hD.2 p hp
        exact ⟨⟨d, q⟩ₖ, kpair_mem_iff.mpr ⟨hd, hq⟩,
          (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hD.1 d hd, hq, hp, hq, hdp, h₂.2.1 q hq⟩⟩
    obtain ⟨z, hz, hzD⟩ := hG.2 _ hD'
    obtain ⟨d, hd, q, _, rfl⟩ := mem_prod_iff.mp hzD
    exact ⟨d, ⟨q, hz⟩, hd⟩

/-- The extension by the product. -/
noncomputable def productContext : ForcingContext V where
  P := P₁ ×ˢ P₂
  R := productOrder P₁ R₁ P₂ R₂
  one := ⟨one₁, one₂⟩ₖ
  G := G
  order := productOrder_preorder h₁ h₂
  top := product_top t₁ t₂
  generic := hG

/-- The extension by the first factor. -/
noncomputable def firstFactorContext : ForcingContext V where
  P := P₁
  R := R₁
  one := one₁
  G := firstProjectionGeneric G
  order := h₁
  top := t₁
  generic := firstProjection_generic h₁ h₂ hG

/-- The second factor inside `V[G₁]`, with the second projection of the generic. -/
def secondFactorGeneric : Set (firstFactorContext h₁ t₁ h₂ hG).Model :=
  {x | ∃ q ∈ secondProjectionGeneric G, x = (firstFactorContext h₁ t₁ h₂ hG).check q}

theorem check_mem_secondFactorGeneric_iff (q : V) :
    (firstFactorContext h₁ t₁ h₂ hG).check q ∈ secondFactorGeneric h₁ t₁ h₂ hG ↔
      q ∈ secondProjectionGeneric G := by
  constructor
  · rintro ⟨q', hq', he⟩
    rw [(firstFactorContext h₁ t₁ h₂ hG).check_eq_iff] at he
    rw [he]
    exact hq'
  · intro hq
    exact ⟨q, hq, rfl⟩

theorem secondFactor_preorder : IsForcingPreorder ((firstFactorContext h₁ t₁ h₂ hG).check P₂)
    ((firstFactorContext h₁ t₁ h₂ hG).check R₂) :=
  (firstFactorContext h₁ t₁ h₂ hG).checkEmbedding.map_forcingPreorder h₂

include t₂ in
theorem secondFactor_top : IsForcingTop ((firstFactorContext h₁ t₁ h₂ hG).check P₂)
    ((firstFactorContext h₁ t₁ h₂ hG).check R₂) ((firstFactorContext h₁ t₁ h₂ hG).check one₂) := by
  let C := firstFactorContext h₁ t₁ h₂ hG
  refine ⟨(C.check_mem_iff _ _).mpr t₂.1, fun x hx ↦ ?_⟩
  obtain ⟨q, hq, rfl⟩ := (C.mem_check_iff _ _).mp hx
  rw [← C.check_kpair, C.check_mem_iff]
  exact t₂.2 q hq

theorem secondFactorGeneric_filter : IsExternalForcingFilter ((firstFactorContext h₁ t₁ h₂ hG).check P₂)
    ((firstFactorContext h₁ t₁ h₂ hG).check R₂) (secondFactorGeneric h₁ t₁ h₂ hG) := by
  let C := firstFactorContext h₁ t₁ h₂ hG
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨q, ⟨p, hpq⟩, rfl⟩
    exact (C.check_mem_iff _ _).mpr (kpair_mem_iff.mp (hG.1.1 _ hpq)).2
  · obtain ⟨z, hz⟩ := hG.1.2.1
    obtain ⟨p, _, q, _, rfl⟩ := mem_prod_iff.mp (hG.1.1 z hz)
    exact ⟨_, q, ⟨p, hz⟩, rfl⟩
  · rintro x ⟨q, ⟨p, hpq⟩, rfl⟩ y hy hxy
    obtain ⟨q', hq', rfl⟩ := (C.mem_check_iff _ _).mp hy
    rw [← C.check_kpair, C.check_mem_iff] at hxy
    obtain ⟨hp, hq⟩ := kpair_mem_iff.mp (hG.1.1 _ hpq)
    refine ⟨q', ⟨p, hG.1.2.2.1 _ hpq _ (kpair_mem_iff.mpr ⟨hp, hq'⟩) ?_⟩, rfl⟩
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp, hq, hp, hq', h₁.2.1 p hp, hxy⟩
  · rintro x ⟨q, ⟨p, hpq⟩, rfl⟩ y ⟨q', ⟨p', hpq'⟩, rfl⟩
    obtain ⟨z, hz, hz1, hz2⟩ := hG.1.2.2.2 _ hpq _ hpq'
    obtain ⟨r, _, s, _, rfl⟩ := mem_prod_iff.mp (hG.1.1 z hz)
    obtain ⟨_, _, _, _, _, hsq⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hz1
    obtain ⟨_, _, _, _, _, hsq'⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hz2
    refine ⟨C.check s, ⟨s, ⟨r, hz⟩, rfl⟩, ?_, ?_⟩
    · rw [← C.check_kpair, C.check_mem_iff]
      exact hsq
    · rw [← C.check_kpair, C.check_mem_iff]
      exact hsq'

/-- Pairs whose first coordinate forces the check of the second into a given name. -/
noncomputable def productWitnessSet (P₁ R₁ one₁ P₂ Dn : V) : V :=
  sep (P₁ ×ˢ P₂) (fun z ↦ kpair.π₁ z ∈ atomicMembership P₁ R₁ (checkName one₁ (kpair.π₂ z)) Dn)
    (by have := atomicMembership_definable P₁ R₁; definability)

theorem mem_productWitnessSet_iff (P₁ R₁ one₁ P₂ Dn z : V) :
    z ∈ productWitnessSet P₁ R₁ one₁ P₂ Dn ↔
      z ∈ P₁ ×ˢ P₂ ∧ kpair.π₁ z ∈ atomicMembership P₁ R₁ (checkName one₁ (kpair.π₂ z)) Dn :=
  mem_sep_iff

noncomputable def productDenseSet (P₁ R₁ one₁ P₂ R₂ Dn : V) : V :=
  productWitnessSet P₁ R₁ one₁ P₂ Dn ∪
    sep (P₁ ×ˢ P₂) (fun z ↦ ∀ z' ∈ productWitnessSet P₁ R₁ one₁ P₂ Dn,
      ⟨z', z⟩ₖ ∉ productOrder P₁ R₁ P₂ R₂) (by definability)

theorem mem_productDenseSet_iff (P₁ R₁ one₁ P₂ R₂ Dn z : V) :
    z ∈ productDenseSet P₁ R₁ one₁ P₂ R₂ Dn ↔ z ∈ productWitnessSet P₁ R₁ one₁ P₂ Dn ∨
      (z ∈ P₁ ×ˢ P₂ ∧ ∀ z' ∈ productWitnessSet P₁ R₁ one₁ P₂ Dn, ⟨z', z⟩ₖ ∉ productOrder P₁ R₁ P₂ R₂) := by
  unfold productDenseSet
  rw [mem_union_iff, mem_sep_iff]

/-- The product lemma: the second projection meets every dense set of `V[G₁]`. -/
theorem secondFactorGeneric_meets (D' : (firstFactorContext h₁ t₁ h₂ hG).Model)
    (hD' : ForcingDense ((firstFactorContext h₁ t₁ h₂ hG).check P₂)
      ((firstFactorContext h₁ t₁ h₂ hG).check R₂) D') :
    ∃ x ∈ secondFactorGeneric h₁ t₁ h₂ hG, x ∈ D' := by
  let C := firstFactorContext h₁ t₁ h₂ hG
  have hgen : IsExternalForcingGeneric P₁ R₁ (firstProjectionGeneric G) := firstProjection_generic h₁ h₂ hG
  obtain ⟨Dn, rfl⟩ := C.ofName_surjective D'
  have hmem_of_forced : ∀ u ∈ P₂, ∀ q ∈ firstProjectionGeneric G,
      q ∈ atomicMembership P₁ R₁ (checkName one₁ u) Dn.val → C.check u ∈ C.ofName Dn := by
    intro u _ q hq hqM
    exact (forcingQuotientMk_mem_iff C.P C.R C.G C.order C.generic.1
      ⟨checkName C.one u, checkName_isName C.top.1 u⟩ Dn).mpr ⟨q, hq, hqM⟩
  have hW : productWitnessSet P₁ R₁ one₁ P₂ Dn.val ⊆ P₁ ×ˢ P₂ :=
    fun z hz ↦ ((mem_productWitnessSet_iff _ _ _ _ _ _).mp hz).1
  have hF : ForcingDense (P₁ ×ˢ P₂) (productOrder P₁ R₁ P₂ R₂) (productDenseSet P₁ R₁ one₁ P₂ R₂ Dn.val) := by
    refine ⟨fun z hz ↦ ((mem_productDenseSet_iff _ _ _ _ _ _ _).mp hz).elim (hW z) (fun h ↦ h.1),
      fun z hz ↦ ?_⟩
    by_cases hex : ∃ z' ∈ productWitnessSet P₁ R₁ one₁ P₂ Dn.val, ⟨z', z⟩ₖ ∈ productOrder P₁ R₁ P₂ R₂
    · obtain ⟨z', hz', hzz'⟩ := hex
      exact ⟨z', (mem_productDenseSet_iff _ _ _ _ _ _ _).mpr (Or.inl hz'), hzz'⟩
    · push Not at hex
      exact ⟨z, (mem_productDenseSet_iff _ _ _ _ _ _ _).mpr (Or.inr ⟨hz, hex⟩),
        (productOrder_preorder h₁ h₂).2.1 z hz⟩
  obtain ⟨z₀, hz₀G, hz₀F⟩ := hG.2 _ hF
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (hG.1.1 z₀ hz₀G)
  have hpG : p ∈ firstProjectionGeneric G := ⟨q, hz₀G⟩
  have hqG : q ∈ secondProjectionGeneric G := ⟨p, hz₀G⟩
  rcases (mem_productDenseSet_iff _ _ _ _ _ _ _).mp hz₀F with hE | hN
  · obtain ⟨_, hM⟩ := (mem_productWitnessSet_iff _ _ _ _ _ _).mp hE
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hM
    exact ⟨C.check q, ⟨q, hqG, rfl⟩, hmem_of_forced q hq p hpG hM⟩
  · exfalso
    obtain ⟨_, hnone⟩ := hN
    have hq' : C.check q ∈ C.check P₂ := (C.check_mem_iff _ _).mpr hq
    obtain ⟨u', hu'D, hu'q⟩ := hD'.2 _ hq'
    obtain ⟨u, hu, rfl⟩ := (C.mem_check_iff P₂ _).mp (hD'.1 _ hu'D)
    rw [← C.check_kpair, C.check_mem_iff] at hu'q
    obtain ⟨q₁, hq₁G, hq₁M⟩ := (forcingQuotientMk_mem_iff C.P C.R C.G C.order C.generic.1
      ⟨checkName C.one u, checkName_isName C.top.1 u⟩ Dn).mp hu'D
    obtain ⟨q', hq'G, hq'q₁, hq'p⟩ := hgen.1.2.2.2 q₁ hq₁G p hpG
    have hq'P : q' ∈ P₁ := hgen.1.1 q' hq'G
    have hq'M : q' ∈ atomicMembership P₁ R₁ (checkName one₁ u) Dn.val :=
      atomicMembership_mono h₁ hq₁M hq'P hq'q₁
    have hz'W : ⟨q', u⟩ₖ ∈ productWitnessSet P₁ R₁ one₁ P₂ Dn.val := by
      refine (mem_productWitnessSet_iff _ _ _ _ _ _).mpr ⟨kpair_mem_iff.mpr ⟨hq'P, hu⟩, ?_⟩
      simp only [kpair.π₁_kpair, kpair.π₂_kpair]
      exact hq'M
    apply hnone _ hz'W
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hq'P, hu, hp, hq, hq'p, hu'q⟩

/-- The second factor over `V[G₁]` with the second projection of the generic. -/
noncomputable def secondFactorContext : ForcingContext (firstFactorContext h₁ t₁ h₂ hG).Model where
  P := (firstFactorContext h₁ t₁ h₂ hG).check P₂
  R := (firstFactorContext h₁ t₁ h₂ hG).check R₂
  one := (firstFactorContext h₁ t₁ h₂ hG).check one₂
  G := secondFactorGeneric h₁ t₁ h₂ hG
  order := secondFactor_preorder h₁ t₁ h₂ hG
  top := secondFactor_top h₁ t₁ h₂ t₂ hG
  generic := ⟨secondFactorGeneric_filter h₁ t₁ h₂ hG, secondFactorGeneric_meets h₁ t₁ h₂ hG⟩

end

end ZFVP
