import ZFVP.SetTheory.DenseEmbeddingComposition

/-! Dense embeddings of the first factor of a product, and associativity of products as a dense
embedding (an isomorphism). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The product of a dense embedding of `P` into `P'` with the identity on `Q`. -/
noncomputable def productEmbeddingLeft (P Q e : V) : V :=
  definableGraph (P ×ˢ Q) (fun z ↦ ⟨e ‘ (kpair.π₁ z), kpair.π₂ z⟩ₖ) (by definability)

theorem productEmbeddingLeft_value {P Q e p q : V} (hp : p ∈ P) (hq : q ∈ Q) :
    (productEmbeddingLeft P Q e) ‘ ⟨p, q⟩ₖ = ⟨e ‘ p, q⟩ₖ := by
  unfold productEmbeddingLeft
  rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hp, hq⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

/-- A dense embedding of the first factor induces a dense embedding of the products. -/
theorem IsDenseEmbedding.productRight {P R P' R' Q S e : V} (hS : IsForcingPreorder Q S)
    (he : IsDenseEmbedding P R P' R' e) :
    IsDenseEmbedding (P ×ˢ Q) (productOrder P R Q S) (P' ×ˢ Q) (productOrder P' R' Q S)
      (productEmbeddingLeft P Q e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply definableGraph_mem_function_of_mapsTo
    intro z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact kpair_mem_iff.mpr ⟨he.value_mem hp, hq⟩
  · intro x hx y hy hyx
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_prod_iff.mp hy
    obtain ⟨_, _, _, _, h1, h2⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hyx
    rw [productEmbeddingLeft_value hp hq, productEmbeddingLeft_value hp' hq']
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨he.value_mem hp', hq', he.value_mem hp, hq,
      he.2.1 p hp p' hp' h1, h2⟩
  · intro x hx y hy hinc hc
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_prod_iff.mp hy
    rw [productEmbeddingLeft_value hp hq, productEmbeddingLeft_value hp' hq'] at hc
    obtain ⟨h1, h2⟩ := (product_compatible_iff (he.value_mem hp) hq (he.value_mem hp') hq').mp hc
    exact hinc ((product_compatible_iff hp hq hp' hq').mpr ⟨he.compatible_of_value hp hp' h1, h2⟩)
  · intro y hy
    obtain ⟨p'', hp'', q, hq, rfl⟩ := mem_prod_iff.mp hy
    obtain ⟨p, hp, hpp⟩ := he.2.2.2 p'' hp''
    refine ⟨⟨p, q⟩ₖ, kpair_mem_iff.mpr ⟨hp, hq⟩, ?_⟩
    rw [productEmbeddingLeft_value hp hq]
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨he.value_mem hp, hq, hp'', hq, hpp, hS.2.1 q hq⟩

/-- The associativity map `⟨⟨a, b⟩, c⟩ ↦ ⟨a, ⟨b, c⟩⟩`. -/
noncomputable def productAssoc (P Q T : V) : V :=
  definableGraph ((P ×ˢ Q) ×ˢ T) (fun z ↦ ⟨kpair.π₁ (kpair.π₁ z), ⟨kpair.π₂ (kpair.π₁ z), kpair.π₂ z⟩ₖ⟩ₖ)
    (by definability)

theorem productAssoc_value {P Q T a b c : V} (ha : a ∈ P) (hb : b ∈ Q) (hc : c ∈ T) :
    (productAssoc P Q T) ‘ ⟨⟨a, b⟩ₖ, c⟩ₖ = ⟨a, ⟨b, c⟩ₖ⟩ₖ := by
  unfold productAssoc
  rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨ha, hb⟩, hc⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

/-- Associativity of products is a dense embedding (an isomorphism). -/
theorem productAssoc_denseEmbedding {P R Q S T U : V} (hR : IsForcingPreorder P R)
    (hS : IsForcingPreorder Q S) (hU : IsForcingPreorder T U) :
    IsDenseEmbedding ((P ×ˢ Q) ×ˢ T) (productOrder (P ×ˢ Q) (productOrder P R Q S) T U)
      (P ×ˢ (Q ×ˢ T)) (productOrder P R (Q ×ˢ T) (productOrder Q S T U)) (productAssoc P Q T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply definableGraph_mem_function_of_mapsTo
    intro z hz
    obtain ⟨ab, hab, c, hc, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hab
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact kpair_mem_iff.mpr ⟨ha, kpair_mem_iff.mpr ⟨hb, hc⟩⟩
  · intro x hx y hy hyx
    obtain ⟨ab, hab, c, hc, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hab
    obtain ⟨ab', hab', c', hc', rfl⟩ := mem_prod_iff.mp hy
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_prod_iff.mp hab'
    obtain ⟨_, _, _, _, h1, h2⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hyx
    obtain ⟨_, _, _, _, h11, h12⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp h1
    rw [productAssoc_value ha hb hc, productAssoc_value ha' hb' hc']
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨ha', kpair_mem_iff.mpr ⟨hb', hc'⟩, ha,
      kpair_mem_iff.mpr ⟨hb, hc⟩, h11, (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hb', hc', hb, hc, h12, h2⟩⟩
  · intro x hx y hy hinc hc
    obtain ⟨ab, hab, c, hcT, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hab
    obtain ⟨ab', hab', c', hc'T, rfl⟩ := mem_prod_iff.mp hy
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_prod_iff.mp hab'
    rw [productAssoc_value ha hb hcT, productAssoc_value ha' hb' hc'T] at hc
    obtain ⟨h1, h2⟩ := (product_compatible_iff ha (kpair_mem_iff.mpr ⟨hb, hcT⟩) ha'
      (kpair_mem_iff.mpr ⟨hb', hc'T⟩)).mp hc
    obtain ⟨h21, h22⟩ := (product_compatible_iff hb hcT hb' hc'T).mp h2
    exact hinc ((product_compatible_iff (kpair_mem_iff.mpr ⟨ha, hb⟩) hcT (kpair_mem_iff.mpr ⟨ha', hb'⟩) hc'T).mpr
      ⟨(product_compatible_iff ha hb ha' hb').mpr ⟨h1, h21⟩, h22⟩)
  · intro y hy
    obtain ⟨a, ha, bc, hbc, rfl⟩ := mem_prod_iff.mp hy
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_prod_iff.mp hbc
    refine ⟨⟨⟨a, b⟩ₖ, c⟩ₖ, kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨ha, hb⟩, hc⟩, ?_⟩
    rw [productAssoc_value ha hb hc]
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨ha, kpair_mem_iff.mpr ⟨hb, hc⟩, ha,
      kpair_mem_iff.mpr ⟨hb, hc⟩, hR.2.1 a ha, (productOrder_preorder hS hU).2.1 _ (kpair_mem_iff.mpr ⟨hb, hc⟩)⟩

end ZFVP
