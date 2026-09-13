import ZFVP.SetTheory.DenseEmbedding
import ZFVP.SetTheory.FunctionComposition
import ZFVP.SetTheory.SequenceCollapseDense

/-! Dense embeddings compose, and a dense embedding of the second factor of a product is a
dense embedding of the products. Consequently `λ^{<ω}` embeds densely into `P × Coll(ω, λ)`
whenever `|P| ≤ λ` for an infinite initial `λ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Dense embeddings compose. -/
theorem IsDenseEmbedding.comp {P R P' R' P'' R'' e e' : V} (hR'' : IsForcingPreorder P'' R'')
    (he : IsDenseEmbedding P R P' R' e) (he' : IsDenseEmbedding P' R' P'' R'' e') :
    IsDenseEmbedding P R P'' R'' (compose e e') := by
  have hval : ∀ p ∈ P, (compose e e') ‘ p = e' ‘ (e ‘ p) :=
    fun p hp ↦ value_compose_of_mem_function he.1 he'.1 hp
  refine ⟨compose_function he.1 he'.1, ?_, ?_, ?_⟩
  · intro p hp q hq hqp
    rw [hval p hp, hval q hq]
    exact he'.2.1 _ (he.value_mem hp) _ (he.value_mem hq) (he.2.1 p hp q hq hqp)
  · intro p hp q hq hinc
    rw [hval p hp, hval q hq]
    exact he'.2.2.1 _ (he.value_mem hp) _ (he.value_mem hq) (he.2.2.1 p hp q hq hinc)
  · intro p'' hp''
    obtain ⟨p', hp', h1⟩ := he'.2.2.2 p'' hp''
    obtain ⟨p, hp, h2⟩ := he.2.2.2 p' hp'
    refine ⟨p, hp, ?_⟩
    rw [hval p hp]
    exact hR''.2.2 _ (he'.value_mem (he.value_mem hp)) _ (he'.value_mem hp') p'' hp''
      (he'.2.1 p' hp' _ (he.value_mem hp) h2) h1

/-- The product of the identity on `P` with a dense embedding of `Q` into `Q'`. -/
noncomputable def productEmbedding (P Q e : V) : V :=
  definableGraph (P ×ˢ Q) (fun z ↦ ⟨kpair.π₁ z, e ‘ (kpair.π₂ z)⟩ₖ) (by definability)

theorem productEmbedding_value {P Q e p q : V} (hp : p ∈ P) (hq : q ∈ Q) :
    (productEmbedding P Q e) ‘ ⟨p, q⟩ₖ = ⟨p, e ‘ q⟩ₖ := by
  unfold productEmbedding
  rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hp, hq⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

/-- A dense embedding of the second factor induces a dense embedding of the products. -/
theorem IsDenseEmbedding.productLeft {P R Q S Q' S' e : V} (hR : IsForcingPreorder P R)
    (he : IsDenseEmbedding Q S Q' S' e) :
    IsDenseEmbedding (P ×ˢ Q) (productOrder P R Q S) (P ×ˢ Q') (productOrder P R Q' S')
      (productEmbedding P Q e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply definableGraph_mem_function_of_mapsTo
    intro z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact kpair_mem_iff.mpr ⟨hp, he.value_mem hq⟩
  · intro x hx y hy hyx
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_prod_iff.mp hy
    obtain ⟨_, _, _, _, h1, h2⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hyx
    rw [productEmbedding_value hp hq, productEmbedding_value hp' hq']
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp', he.value_mem hq', hp, he.value_mem hq,
      h1, he.2.1 q hq q' hq' h2⟩
  · intro x hx y hy hinc hc
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_prod_iff.mp hy
    rw [productEmbedding_value hp hq, productEmbedding_value hp' hq'] at hc
    obtain ⟨h1, h2⟩ := (product_compatible_iff hp (he.value_mem hq) hp' (he.value_mem hq')).mp hc
    exact hinc ((product_compatible_iff hp hq hp' hq').mpr ⟨h1, he.compatible_of_value hq hq' h2⟩)
  · intro y hy
    obtain ⟨p, hp, q'', hq'', rfl⟩ := mem_prod_iff.mp hy
    obtain ⟨q, hq, hqq⟩ := he.2.2.2 q'' hq''
    refine ⟨⟨p, q⟩ₖ, kpair_mem_iff.mpr ⟨hp, hq⟩, ?_⟩
    rw [productEmbedding_value hp hq]
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp, he.value_mem hq, hp, hq'', hR.2.1 p hp, hqq⟩

/-- Absorption: `λ^{<ω}` embeds densely into `P × Coll(ω, λ)` when `|P| ≤ λ`. -/
theorem exists_collapseProduct_denseEmbedding (hAC : InternalChoice V) {P R one lam : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hlam : IsInitialOrdinal lam)
    (hω : (ω : V) ⊆ lam) (hP : P ≤# lam) :
    ∃ e, IsDenseEmbedding (finiteSequences lam) (sequenceOrder lam) (P ×ˢ collapseConditions lam)
      (productOrder P R (collapseConditions lam) (collapseOrder lam)) e := by
  obtain ⟨e₁, he₁⟩ := exists_sequenceProduct_denseEmbedding hR htop hAC hlam hω hP
  have he₂ := (sequence_collapse_denseEmbedding (hω ∅ empty_mem_ω)).productLeft (P := P) (R := R) hR
  exact ⟨_, he₁.comp (productOrder_preorder hR (collapse_poset lam).1) he₂⟩

end ZFVP
