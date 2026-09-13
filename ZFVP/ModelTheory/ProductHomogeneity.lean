import ZFVP.SetTheory.HomogeneousForcing
import ZFVP.SetTheory.ForcingFormulaNameAction
import ZFVP.SetTheory.InverseFunction
import ZFVP.ModelTheory.ProductForcingEquivalence

/-! Homogeneity of a product in its second coordinate: an automorphism of the second factor acts
on the product fixing the first coordinate, fixes the names lifted from the first factor and the
check names, and, when the second factor is weakly homogeneous, a statement about such names
forced by `(s, p)` is forced by `(s, 1)`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The map `(p, q) ↦ (p, π q)` on the product. -/
noncomputable def secondCoordinateAction (P₁ P₂ π : V) : V :=
  definableGraph (P₁ ×ˢ P₂) (fun z ↦ ⟨kpair.π₁ z, π ‘ (kpair.π₂ z)⟩ₖ) (by definability)

theorem secondCoordinateAction_value {P₁ P₂ π p q : V} (hp : p ∈ P₁) (hq : q ∈ P₂) :
    (secondCoordinateAction P₁ P₂ π) ‘ ⟨p, q⟩ₖ = ⟨p, π ‘ q⟩ₖ := by
  unfold secondCoordinateAction
  rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hp, hq⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

section

variable {P₁ R₁ P₂ R₂ π : V} (hπ : IsForcingAutomorphism P₂ R₂ π)

include hπ in
theorem secondCoordinateAction_mem_function :
    secondCoordinateAction P₁ P₂ π ∈ (P₁ ×ˢ P₂) ^ (P₁ ×ˢ P₂) := by
  apply definableGraph_mem_function_of_mapsTo
  intro z hz
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  exact kpair_mem_iff.mpr ⟨hp, function_value_mem hπ.1 hq⟩

include hπ in
theorem secondCoordinateAction_automorphism :
    IsForcingAutomorphism (P₁ ×ˢ P₂) (productOrder P₁ R₁ P₂ R₂) (secondCoordinateAction P₁ P₂ π) := by
  have hf := secondCoordinateAction_mem_function (P₁ := P₁) hπ
  have hfun : IsFunction (secondCoordinateAction P₁ P₂ π) := IsFunction.of_mem hf
  have hπf : IsFunction π := IsFunction.of_mem hπ.1
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro z₁ z₂ y h1 h2
    have hz₁ := mem_domain_of_kpair_mem h1
    have hz₂ := mem_domain_of_kpair_mem h2
    rw [domain_eq_of_mem_function hf] at hz₁ hz₂
    obtain ⟨p₁, hp₁, q₁, hq₁, rfl⟩ := mem_prod_iff.mp hz₁
    obtain ⟨p₂, hp₂, q₂, hq₂, rfl⟩ := mem_prod_iff.mp hz₂
    have e1 := value_eq_of_kpair_mem h1
    have e2 := value_eq_of_kpair_mem h2
    rw [secondCoordinateAction_value hp₁ hq₁] at e1
    rw [secondCoordinateAction_value hp₂ hq₂] at e2
    obtain ⟨hpp, hqq⟩ := kpair_iff.mp (e1.trans e2.symm)
    rw [hpp, injective_value_eq hπ.1 hπ.2.1 hq₁ hq₂ hqq]
  · apply subset_antisymm (range_subset_of_mem_function hf)
    intro z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    have hqr : q ∈ range π := by
      rw [hπ.2.2.1]
      exact hq
    obtain ⟨q₀, hq₀⟩ := mem_range_iff.mp hqr
    have hq₀P : q₀ ∈ P₂ := by
      rw [← domain_eq_of_mem_function hπ.1]
      exact mem_domain_of_kpair_mem hq₀
    have hv : π ‘ q₀ = q := value_eq_of_kpair_mem hq₀
    refine mem_range_iff.mpr ⟨⟨p, q₀⟩ₖ, ?_⟩
    have := kpair_value_mem (f := secondCoordinateAction P₁ P₂ π) (x := ⟨p, q₀⟩ₖ)
      (by rw [domain_eq_of_mem_function hf]; exact kpair_mem_iff.mpr ⟨hp, hq₀P⟩)
    rwa [secondCoordinateAction_value hp hq₀P, hv] at this
  · intro z hz z' hz'
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_prod_iff.mp hz'
    rw [secondCoordinateAction_value hp hq, secondCoordinateAction_value hp' hq',
      pair_mem_productOrder_iff, pair_mem_productOrder_iff]
    have hπq := function_value_mem hπ.1 hq
    have hπq' := function_value_mem hπ.1 hq'
    constructor
    · rintro ⟨_, _, _, _, hpp, hqq⟩
      exact ⟨hp, hπq, hp', hπq', hpp, (hπ.2.2.2 q hq q' hq').mp hqq⟩
    · rintro ⟨_, _, _, _, hpp, hqq⟩
      exact ⟨hp, hq, hp', hq', hpp, (hπ.2.2.2 q hq q' hq').mpr hqq⟩

variable {one₂ : V} (hone₂ : one₂ ∈ P₂) (hfix : π ‘ one₂ = one₂)

include hone₂ hfix in
theorem secondCoordinateAction_top {one₁ : V} (hone₁ : one₁ ∈ P₁) :
    (secondCoordinateAction P₁ P₂ π) ‘ ⟨one₁, one₂⟩ₖ = ⟨one₁, one₂⟩ₖ := by
  rw [secondCoordinateAction_value hone₁ hone₂, hfix]

include hπ hone₂ hfix in
theorem compose_leftEmbedding_secondCoordinateAction :
    compose (leftEmbedding P₁ one₂) (secondCoordinateAction P₁ P₂ π) = leftEmbedding P₁ one₂ := by
  have hℓ := leftEmbedding_mem_function (P₁ := P₁) hone₂
  have hf := secondCoordinateAction_mem_function (P₁ := P₁) hπ
  have hc := compose_function hℓ hf
  have : IsFunction (compose (leftEmbedding P₁ one₂) (secondCoordinateAction P₁ P₂ π)) := IsFunction.of_mem hc
  have : IsFunction (leftEmbedding P₁ one₂) := IsFunction.of_mem hℓ
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hc, domain_eq_of_mem_function hℓ]
  · intro p hp
    rw [domain_eq_of_mem_function hc] at hp
    rw [value_compose_of_mem_function hℓ hf hp, leftEmbedding_value hp, secondCoordinateAction_value hp hone₂, hfix]

include hπ hone₂ hfix in
/-- Names lifted from the first factor are fixed by the second-coordinate action. -/
theorem nameAction_secondCoordinateAction_lift {τ : V} (hτ : IsForcingName P₁ τ) :
    nameAction (secondCoordinateAction P₁ P₂ π) (nameAction (leftEmbedding P₁ one₂) τ) =
      nameAction (leftEmbedding P₁ one₂) τ := by
  rw [nameAction_compose (leftEmbedding_mem_function hone₂) (secondCoordinateAction_mem_function hπ) hτ,
    compose_leftEmbedding_secondCoordinateAction hπ hone₂ hfix]

end

/-- In a product whose second factor is weakly homogeneous, a statement about names fixed by all
second-coordinate actions that is forced by `(s, p)` is forced by `(s, 1)`. -/
theorem forced_by_first_of_homogeneous {P₁ R₁ P₂ R₂ one₂ : V} (h₁ : IsForcingPreorder P₁ R₁)
    (h₂ : IsForcingPreorder P₂ R₂) (t₂ : IsForcingTop P₂ R₂ one₂)
    (hhom : IsWeaklyHomogeneous P₂ R₂ one₂) {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V)
    (hv : ∀ i, IsForcingName (P₁ ×ˢ P₂) (v i))
    (hinv : ∀ π, IsForcingAutomorphism P₂ R₂ π → π ‘ one₂ = one₂ →
      ∀ i, nameAction (secondCoordinateAction P₁ P₂ π) (v i) = v i)
    {s p : V} (hs : s ∈ P₁) (hp : p ∈ P₂)
    (hsp : ⟨s, p⟩ₖ ∈ forcingFormula (P₁ ×ˢ P₂) (productOrder P₁ R₁ P₂ R₂) φ (standardTuple v)) :
    ⟨s, one₂⟩ₖ ∈ forcingFormula (P₁ ×ˢ P₂) (productOrder P₁ R₁ P₂ R₂) φ (standardTuple v) := by
  have hR := productOrder_preorder h₁ h₂
  have hreg := forcingFormula_regular hR φ (standardTuple v)
  apply hreg.2.2 ⟨s, one₂⟩ₖ (kpair_mem_iff.mpr ⟨hs, t₂.1⟩)
  intro q hq hqs
  obtain ⟨s', hs', q₂, hq₂, rfl⟩ := mem_prod_iff.mp hq
  obtain ⟨_, _, _, _, hs's, _⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hqs
  obtain ⟨π, hπ, hfix, r₂, hr₂, hr₂π, hr₂q⟩ := hhom p hp q₂ hq₂
  have h1 : ⟨s', p⟩ₖ ∈ forcingFormula (P₁ ×ˢ P₂) (productOrder P₁ R₁ P₂ R₂) φ (standardTuple v) :=
    hreg.2.1 _ hsp _ (kpair_mem_iff.mpr ⟨hs', hp⟩)
      ((pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hs', hp, hs, hp, hs's, h₂.2.1 p hp⟩)
  have hπ' := secondCoordinateAction_automorphism (P₁ := P₁) (R₁ := R₁) hπ
  have h2 : (secondCoordinateAction P₁ P₂ π) ‘ ⟨s', p⟩ₖ ∈
      forcingFormula (P₁ ×ˢ P₂) (productOrder P₁ R₁ P₂ R₂) φ (standardTuple v) := by
    have h := (forcingFormula_nameAction_iff hR hπ' φ v hv (kpair_mem_iff.mpr ⟨hs', hp⟩)).mpr h1
    have hfix' : (fun i ↦ nameAction (secondCoordinateAction P₁ P₂ π) (v i)) = v := funext (hinv π hπ hfix)
    rwa [hfix'] at h
  rw [secondCoordinateAction_value hs' hp] at h2
  refine ⟨⟨s', r₂⟩ₖ, hreg.2.1 _ h2 _ (kpair_mem_iff.mpr ⟨hs', hr₂⟩)
    ((pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr
      ⟨hs', hr₂, hs', function_value_mem hπ.1 hp, h₁.2.1 s' hs', hr₂π⟩), ?_⟩
  exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hs', hr₂, hs', hq₂, h₁.2.1 s' hs', hr₂q⟩

end ZFVP
