import ZFVP.ModelTheory.ProductForcingEquivalence
import ZFVP.ModelTheory.DensePreimageGeneric

/-! The converse product lemma: if `G₁` is `P₁`-generic over `V` and `H` is generic over `V[G₁]`
for the check of a ground poset `P₂`, then the pairs `⟨p, q⟩` with `p ∈ G₁` and `q̌ ∈ H` form a
`P₁ × P₂`-generic over `V`, and `V[G₁][H]` is the product extension. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The combined generic on the product. -/
def combinedGeneric (C : ForcingContext V) (Q : ForcingContext C.Model) : Set V :=
  {z | ∃ p q : V, z = ⟨p, q⟩ₖ ∧ p ∈ C.G ∧ C.check q ∈ Q.G}

section

variable (C : ForcingContext V) {P₂ R₂ one₂ : V} (h₂ : IsForcingPreorder P₂ R₂)
  (t₂ : IsForcingTop P₂ R₂ one₂) (Q : ForcingContext C.Model)
  (hP : Q.P = C.check P₂) (hR : Q.R = C.check R₂)

include hP hR in
theorem combinedGeneric_generic :
    IsExternalForcingGeneric (C.P ×ˢ P₂) (productOrder C.P C.R P₂ R₂) (combinedGeneric C Q) := by
  have hQsub : ∀ y ∈ Q.G, ∃ q ∈ P₂, y = C.check q := by
    intro y hy
    have := Q.generic.1.1 y hy
    rw [hP] at this
    exact (C.mem_check_iff _ _).mp this
  have hQord : ∀ q q' : V, ⟨C.check q, C.check q'⟩ₖ ∈ Q.R ↔ ⟨q, q'⟩ₖ ∈ R₂ := by
    intro q q'
    rw [hR, ← C.check_kpair, C.check_mem_iff]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro z ⟨p, q, rfl, hp, hq⟩
    obtain ⟨q', hq', he⟩ := hQsub _ hq
    rw [C.check_eq_iff] at he
    exact kpair_mem_iff.mpr ⟨C.generic.1.1 p hp, he ▸ hq'⟩
  · obtain ⟨p, hp⟩ := C.generic.1.2.1
    obtain ⟨y, hy⟩ := Q.generic.1.2.1
    obtain ⟨q, _, rfl⟩ := hQsub y hy
    exact ⟨⟨p, q⟩ₖ, p, q, rfl, hp, hy⟩
  · rintro z ⟨p, q, rfl, hp, hq⟩ z' hz' hzz'
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_prod_iff.mp hz'
    obtain ⟨_, _, _, _, hpp', hqq'⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hzz'
    refine ⟨p', q', rfl, C.generic.1.2.2.1 p hp p' hp' hpp', ?_⟩
    apply Q.generic.1.2.2.1 _ hq _ (by rw [hP]; exact (C.check_mem_iff _ _).mpr hq')
    exact (hQord q q').mpr hqq'
  · rintro z ⟨p, q, rfl, hp, hq⟩ z' ⟨p', q', rfl, hp', hq'⟩
    obtain ⟨r, hr, hrp, hrp'⟩ := C.generic.1.2.2.2 p hp p' hp'
    obtain ⟨s, hs, hsq, hsq'⟩ := Q.generic.1.2.2.2 _ hq _ hq'
    obtain ⟨s₀, hs₀, rfl⟩ := hQsub s hs
    obtain ⟨q₀, hq₀, he⟩ := hQsub _ hq
    obtain ⟨q₀', hq₀', he'⟩ := hQsub _ hq'
    rw [C.check_eq_iff] at he he'
    subst he
    subst he'
    refine ⟨⟨r, s₀⟩ₖ, ⟨r, s₀, rfl, hr, hs⟩, ?_, ?_⟩
    · exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨C.generic.1.1 r hr, hs₀, C.generic.1.1 p hp,
        hq₀, hrp, (hQord _ _).mp hsq⟩
    · exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨C.generic.1.1 r hr, hs₀, C.generic.1.1 p' hp',
        hq₀', hrp', (hQord _ _).mp hsq'⟩
  · intro D hD
    -- the second coordinates of members of `D` with first coordinate in `G₁` are dense over `V[G₁]`
    let D' : C.Model := {y ∈ C.check P₂ ; ∃ p ∈ C.genericSet, ⟨p, y⟩ₖ ∈ C.check D}
    have hD' : ForcingDense Q.P Q.R D' := by
      refine ⟨fun y hy ↦ by rw [hP]; exact (mem_sep_iff.mp hy).1, fun y hy ↦ ?_⟩
      rw [hP] at hy
      obtain ⟨q₀, hq₀, rfl⟩ := (C.mem_check_iff _ _).mp hy
      -- the first coordinates of members of `D` below `⟨·, q₀⟩` are dense in `P₁`
      have hE : ForcingDense C.P C.R {p ∈ C.P ; ∃ q ∈ P₂, ⟨q, q₀⟩ₖ ∈ R₂ ∧ ⟨p, q⟩ₖ ∈ D} := by
        refine ⟨sep_subset, fun p hp ↦ ?_⟩
        obtain ⟨d, hd, hdp⟩ := hD.2 ⟨p, q₀⟩ₖ (kpair_mem_iff.mpr ⟨hp, hq₀⟩)
        obtain ⟨p', hp', q', hq', rfl⟩ := mem_prod_iff.mp (hD.1 d hd)
        obtain ⟨_, _, _, _, hpp', hqq'⟩ := (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hdp
        exact ⟨p', mem_sep_iff.mpr ⟨hp', q', hq', hqq', hd⟩, hpp'⟩
      obtain ⟨p, hpG, hpE⟩ := C.generic.2 _ hE
      obtain ⟨hpP, q, hq, hqq₀, hpqD⟩ := mem_sep_iff.mp hpE
      refine ⟨C.check q, mem_sep_iff.mpr ⟨(C.check_mem_iff _ _).mpr hq, C.check p,
        (C.check_mem_genericSet_iff p).mpr hpG, ?_⟩, ?_⟩
      · rw [← C.check_kpair, C.check_mem_iff]
        exact hpqD
      · exact (hQord q q₀).mpr hqq₀
    obtain ⟨y, hyG, hyD'⟩ := Q.generic.2 D' hD'
    obtain ⟨hyP, p, hp, hpy⟩ := mem_sep_iff.mp hyD'
    obtain ⟨q, _, rfl⟩ := (C.mem_check_iff _ _).mp hyP
    obtain ⟨p₀, hp₀, rfl⟩ := (C.mem_genericSet_iff p).mp hp
    rw [← C.check_kpair, C.check_mem_iff] at hpy
    exact ⟨⟨p₀, q⟩ₖ, ⟨p₀, q, rfl, hp₀, hyG⟩, hpy⟩

include hP hR in
theorem firstProjection_combinedGeneric : firstProjectionGeneric (combinedGeneric C Q) = C.G := by
  ext p
  constructor
  · rintro ⟨q, p', q', he, hp', _⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact hp'
  · intro hp
    obtain ⟨y, hy⟩ := Q.generic.1.2.1
    have := Q.generic.1.1 y hy
    rw [hP] at this
    obtain ⟨q, _, rfl⟩ := (C.mem_check_iff _ _).mp this
    exact ⟨q, p, q, rfl, hp, hy⟩

include hP hR in
theorem secondProjection_combinedGeneric :
    secondProjectionGeneric (combinedGeneric C Q) = {q | C.check q ∈ Q.G} := by
  ext q
  constructor
  · rintro ⟨p, p', q', he, _, hq'⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact hq'
  · intro hq
    obtain ⟨p, hp⟩ := C.generic.1.2.1
    exact ⟨p, p, q, rfl, hp, hq⟩

end

end ZFVP
