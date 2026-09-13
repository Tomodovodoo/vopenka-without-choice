import ZFVP.SetTheory.AtomicForcingDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingSaturatedNameFormula : SetTheorySemisentence 5 :=
  f“N P R U Q. ∀ z, z ∈ N ↔ z ∈ !prod.dfn U P ∧
    !forcingNameFormula P (!kpair.π₁.dfn z) ∧
    !kpair.π₂.dfn z ∈ !atomicMembershipFormula P R (!kpair.π₁.dfn z) Q”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Include every permitted name together with every condition forcing its membership. -/
noncomputable def forcingSaturatedName (P R U Q : V) : V :=
  {z ∈ U ×ˢ P ; IsForcingName P (kpair.π₁ z) ∧
    kpair.π₂ z ∈ atomicMembership P R (kpair.π₁ z) Q}

instance forcingSaturatedNameFormula_defined :
    ℒₛₑₜ-function₄[V] forcingSaturatedName via forcingSaturatedNameFormula :=
  ⟨fun v ↦ by
    change forcingSaturatedNameFormula.Evalb v ↔ v 0 = forcingSaturatedName (v 1) (v 2) (v 3) (v 4)
    rw [mem_ext_iff]
    simp [forcingSaturatedNameFormula, forcingSaturatedName]⟩

instance forcingSaturatedName_definable : ℒₛₑₜ-function₄[V] forcingSaturatedName :=
  forcingSaturatedNameFormula_defined.to_definable

theorem pair_mem_forcingSaturatedName (P R U Q τ p : V) :
    ⟨τ, p⟩ₖ ∈ forcingSaturatedName P R U Q ↔
      τ ∈ U ∧ p ∈ P ∧ IsForcingName P τ ∧ p ∈ atomicMembership P R τ Q := by
  simp [forcingSaturatedName, and_assoc]

theorem forcingSaturatedName_isName (P R U Q : V) : IsForcingName P (forcingSaturatedName P R U Q) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨hzU, hzN, hzM⟩ := mem_sep_iff.mp hz
  obtain ⟨τ, hτ, p, hp, rfl⟩ := mem_prod_iff.mp hzU
  exact ⟨τ, p, hp, rfl, by simpa only [kpair.π₁_kpair] using hzN⟩

theorem forcingSaturatedName_subset (P R U Q : V) : forcingSaturatedName P R U Q ⊆ U ×ˢ P := sep_subset

theorem forcingSaturatedName_domain_subset (P R U Q : V) : domain (forcingSaturatedName P R U Q) ⊆ U := by
  intro τ hτ
  obtain ⟨p, hp⟩ := mem_domain_iff.mp hτ
  exact ((pair_mem_forcingSaturatedName _ _ _ _ _ _).mp hp).1

theorem forcingSaturatedName_mem_domain {P R U Q τ p : V}
    (hτ : τ ∈ U) (hp : p ∈ P) (hname : IsForcingName P τ)
    (hmem : p ∈ atomicMembership P R τ Q) : τ ∈ domain (forcingSaturatedName P R U Q) :=
  mem_domain_of_kpair_mem ((pair_mem_forcingSaturatedName _ _ _ _ _ _).mpr ⟨hτ, hp, hname, hmem⟩)

theorem forcingSaturatedName_forces_member {P R U Q τ p : V}
    (hR : IsForcingPreorder P R) (hτ : τ ∈ U) (hp : p ∈ P) (hname : IsForcingName P τ)
    (hmem : p ∈ atomicMembership P R τ Q) : p ∈ atomicMembership P R τ (forcingSaturatedName P R U Q) :=
  atomicMembership_of_pair hR hp ((pair_mem_forcingSaturatedName _ _ _ _ _ _).mpr ⟨hτ, hp, hname, hmem⟩)

end ZFVP

