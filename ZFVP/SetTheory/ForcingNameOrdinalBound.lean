import ZFVP.SetTheory.AtomicCheckNames
import ZFVP.SetTheory.AtomicEqualityTransitivity
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingName_checkedOrdinals_bounded {δ P R one : V}
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (τ : V) :
    ∃ β ∈ δ, ∀ p ∈ P, ∀ y ∈ δ,
      p ∈ atomicEquality P R τ (checkName one y) → y ∈ β := by
  let := hδ.1
  let g := {z ∈ P ×ˢ δ ; kpair.π₁ z ∈ atomicEquality P R τ (checkName one (kpair.π₂ z))}
  have hgmem (p y : V) : ⟨p, y⟩ₖ ∈ g ↔
      p ∈ P ∧ y ∈ δ ∧ p ∈ atomicEquality P R τ (checkName one y) := by
    simp [g, and_assoc]
  have hg : g ∈ δ ^ domain g := by
    apply mem_function.intro
    · intro z hz
      obtain ⟨p, _, y, hy, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hz, hy⟩
    · intro p hp
      obtain ⟨y, hpy⟩ := mem_domain_iff.mp hp
      refine ⟨y, hpy, fun w hpw ↦ ?_⟩
      have hy := (hgmem p y).mp hpy
      have hw := (hgmem p w).mp hpw
      exact atomicEquality_checkName_injective hR ht w y p
        (atomicEquality_trans hR (checkName one w) τ (checkName one y) p
          ((atomicEquality_symm P R τ (checkName one w)) ▸ hw.2.2) hy.2.2)
  have hd : domain g ∈ hierarchy δ := subset_mem_hierarchy_limit
    hδ.rankCriterion.2.2.1 hP (by
      intro p hp
      obtain ⟨y, hpy⟩ := mem_domain_iff.mp hp
      exact ((hgmem p y).mp hpy).1)
  obtain ⟨β, hβ, hb⟩ := hδ.rankCriterion.2.2.2.map_bounded hd hg
  let := IsFunction.of_mem hg
  refine ⟨β, hβ, ?_⟩
  intro p hp y hy he
  have hpy := (hgmem p y).mpr ⟨hp, hy, he⟩
  simpa only [value_eq_of_kpair_mem hpy] using hb p (mem_domain_of_kpair_mem hpy)

end ZFVP
