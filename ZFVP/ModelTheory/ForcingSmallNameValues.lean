import ZFVP.ModelTheory.ForcingSmallFunctions
import ZFVP.SetTheory.AtomicCheckNames
import ZFVP.SetTheory.AtomicEqualityTransitivity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- All checked ordinal values of a fixed name are bounded uniformly across
generics when the forcing is small relative to an inaccessible cardinal. -/
theorem small_forcing_checked_name_values_bounded {P R one δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (τ : V) :
    ∃ β ∈ δ, ∀ p ∈ P, ∀ α ∈ δ,
      p ∈ atomicEquality P R τ (checkName one α) → α ∈ β := by
  let := hδ.1
  let g := {z ∈ P ×ˢ δ ; kpair.π₁ z ∈ atomicEquality P R τ (checkName one (kpair.π₂ z))}
  have hm (p α : V) : ⟨p, α⟩ₖ ∈ g ↔ p ∈ P ∧ α ∈ δ ∧ p ∈ atomicEquality P R τ (checkName one α) := by
    simp only [g, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]
  have hf : g ∈ δ ^ domain g := by
    apply mem_function.intro
    · intro z hz
      obtain ⟨p, _, α, hα, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
      exact mem_prod_iff.mpr ⟨p, mem_domain_of_kpair_mem hz, α, hα, rfl⟩
    · intro p hp
      obtain ⟨α, hpa⟩ := mem_domain_iff.mp hp
      refine ⟨α, hpa, fun β hpb ↦ ?_⟩
      have ha := ((hm p α).mp hpa).2.2
      have hb := ((hm p β).mp hpb).2.2
      rw [atomicEquality_symm P R τ (checkName one β)] at hb
      exact atomicEquality_checkName_injective hR ht β α p
        (atomicEquality_trans hR _ τ _ p hb ha)
  have hd : domain g ⊆ P := by
    intro p hp
    obtain ⟨α, hpa⟩ := mem_domain_iff.mp hp
    exact ((hm p α).mp hpa).1
  have hdom : domain g ∈ hierarchy δ :=
    subset_mem_hierarchy_limit (fun _ hα ↦ regularCardinal_succ_closed hδ.regular hα) hP hd
  have hn : NoLowRankCofinalMaps δ := fun _ hX _ ↦ hδ.no_rank_cofinalMap hX
  obtain ⟨β, hβ, hb⟩ := hn.map_bounded hdom hf
  let := IsFunction.of_mem hf
  refine ⟨β, hβ, ?_⟩
  intro p hp α hα he
  have hpa := (hm p α).mpr ⟨hp, hα, he⟩
  exact value_eq_of_kpair_mem hpa ▸ hb p (mem_domain_of_kpair_mem hpa)

end ZFVP
