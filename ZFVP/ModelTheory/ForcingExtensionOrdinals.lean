import ZFVP.ModelTheory.ForcingExtensionDomain
import ZFVP.SetTheory.NameValueRank

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinal_mem_forcingExtension_ground {P G α : V} [IsOrdinal α]
    (hα : α ∈ forcingExtensionDomain U P G) : α ∈ U := by
  obtain ⟨τ, hτU, _, he⟩ := (mem_forcingExtensionDomain_iff _ _ _ _).mp hα
  let τ' : SetDomain U := ⟨τ, hτU⟩
  have hrU := (rank τ').property
  rw [rank_val U] at hrU
  have hbound : α ⊆ rank τ := by
    have hb := rank_nameValue_subset G τ
    rw [← he, rank_of_ordinal] at hb
    exact hb
  rcases IsOrdinal.subset_iff.mp hbound with h | h
  · exact h.symm ▸ hrU
  · exact (inferInstance : IsTransitive U).mem_trans h hrU

theorem ordinal_mem_forcingExtension_iff (P one : SetDomain U) (G : V)
    (honeP : one ∈ P) (honeG : one.val ∈ G) (α : V) [IsOrdinal α] :
    α ∈ forcingExtensionDomain U P.val G ↔ α ∈ U :=
  ⟨ordinal_mem_forcingExtension_ground U,
    ground_subset_forcingExtensionDomain U P one G honeP honeG α⟩

theorem ordinal_mem_symmetricExtension_ground {P Γ F G α : V} [IsOrdinal α]
    (hα : α ∈ symmetricExtensionDomain U P Γ F G) : α ∈ U :=
  ordinal_mem_forcingExtension_ground U (symmetricExtensionDomain_subset U P Γ F G α hα)

theorem ordinal_mem_symmetricExtension_iff (P one : SetDomain U) (R Γ F G : V)
    (hR : IsForcingPoset P.val R) (hΓ : IsForcingAutomorphismGroup P.val R Γ)
    (hF : IsNormalSubgroupFilter P.val Γ F) (hone : IsForcingTop P.val R one.val)
    (honeG : one.val ∈ G) (α : V) [IsOrdinal α] :
    α ∈ symmetricExtensionDomain U P.val Γ F G ↔ α ∈ U :=
  ⟨ordinal_mem_symmetricExtension_ground U,
    ground_subset_symmetricExtensionDomain U P one R Γ F G hR hΓ hF hone honeG α⟩

end TransitiveZF
end ZFVP
