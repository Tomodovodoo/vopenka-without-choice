import ZFVP.SetTheory.ForcingNameHierarchy
import ZFVP.ModelTheory.ForcingModelEvaluation
import ZFVP.ModelTheory.ForcingQuotientBoundedNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingHierarchyName (P one α : V) : V := forcingNameHierarchy P α ×ˢ {one}

instance forcingHierarchyName_definable : ℒₛₑₜ-function₃[V] forcingHierarchyName := by
  unfold forcingHierarchyName
  definability

theorem forcingHierarchyName_isName {P one α : V} (ho : one ∈ P) [IsOrdinal α] :
    IsForcingName P (forcingHierarchyName P one α) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ν, hν, p, hp, rfl⟩ := mem_prod_iff.mp hz
  have he : p = one := mem_singleton_iff.mp hp
  exact ⟨ν, p, he ▸ ho, rfl, forcingNameHierarchy_names P α ν hν⟩

theorem forcingHierarchyName_mem_level {P one α β : V} (ho : one ∈ P) [IsOrdinal β]
    (hα : α ∈ β) : forcingHierarchyName P one α ∈ forcingNameHierarchy P β := by
  apply (mem_forcingNameHierarchy P β _).mpr
  refine ⟨α, hα, ?_⟩
  intro z hz
  obtain ⟨ν, hν, p, hp, rfl⟩ := mem_prod_iff.mp hz
  exact kpair_mem_iff.mpr ⟨hν, (mem_singleton_iff.mp hp) ▸ ho⟩

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def hierarchyName (α : V) [IsOrdinal α] : ForcingName A.P :=
  ⟨forcingHierarchyName A.P A.one α, forcingHierarchyName_isName A.top.1⟩

theorem mem_hierarchyName_iff (α : V) [IsOrdinal α] (x : A.Model) :
    x ∈ A.ofName (A.hierarchyName α) ↔
      ∃ τ : ForcingName A.P, τ.val ∈ forcingNameHierarchy A.P α ∧ x = A.ofName τ := by
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨τ, p, _hp, hτp, he⟩
    exact ⟨τ, (kpair_mem_iff.mp hτp).1, he⟩
  · rintro ⟨τ, hτ, he⟩
    exact ⟨τ, A.one, externalForcingFilter_top A.generic.1 A.top,
      kpair_mem_iff.mpr ⟨hτ, by simp⟩, he⟩

theorem subset_hierarchyName_representative (α : V) [IsOrdinal α] (x : A.Model)
    (hx : x ⊆ A.ofName (A.hierarchyName α)) :
    ∃ τ : ForcingName A.P, τ.val ⊆ forcingNameHierarchy A.P α ×ˢ A.P ∧ A.ofName τ = x := by
  obtain ⟨τ, hτ, he⟩ := forcingQuotient_boundedRepresentative A.P A.R A.G A.order A.generic
    (A.hierarchyName α) x hx
  refine ⟨τ, ?_, he⟩
  intro z hz
  obtain ⟨ν, hν, p, hp, rfl⟩ := mem_prod_iff.mp (hτ z hz)
  obtain ⟨q, hνq⟩ := mem_domain_iff.mp hν
  exact kpair_mem_iff.mpr ⟨(kpair_mem_iff.mp hνq).1, hp⟩

end ForcingContext
end ZFVP
