import ZFVP.SetTheory.SymmetricSystems

/-! The trivial automorphism group makes every forcing name hereditarily symmetric. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem converseGraph_identity (P : V) : converseGraph (identity P) = identity P := by
  have h := forcingAutomorphism_inverse_compose (forcingAutomorphism_identity P P)
  rw [graph_compose_identity (forcingAutomorphism_inverse (forcingAutomorphism_identity P P)).1] at h
  exact h

theorem trivialAutomorphismGroup (P R : V) : IsForcingAutomorphismGroup P R ({identity P} : V) := by
  refine ⟨?_, by simp, ?_, ?_⟩
  · intro π hπ
    have he := mem_singleton_iff.mp hπ
    exact he ▸ forcingAutomorphism_identity P R
  · intro π hπ ρ hρ
    obtain rfl := mem_singleton_iff.mp hπ
    obtain rfl := mem_singleton_iff.mp hρ
    rw [graph_compose_identity (identity_mem_function P)]
    simp
  · intro π hπ
    obtain rfl := mem_singleton_iff.mp hπ
    rw [converseGraph_identity]
    simp

theorem conjugate_trivialGroup (P : V) :
    conjugateSubgroup (identity P) ({identity P} : V) = {identity P} := by
  apply mem_ext
  intro x
  simp only [conjugateSubgroup, repl_spec, mem_singleton_iff, exists_eq_left,
    converseGraph_identity, graph_compose_identity (identity_mem_function P)]

theorem trivialNormalFilter (P R : V) :
    IsNormalSubgroupFilter P ({identity P} : V) ({{identity P}} : V) := by
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · intro H hH
    obtain rfl := mem_singleton_iff.mp hH
    exact forcingGroup_subgroup_self (trivialAutomorphismGroup P R)
  · intro H hH K hK hHK
    obtain rfl := mem_singleton_iff.mp hH
    exact mem_singleton_iff.mpr (subset_antisymm hK.1 hHK)
  · intro H hH K hK
    obtain rfl := mem_singleton_iff.mp hH
    obtain rfl := mem_singleton_iff.mp hK
    simp
  · intro π hπ H hH
    obtain rfl := mem_singleton_iff.mp hπ
    obtain rfl := mem_singleton_iff.mp hH
    rw [conjugate_trivialGroup]
    simp

theorem trivialNameStabilizer {P τ : V} (hτ : IsForcingName P τ) :
    nameStabilizer ({identity P} : V) τ = {identity P} := by
  apply mem_ext
  intro π
  simp only [nameStabilizer, mem_sep_iff, mem_singleton_iff]
  constructor
  · exact And.left
  · rintro rfl
    exact ⟨rfl, nameAction_identity hτ⟩

theorem trivialHereditarilySymmetric_iff (P τ : V) :
    IsHereditarilySymmetricName P ({identity P} : V) ({{identity P}} : V) τ ↔ IsForcingName P τ := by
  refine ⟨And.left, fun hτ ↦ ⟨hτ, ?_⟩⟩
  intro σ hσ
  rw [trivialNameStabilizer (forcingName_mem_closure hτ hσ)]
  simp

end ZFVP
