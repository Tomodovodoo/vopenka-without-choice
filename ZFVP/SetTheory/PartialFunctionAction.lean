import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.InternalPermutations

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def permutedGraphEntry (π z : V) : V := ⟨π ‘ (kpair.π₁ z), kpair.π₂ z⟩ₖ

instance permutedGraphEntry_definable : ℒₛₑₜ-function₂[V] permutedGraphEntry := by
  unfold permutedGraphEntry
  definability

noncomputable def permutedGraph (π p : V) : V := repl (permutedGraphEntry π) (by definability) p

instance permutedGraph_definable : ℒₛₑₜ-function₂[V] permutedGraph := by
  have h : ℒₛₑₜ-relation₃[V] (fun q π p ↦ ∀ z, z ∈ q ↔ ∃ u ∈ p, z = permutedGraphEntry π u) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = permutedGraph (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [permutedGraph, repl_spec]

theorem mem_permutedGraph (π p z : V) :
    z ∈ permutedGraph π p ↔ ∃ u ∈ p, z = permutedGraphEntry π u := repl_spec _

theorem pair_mem_permutedGraph (π p x y : V) [IsFunction p] :
    ⟨x, y⟩ₖ ∈ permutedGraph π p ↔ ∃ u, ⟨u, y⟩ₖ ∈ p ∧ x = π ‘ u := by
  constructor
  · intro h
    obtain ⟨z, hz, he⟩ := (mem_permutedGraph π p _).mp h
    obtain ⟨u, v, rfl⟩ := IsFunction.mem_eq_kpair hz
    have he' : x = π ‘ u ∧ y = v := by simpa only [permutedGraphEntry,
      kpair.π₁_kpair, kpair.π₂_kpair, kpair_iff] using he
    exact ⟨u, he'.2.symm ▸ hz, he'.1⟩
  · rintro ⟨u, hu, rfl⟩
    exact (mem_permutedGraph π p _).mpr ⟨⟨u, y⟩ₖ, hu, by simp [permutedGraphEntry]⟩

theorem permutedGraph_mono {π p q : V} (h : p ⊆ q) :
    permutedGraph π p ⊆ permutedGraph π q := by
  intro z hz
  obtain ⟨u, hu, he⟩ := (mem_permutedGraph π p z).mp hz
  exact (mem_permutedGraph π q z).mpr ⟨u, h u hu, he⟩

theorem permutedGraph_condition {D B π p : V} (hπ : IsInternalPermutation D π)
    (hp : p ∈ finitePartialFunctions D B) :
    permutedGraph π p ∈ finitePartialFunctions D B := by
  obtain ⟨hpD, hpf, hpfin⟩ := (mem_finitePartialFunctions D B p).mp hp
  have : IsFunction p := hpf
  have hsub : permutedGraph π p ⊆ D ×ˢ B := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph π p z).mp hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    obtain ⟨hx, hy⟩ := kpair_mem_iff.mp (hpD _ hu)
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair] using
      kpair_mem_iff.mpr ⟨function_value_mem hπ.1 hx, hy⟩
  have hfun : IsFunction (permutedGraph π p) := by
    apply isFunction_iff.mpr
    apply mem_function.intro
    · intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (hsub z hz)
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hz, mem_range_of_kpair_mem hz⟩
    · intro x hx
      obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
      refine ⟨y, hxy, ?_⟩
      intro z hxz
      obtain ⟨u, huy, hxu⟩ := (pair_mem_permutedGraph π p x y).mp hxy
      obtain ⟨v, hvz, hxv⟩ := (pair_mem_permutedGraph π p x z).mp hxz
      have huv : u = v := injective_value_eq hπ.1 hπ.2.1
        (kpair_mem_iff.mp (hpD _ huy)).1 (kpair_mem_iff.mp (hpD _ hvz)).1 (hxu.symm.trans hxv)
      subst v
      exact IsFunction.unique hvz huy
  exact (mem_finitePartialFunctions D B _).mpr ⟨hsub, hfun,
    internallyFinite_domain (internallyFinite_repl _ _ (internallyFinite_function hpfin))⟩

theorem permutedGraph_identity {D B p : V} (hp : p ∈ finitePartialFunctions D B) :
    permutedGraph (identity D) p = p := by
  have : IsFunction p := ((mem_finitePartialFunctions D B p).mp hp).2.1
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph _ p z).mp hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    have hx : x ∈ D := finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hu)
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair, identity_value hx] using hu
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact (pair_mem_permutedGraph _ p x y).mpr ⟨x, hz,
      (identity_value (finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hz))).symm⟩

theorem permutedGraph_compose {D B π ρ p : V} (hπ : IsInternalPermutation D π)
    (hρ : IsInternalPermutation D ρ) (hp : p ∈ finitePartialFunctions D B) :
    permutedGraph ρ (permutedGraph π p) = permutedGraph (compose π ρ) p := by
  apply mem_ext
  intro z
  simp only [mem_permutedGraph]
  have hv (u : V) (hu : u ∈ p) :
      permutedGraphEntry ρ (permutedGraphEntry π u) = permutedGraphEntry (compose π ρ) u := by
    have : IsFunction p := ((mem_finitePartialFunctions D B p).mp hp).2.1
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    have hx : x ∈ D := finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hu)
    simp only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair,
      value_compose_of_mem_function hπ.1 hρ.1 hx]
  constructor
  · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, hv u hu⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨permutedGraphEntry π u, ⟨u, hu, rfl⟩, (hv u hu).symm⟩

theorem permutedGraph_inverse {D B π p : V} (hπ : IsInternalPermutation D π)
    (hp : p ∈ finitePartialFunctions D B) :
    permutedGraph (converseGraph π) (permutedGraph π p) = p := by
  rw [permutedGraph_compose hπ hπ.inv hp,
    forcingAutomorphism_compose_inverse ((internalPermutation_iff_emptyOrder D π).mp hπ),
    permutedGraph_identity hp]

end ZFVP
