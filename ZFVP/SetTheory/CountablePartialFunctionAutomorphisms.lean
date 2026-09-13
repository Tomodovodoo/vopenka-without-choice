import ZFVP.SetTheory.CountablePartialFunctions
import ZFVP.SetTheory.PartialFunctionAutomorphisms

/-! Permutations of the index set act on countable partial functions by
permuting first coordinates; each such action is a forcing automorphism. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem permutedGraph_countable_condition {D B π p : V} (hπ : IsInternalPermutation D π)
    (hp : p ∈ countablePartialFunctions D B) :
    permutedGraph π p ∈ countablePartialFunctions D B := by
  obtain ⟨hpD, hpf, hpc⟩ := (mem_countablePartialFunctions D B p).mp hp
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
  exact (mem_countablePartialFunctions D B _).mpr ⟨hsub, hfun,
    internallyCountable_domain (internallyCountable_repl _ _ (internallyCountable_function hpc))⟩

theorem permutedGraph_countable_identity {D B p : V} (hp : p ∈ countablePartialFunctions D B) :
    permutedGraph (identity D) p = p := by
  have : IsFunction p := ((mem_countablePartialFunctions D B p).mp hp).2.1
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph _ p z).mp hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    have hx : x ∈ D := countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem hu)
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair, identity_value hx] using hu
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact (pair_mem_permutedGraph _ p x y).mpr ⟨x, hz,
      (identity_value (countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem hz))).symm⟩

theorem permutedGraph_countable_compose {D B π ρ p : V} (hπ : IsInternalPermutation D π)
    (hρ : IsInternalPermutation D ρ) (hp : p ∈ countablePartialFunctions D B) :
    permutedGraph ρ (permutedGraph π p) = permutedGraph (compose π ρ) p := by
  apply mem_ext
  intro z
  simp only [mem_permutedGraph]
  have hv (u : V) (hu : u ∈ p) :
      permutedGraphEntry ρ (permutedGraphEntry π u) = permutedGraphEntry (compose π ρ) u := by
    have : IsFunction p := ((mem_countablePartialFunctions D B p).mp hp).2.1
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    have hx : x ∈ D := countablePartialFunction_domain hp _ (mem_domain_of_kpair_mem hu)
    simp only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair,
      value_compose_of_mem_function hπ.1 hρ.1 hx]
  constructor
  · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, hv u hu⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨permutedGraphEntry π u, ⟨u, hu, rfl⟩, (hv u hu).symm⟩

theorem permutedGraph_countable_inverse {D B π p : V} (hπ : IsInternalPermutation D π)
    (hp : p ∈ countablePartialFunctions D B) :
    permutedGraph (converseGraph π) (permutedGraph π p) = p := by
  rw [permutedGraph_countable_compose hπ hπ.inv hp,
    forcingAutomorphism_compose_inverse ((internalPermutation_iff_emptyOrder D π).mp hπ),
    permutedGraph_countable_identity hp]

theorem permutedGraph_countable_inverse_right {D B π p : V} (hπ : IsInternalPermutation D π)
    (hp : p ∈ countablePartialFunctions D B) :
    permutedGraph π (permutedGraph (converseGraph π) p) = p := by
  rw [permutedGraph_countable_compose hπ.inv hπ hp,
    forcingAutomorphism_inverse_compose ((internalPermutation_iff_emptyOrder D π).mp hπ),
    permutedGraph_countable_identity hp]

noncomputable def countablePartialFunctionPermutation (D B π : V) : V :=
  definableGraph (countablePartialFunctions D B) (permutedGraph π) (by definability)

instance countablePartialFunctionPermutation_definable :
    ℒₛₑₜ-function₃[V] countablePartialFunctionPermutation := by
  have h : ℒₛₑₜ-relation₄[V] (fun f D B π ↦ ∀ z, z ∈ f ↔
      ∃ p ∈ countablePartialFunctions D B, z = ⟨p, permutedGraph π p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = countablePartialFunctionPermutation (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [countablePartialFunctionPermutation, mem_definableGraph_iff]

theorem countablePartialFunctionPermutation_value {D B π p : V}
    (hp : p ∈ countablePartialFunctions D B) :
    (countablePartialFunctionPermutation D B π) ‘ p = permutedGraph π p :=
  value_definableGraph _ _ _ hp

theorem countablePartialFunctionPermutation_function {D B π : V} (hπ : IsInternalPermutation D π) :
    countablePartialFunctionPermutation D B π ∈
      countablePartialFunctions D B ^ countablePartialFunctions D B :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hp ↦ permutedGraph_countable_condition hπ hp)

theorem countablePartialFunctionPermutation_automorphism {D B π : V}
    (hπ : IsInternalPermutation D π) :
    IsForcingAutomorphism (countablePartialFunctions D B)
      (reverseInclusionOrder (countablePartialFunctions D B))
      (countablePartialFunctionPermutation D B π) := by
  have hf := countablePartialFunctionPermutation_function (B := B) hπ
  have : IsFunction (countablePartialFunctionPermutation D B π) := IsFunction.of_mem hf
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro p q z hp hq
    have hpP := (mem_of_mem_functions hf hp).1
    have hqP := (mem_of_mem_functions hf hq).1
    have he : permutedGraph π p = permutedGraph π q := by
      rw [← countablePartialFunctionPermutation_value hpP,
        ← countablePartialFunctionPermutation_value hqP]
      exact (value_eq_of_kpair_mem hp).trans (value_eq_of_kpair_mem hq).symm
    have hh := congrArg (permutedGraph (converseGraph π)) he
    simpa only [permutedGraph_countable_inverse hπ hpP,
      permutedGraph_countable_inverse hπ hqP] using hh
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    have hi := permutedGraph_countable_condition hπ.inv hq
    have hv : (countablePartialFunctionPermutation D B π) ‘
        (permutedGraph (converseGraph π) q) = q := by
      rw [countablePartialFunctionPermutation_value hi, permutedGraph_countable_inverse_right hπ hq]
    exact hv ▸ value_mem_range hf hi
  · intro p hp q hq
    rw [pair_mem_reverseInclusionOrder, pair_mem_reverseInclusionOrder,
      countablePartialFunctionPermutation_value hp, countablePartialFunctionPermutation_value hq]
    have hp' := permutedGraph_countable_condition hπ hp
    have hq' := permutedGraph_countable_condition hπ hq
    simp only [hp, hq, hp', hq', true_and]
    constructor
    · exact permutedGraph_mono
    · intro h
      have hh := permutedGraph_mono (π := converseGraph π) h
      simpa only [permutedGraph_countable_inverse hπ hp,
        permutedGraph_countable_inverse hπ hq] using hh

theorem countablePartialFunctionPermutation_identity (D B : V) :
    countablePartialFunctionPermutation D B (identity D) =
      identity (countablePartialFunctions D B) := by
  have hf := countablePartialFunctionPermutation_function (B := B) (internalPermutation_identity D)
  have : IsFunction (countablePartialFunctionPermutation D B (identity D)) := IsFunction.of_mem hf
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hf, domain_eq_of_mem_function (identity_mem_function _)]
  · intro p hp
    have hpP : p ∈ countablePartialFunctions D B := domain_eq_of_mem_function hf ▸ hp
    rw [countablePartialFunctionPermutation_value hpP, permutedGraph_countable_identity hpP,
      identity_value hpP]

theorem countablePartialFunctionPermutation_compose {D B π ρ : V}
    (hπ : IsInternalPermutation D π) (hρ : IsInternalPermutation D ρ) :
    countablePartialFunctionPermutation D B (compose π ρ) =
      compose (countablePartialFunctionPermutation D B π)
        (countablePartialFunctionPermutation D B ρ) := by
  have hf := countablePartialFunctionPermutation_function (B := B) hπ
  have hg := countablePartialFunctionPermutation_function (B := B) hρ
  have hh := countablePartialFunctionPermutation_function (B := B) (hπ.comp hρ)
  have : IsFunction (countablePartialFunctionPermutation D B (compose π ρ)) := IsFunction.of_mem hh
  have : IsFunction (compose (countablePartialFunctionPermutation D B π)
    (countablePartialFunctionPermutation D B ρ)) := IsFunction.of_mem (compose_function hf hg)
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hh, domain_eq_of_mem_function (compose_function hf hg)]
  · intro p hp
    have hpP : p ∈ countablePartialFunctions D B := domain_eq_of_mem_function hh ▸ hp
    rw [countablePartialFunctionPermutation_value hpP, value_compose_of_mem_function hf hg hpP,
      countablePartialFunctionPermutation_value hpP,
      countablePartialFunctionPermutation_value (permutedGraph_countable_condition hπ hpP)]
    exact (permutedGraph_countable_compose hπ hρ hpP).symm

theorem countablePartialFunctionPermutation_inverse {D B π : V} (hπ : IsInternalPermutation D π) :
    countablePartialFunctionPermutation D B (converseGraph π) =
      converseGraph (countablePartialFunctionPermutation D B π) := by
  have ha := countablePartialFunctionPermutation_automorphism (B := B) hπ
  have hb := countablePartialFunctionPermutation_function (B := B) hπ.inv
  have hc := (forcingAutomorphism_inverse ha).1
  have : IsFunction (countablePartialFunctionPermutation D B (converseGraph π)) := IsFunction.of_mem hb
  have : IsFunction (converseGraph (countablePartialFunctionPermutation D B π)) := IsFunction.of_mem hc
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hb, domain_eq_of_mem_function hc]
  · intro p hp
    have hpP : p ∈ countablePartialFunctions D B := domain_eq_of_mem_function hb ▸ hp
    apply injective_value_eq ha.1 ha.2.1 (function_value_mem hb hpP) (function_value_mem hc hpP)
    rw [countablePartialFunctionPermutation_value hpP,
      countablePartialFunctionPermutation_value (permutedGraph_countable_condition hπ.inv hpP),
      permutedGraph_countable_inverse_right hπ hpP]
    exact (value_converseGraph_value ha.1 ha.2.1 (ha.2.2.1.symm ▸ hpP)).symm

end ZFVP
