import ZFVP.SetTheory.PartialFunctionAction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem permutedGraph_inverse_right {D B π p : V} (hπ : IsInternalPermutation D π)
    (hp : p ∈ finitePartialFunctions D B) :
    permutedGraph π (permutedGraph (converseGraph π) p) = p := by
  rw [permutedGraph_compose hπ.inv hπ hp,
    forcingAutomorphism_inverse_compose ((internalPermutation_iff_emptyOrder D π).mp hπ),
    permutedGraph_identity hp]

noncomputable def partialFunctionPermutation (D B π : V) : V :=
  definableGraph (finitePartialFunctions D B) (permutedGraph π) (by definability)

instance partialFunctionPermutation_definable : ℒₛₑₜ-function₃[V] partialFunctionPermutation := by
  have h : ℒₛₑₜ-relation₄[V] (fun f D B π ↦ ∀ z, z ∈ f ↔
      ∃ p ∈ finitePartialFunctions D B, z = ⟨p, permutedGraph π p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = partialFunctionPermutation (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [partialFunctionPermutation, mem_definableGraph_iff]

theorem partialFunctionPermutation_value {D B π p : V} (hp : p ∈ finitePartialFunctions D B) :
    (partialFunctionPermutation D B π) ‘ p = permutedGraph π p := value_definableGraph _ _ _ hp

theorem partialFunctionPermutation_function {D B π : V} (hπ : IsInternalPermutation D π) :
    partialFunctionPermutation D B π ∈ finitePartialFunctions D B ^ finitePartialFunctions D B :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hp ↦ permutedGraph_condition hπ hp)

theorem partialFunctionPermutation_automorphism {D B π : V} (hπ : IsInternalPermutation D π) :
    IsForcingAutomorphism (finitePartialFunctions D B)
      (reverseInclusionOrder (finitePartialFunctions D B)) (partialFunctionPermutation D B π) := by
  have hf := partialFunctionPermutation_function (B := B) hπ
  have : IsFunction (partialFunctionPermutation D B π) := IsFunction.of_mem hf
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro p q z hp hq
    have hpP := (mem_of_mem_functions hf hp).1
    have hqP := (mem_of_mem_functions hf hq).1
    have he : permutedGraph π p = permutedGraph π q := by
      rw [← partialFunctionPermutation_value hpP, ← partialFunctionPermutation_value hqP]
      exact (value_eq_of_kpair_mem hp).trans (value_eq_of_kpair_mem hq).symm
    have hh := congrArg (permutedGraph (converseGraph π)) he
    simpa only [permutedGraph_inverse hπ hpP, permutedGraph_inverse hπ hqP] using hh
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    have hi := permutedGraph_condition hπ.inv hq
    have hv : (partialFunctionPermutation D B π) ‘ (permutedGraph (converseGraph π) q) = q := by
      rw [partialFunctionPermutation_value hi, permutedGraph_inverse_right hπ hq]
    exact hv ▸ value_mem_range hf hi
  · intro p hp q hq
    rw [pair_mem_reverseInclusionOrder, pair_mem_reverseInclusionOrder,
      partialFunctionPermutation_value hp, partialFunctionPermutation_value hq]
    have hp' := permutedGraph_condition hπ hp
    have hq' := permutedGraph_condition hπ hq
    simp only [hp, hq, hp', hq', true_and]
    constructor
    · exact permutedGraph_mono
    · intro h
      have hh := permutedGraph_mono (π := converseGraph π) h
      simpa only [permutedGraph_inverse hπ hp, permutedGraph_inverse hπ hq] using hh

theorem partialFunctionPermutation_identity (D B : V) :
    partialFunctionPermutation D B (identity D) = identity (finitePartialFunctions D B) := by
  have hf := partialFunctionPermutation_function (B := B) (internalPermutation_identity D)
  have : IsFunction (partialFunctionPermutation D B (identity D)) := IsFunction.of_mem hf
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hf, domain_eq_of_mem_function (identity_mem_function _)]
  · intro p hp
    have hpP : p ∈ finitePartialFunctions D B := domain_eq_of_mem_function hf ▸ hp
    rw [partialFunctionPermutation_value hpP, permutedGraph_identity hpP, identity_value hpP]

theorem partialFunctionPermutation_compose {D B π ρ : V}
    (hπ : IsInternalPermutation D π) (hρ : IsInternalPermutation D ρ) :
    partialFunctionPermutation D B (compose π ρ) =
      compose (partialFunctionPermutation D B π) (partialFunctionPermutation D B ρ) := by
  have hf := partialFunctionPermutation_function (B := B) hπ
  have hg := partialFunctionPermutation_function (B := B) hρ
  have hh := partialFunctionPermutation_function (B := B) (hπ.comp hρ)
  have : IsFunction (partialFunctionPermutation D B (compose π ρ)) := IsFunction.of_mem hh
  have : IsFunction (compose (partialFunctionPermutation D B π) (partialFunctionPermutation D B ρ)) :=
    IsFunction.of_mem (compose_function hf hg)
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hh, domain_eq_of_mem_function (compose_function hf hg)]
  · intro p hp
    have hpP : p ∈ finitePartialFunctions D B := domain_eq_of_mem_function hh ▸ hp
    rw [partialFunctionPermutation_value hpP, value_compose_of_mem_function hf hg hpP,
      partialFunctionPermutation_value hpP, partialFunctionPermutation_value (permutedGraph_condition hπ hpP)]
    exact (permutedGraph_compose hπ hρ hpP).symm

theorem partialFunctionPermutation_inverse {D B π : V} (hπ : IsInternalPermutation D π) :
    partialFunctionPermutation D B (converseGraph π) = converseGraph (partialFunctionPermutation D B π) := by
  have ha := partialFunctionPermutation_automorphism (B := B) hπ
  have hb := partialFunctionPermutation_function (B := B) hπ.inv
  have hc := (forcingAutomorphism_inverse ha).1
  have : IsFunction (partialFunctionPermutation D B (converseGraph π)) := IsFunction.of_mem hb
  have : IsFunction (converseGraph (partialFunctionPermutation D B π)) := IsFunction.of_mem hc
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hb, domain_eq_of_mem_function hc]
  · intro p hp
    have hpP : p ∈ finitePartialFunctions D B := domain_eq_of_mem_function hb ▸ hp
    apply injective_value_eq ha.1 ha.2.1 (function_value_mem hb hpP) (function_value_mem hc hpP)
    rw [partialFunctionPermutation_value hpP,
      partialFunctionPermutation_value (permutedGraph_condition hπ.inv hpP), permutedGraph_inverse_right hπ hpP]
    exact (value_converseGraph_value ha.1 ha.2.1 (ha.2.2.1.symm ▸ hpP)).symm

end ZFVP
