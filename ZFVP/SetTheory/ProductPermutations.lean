import ZFVP.SetTheory.InternalPermutations

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def productPermutationValue (π z : V) : V := ⟨π ‘ (kpair.π₁ z), kpair.π₂ z⟩ₖ

instance productPermutationValue_definable : ℒₛₑₜ-function₂[V] productPermutationValue := by
  unfold productPermutationValue
  definability

noncomputable def productPermutation (I J π : V) : V :=
  definableGraph (I ×ˢ J) (productPermutationValue π) (by definability)

instance productPermutation_definable : ℒₛₑₜ-function₃[V] productPermutation := by
  have h : ℒₛₑₜ-relation₄[V] (fun f I J π ↦ ∀ z, z ∈ f ↔
      ∃ p ∈ I ×ˢ J, z = ⟨p, productPermutationValue π p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = productPermutation (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [productPermutation, mem_definableGraph_iff]

theorem productPermutation_value {I J π i j : V} (hi : i ∈ I) (hj : j ∈ J) :
    (productPermutation I J π) ‘ ⟨i, j⟩ₖ = ⟨π ‘ i, j⟩ₖ := by
  rw [show productPermutation I J π = definableGraph (I ×ˢ J) (productPermutationValue π) _ from rfl,
    value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩)]
  simp only [productPermutationValue, kpair.π₁_kpair, kpair.π₂_kpair]

theorem productPermutation_function {I J π : V} (hπ : IsInternalPermutation I π) :
    productPermutation I J π ∈ (I ×ˢ J) ^ (I ×ˢ J) := by
  apply definableGraph_mem_function_of_mapsTo
  intro z hz
  obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hz
  simpa only [productPermutationValue, kpair.π₁_kpair, kpair.π₂_kpair] using
    kpair_mem_iff.mpr ⟨function_value_mem hπ.1 hi, hj⟩

theorem productPermutation_permutation {I J π : V} (hπ : IsInternalPermutation I π) :
    IsInternalPermutation (I ×ˢ J) (productPermutation I J π) := by
  have hf := productPermutation_function (J := J) hπ
  have : IsFunction (productPermutation I J π) := IsFunction.of_mem hf
  refine ⟨hf, ?_, ?_⟩
  · intro x y z hx hy
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp (mem_of_mem_functions hf hx).1
    obtain ⟨k, hk, l, hl, rfl⟩ := mem_prod_iff.mp (mem_of_mem_functions hf hy).1
    have he := (value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm
    rw [productPermutation_value hi hj, productPermutation_value hk hl] at he
    obtain ⟨hik, rfl⟩ := kpair_iff.mp he
    rw [injective_value_eq hπ.1 hπ.2.1 hi hk hik]
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro z hz
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨k, hk, hki⟩ := hπ.surjective hi
    have he : (productPermutation I J π) ‘ ⟨k, j⟩ₖ = ⟨i, j⟩ₖ := by
      rw [productPermutation_value hk hj, hki]
    exact he ▸ value_mem_range hf (kpair_mem_iff.mpr ⟨hk, hj⟩)

theorem productPermutation_identity (I J : V) :
    productPermutation I J (identity I) = identity (I ×ˢ J) := by
  have hf := productPermutation_function (J := J) (internalPermutation_identity I)
  have : IsFunction (productPermutation I J (identity I)) := IsFunction.of_mem hf
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hf, domain_eq_of_mem_function (identity_mem_function _)]
  · intro z hz
    have hzP : z ∈ I ×ˢ J := domain_eq_of_mem_function hf ▸ hz
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hzP
    rw [productPermutation_value hi hj, identity_value hi, identity_value (kpair_mem_iff.mpr ⟨hi, hj⟩)]

theorem productPermutation_compose {I J π ρ : V}
    (hπ : IsInternalPermutation I π) (hρ : IsInternalPermutation I ρ) :
    productPermutation I J (compose π ρ) =
      compose (productPermutation I J π) (productPermutation I J ρ) := by
  have hf := productPermutation_function (J := J) hπ
  have hg := productPermutation_function (J := J) hρ
  have hh := productPermutation_function (J := J) (hπ.comp hρ)
  have : IsFunction (productPermutation I J (compose π ρ)) := IsFunction.of_mem hh
  have : IsFunction (compose (productPermutation I J π) (productPermutation I J ρ)) :=
    IsFunction.of_mem (compose_function hf hg)
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hh, domain_eq_of_mem_function (compose_function hf hg)]
  · intro z hz
    have hzP : z ∈ I ×ˢ J := domain_eq_of_mem_function hh ▸ hz
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hzP
    rw [productPermutation_value hi hj, value_compose_of_mem_function hπ.1 hρ.1 hi,
      value_compose_of_mem_function hf hg (kpair_mem_iff.mpr ⟨hi, hj⟩),
      productPermutation_value hi hj, productPermutation_value (function_value_mem hπ.1 hi) hj]

theorem productPermutation_inverse {I J π : V} (hπ : IsInternalPermutation I π) :
    productPermutation I J (converseGraph π) = converseGraph (productPermutation I J π) := by
  have ha := productPermutation_permutation (J := J) hπ
  have hb := productPermutation_function (J := J) hπ.inv
  have hc := ha.inv.1
  have : IsFunction (productPermutation I J (converseGraph π)) := IsFunction.of_mem hb
  have : IsFunction (converseGraph (productPermutation I J π)) := IsFunction.of_mem hc
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hb, domain_eq_of_mem_function hc]
  · intro z hz
    have hzP : z ∈ I ×ˢ J := domain_eq_of_mem_function hb ▸ hz
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hzP
    apply injective_value_eq ha.1 ha.2.1 (function_value_mem hb (kpair_mem_iff.mpr ⟨hi, hj⟩))
      (function_value_mem hc (kpair_mem_iff.mpr ⟨hi, hj⟩))
    rw [productPermutation_value hi hj, productPermutation_value (function_value_mem hπ.inv.1 hi) hj,
      hπ.value_inv hi, ha.value_inv (kpair_mem_iff.mpr ⟨hi, hj⟩)]

end ZFVP
