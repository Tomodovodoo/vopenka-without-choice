import ZFVP.SetTheory.CohenLeastSupport

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCohenNameSupport.image {τ E π : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ) (hE : IsCohenNameSupport τ E)
    (hπ : IsInternalPermutation (ω : V) π) :
    IsCohenNameSupport (nameAction (cohenPermutation (ω : V) π) τ)
      (repl (fun i ↦ π ‘ i) (by definability) E) := by
  refine ⟨?_, internallyFinite_repl _ _ hE.2.1, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := (repl_spec (by definability)).mp hi
    exact function_value_mem hπ.1 (hE.1 j hj)
  · intro θ hθ hfix
    have hκ := hE.2.2 (compose (compose π θ) (converseGraph π)) ((hπ.comp hθ).comp hπ.inv) (by
      intro i hi
      rw [value_compose_of_mem_function (hπ.comp hθ).1 hπ.inv.1 (hE.1 i hi),
        value_compose_of_mem_function hπ.1 hθ.1 (hE.1 i hi),
        hfix _ ((repl_spec (by definability)).mpr ⟨i, hi, rfl⟩), hπ.inv_value (hE.1 i hi)])
    rw [cohenPermutation_compose (hπ.comp hθ) hπ.inv, cohenPermutation_inverse hπ,
      ← nameAction_compose (cohenPermutation_automorphism (hπ.comp hθ)).1
        (forcingAutomorphism_inverse (cohenPermutation_automorphism hπ)).1 hτ,
      cohenPermutation_compose hπ hθ,
      ← nameAction_compose (cohenPermutation_automorphism hπ).1
        (cohenPermutation_automorphism hθ).1 hτ] at hκ
    have hh := congrArg (nameAction (cohenPermutation (ω : V) π)) hκ
    rw [nameAction_cancel_inverse (cohenPermutation_automorphism hπ)
      (nameAction_isName (cohenPermutation_automorphism hθ).1
        (nameAction_isName (cohenPermutation_automorphism hπ).1 hτ))] at hh
    exact hh

/-- The canonical least support commutes with the ground permutation action. -/
theorem cohenNameLeastSupport_nameAction {τ π : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hπ : IsInternalPermutation (ω : V) π) :
    cohenNameLeastSupport (nameAction (cohenPermutation (ω : V) π) τ) =
      repl (fun i ↦ π ‘ i) (by definability) (cohenNameLeastSupport τ) := by
  have hact : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V))
      (nameAction (cohenPermutation (ω : V) π) τ) :=
    hereditarilySymmetric_nameAction (cohenGroup_group (ω : V)) (cohenFilter_normal (ω : V))
      ((mem_cohenGroup (ω : V) _).mpr ⟨π, hπ, rfl⟩) hτ
  have hD := cohenNameLeastSupport_isSupport hτ
  have hD' := cohenNameLeastSupport_isSupport hact
  apply SetTheory.subset_antisymm (cohenNameLeastSupport_subset (hD.image hτ.1 hπ))
  have hinv := hD'.image hact.1 hπ.inv
  rw [cohenPermutation_inverse hπ, nameAction_inverse_cancel (cohenPermutation_automorphism hπ) hτ.1] at hinv
  intro i hi
  obtain ⟨j, hj, rfl⟩ := (repl_spec (by definability)).mp hi
  obtain ⟨k, hk, he⟩ := (repl_spec (by definability)).mp (cohenNameLeastSupport_subset hinv j hj)
  rw [he, hπ.value_inv (hD'.1 k hk)]
  exact hk

theorem cohenNameLeastSupport_image_eq_of_fixed {τ π : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hπ : IsInternalPermutation (ω : V) π)
    (hfix : nameAction (cohenPermutation (ω : V) π) τ = τ) :
    repl (fun i ↦ π ‘ i) (by definability) (cohenNameLeastSupport τ) = cohenNameLeastSupport τ := by
  rw [← cohenNameLeastSupport_nameAction hτ hπ, hfix]

end ZFVP
