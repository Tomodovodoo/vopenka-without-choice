import ZFVP.SetTheory.CohenNameSupport
import ZFVP.SetTheory.SymmetryAction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The action on a supported name depends only on the permutation's values on its support. -/
theorem cohenNameAction_eq_of_agree_on_support {I E τ π ρ : V}
    (hτ : IsForcingName (cohenConditions I) τ) (hEI : E ⊆ I)
    (hE : ∀ θ, IsInternalPermutation I θ → (∀ i ∈ E, θ ‘ i = i) →
      nameAction (cohenPermutation I θ) τ = τ)
    (hπ : IsInternalPermutation I π) (hρ : IsInternalPermutation I ρ)
    (hagree : ∀ i ∈ E, π ‘ i = ρ ‘ i) :
    nameAction (cohenPermutation I π) τ = nameAction (cohenPermutation I ρ) τ := by
  have hfix := hE (compose π (converseGraph ρ)) (hπ.comp hρ.inv) (by
    intro i hi
    rw [value_compose_of_mem_function hπ.1 hρ.inv.1 (hEI i hi),
      hagree i hi, hρ.inv_value (hEI i hi)])
  rw [cohenPermutation_compose hπ hρ.inv, cohenPermutation_inverse hρ,
    ← nameAction_compose (cohenPermutation_automorphism hπ).1
      (forcingAutomorphism_inverse (cohenPermutation_automorphism hρ)).1 hτ] at hfix
  have hh := congrArg (nameAction (cohenPermutation I ρ)) hfix
  rw [nameAction_cancel_inverse (cohenPermutation_automorphism hρ)
    (nameAction_isName (cohenPermutation_automorphism hπ).1 hτ)] at hh
  exact hh

/-- Restricting permutations to a support preserves all information about their action. -/
theorem cohenNameAction_eq_of_restrict_eq {I E τ π ρ : V}
    (hτ : IsForcingName (cohenConditions I) τ) (hEI : E ⊆ I)
    (hE : ∀ θ, IsInternalPermutation I θ → (∀ i ∈ E, θ ‘ i = i) →
      nameAction (cohenPermutation I θ) τ = τ)
    (hπ : IsInternalPermutation I π) (hρ : IsInternalPermutation I ρ)
    (he : π ↾ E = ρ ↾ E) :
    nameAction (cohenPermutation I π) τ = nameAction (cohenPermutation I ρ) τ := by
  apply cohenNameAction_eq_of_agree_on_support hτ hEI hE hπ hρ
  intro i hi
  have : IsFunction π := IsFunction.of_mem hπ.1
  have : IsFunction ρ := IsFunction.of_mem hρ.1
  have hip : i ∈ domain π := by rw [domain_eq_of_mem_function hπ.1]; exact hEI i hi
  have hir : i ∈ domain ρ := by rw [domain_eq_of_mem_function hρ.1]; exact hEI i hi
  calc
    π ‘ i = (π ↾ E) ‘ i := (value_restrict hip hi).symm
    _ = (ρ ↾ E) ‘ i := congrArg (fun f : V ↦ f ‘ i) he
    _ = ρ ‘ i := value_restrict hir hi

/-- The restrictions to `E` of ground permutations of `I`. -/
noncomputable def cohenSupportRestrictions (I E : V) : V :=
  repl (fun π ↦ π ↾ E) (by definability) (internalPermutations I)

/-- The ground set of names in the permutation orbit of `τ`. -/
noncomputable def cohenNameOrbit (I τ : V) : V :=
  repl (fun π ↦ nameAction (cohenPermutation I π) τ) (by definability)
    (internalPermutations I)

/-- A ground graph presenting a name orbit by restrictions to its support. -/
noncomputable def cohenSupportOrbitMap (I E τ : V) : V :=
  repl (fun π ↦ ⟨π ↾ E, nameAction (cohenPermutation I π) τ⟩ₖ) (by definability)
    (internalPermutations I)

theorem mem_cohenSupportRestrictions (I E f : V) :
    f ∈ cohenSupportRestrictions I E ↔
      ∃ π, IsInternalPermutation I π ∧ f = π ↾ E := by
  simp only [cohenSupportRestrictions, repl_spec, mem_internalPermutations]

theorem mem_cohenNameOrbit (I τ σ : V) :
    σ ∈ cohenNameOrbit I τ ↔
      ∃ π, IsInternalPermutation I π ∧ σ = nameAction (cohenPermutation I π) τ := by
  simp only [cohenNameOrbit, repl_spec, mem_internalPermutations]

theorem mem_cohenSupportOrbitMap (I E τ z : V) :
    z ∈ cohenSupportOrbitMap I E τ ↔
      ∃ π, IsInternalPermutation I π ∧
        z = ⟨π ↾ E, nameAction (cohenPermutation I π) τ⟩ₖ := by
  simp only [cohenSupportOrbitMap, repl_spec, mem_internalPermutations]

/-- The orbit presentation is an internal function, not an external choice of representatives. -/
theorem cohenSupportOrbitMap_function {I E τ : V}
    (hτ : IsForcingName (cohenConditions I) τ) (hEI : E ⊆ I)
    (hE : ∀ θ, IsInternalPermutation I θ → (∀ i ∈ E, θ ‘ i = i) →
      nameAction (cohenPermutation I θ) τ = τ) :
    cohenSupportOrbitMap I E τ ∈ cohenNameOrbit I τ ^ cohenSupportRestrictions I E := by
  apply mem_function.intro
  · intro z hz
    obtain ⟨π, hπ, rfl⟩ := (mem_cohenSupportOrbitMap I E τ z).mp hz
    exact kpair_mem_iff.mpr
      ⟨(mem_cohenSupportRestrictions I E _).mpr ⟨π, hπ, rfl⟩,
       (mem_cohenNameOrbit I τ _).mpr ⟨π, hπ, rfl⟩⟩
  · intro f hf
    obtain ⟨π, hπ, rfl⟩ := (mem_cohenSupportRestrictions I E f).mp hf
    refine ⟨nameAction (cohenPermutation I π) τ,
      (mem_cohenSupportOrbitMap I E τ _).mpr ⟨π, hπ, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨ρ, hρ, he⟩ := (mem_cohenSupportOrbitMap I E τ _).mp hy
    have hrestrict := (kpair_iff.mp he).1
    exact (kpair_iff.mp he).2.trans
      (cohenNameAction_eq_of_restrict_eq hτ hEI hE hπ hρ hrestrict).symm

theorem cohenSupportOrbitMap_range (I E τ : V) :
    range (cohenSupportOrbitMap I E τ) = cohenNameOrbit I τ := by
  apply mem_ext
  intro σ
  constructor
  · intro hσ
    obtain ⟨f, hf⟩ := mem_range_iff.mp hσ
    obtain ⟨π, hπ, he⟩ := (mem_cohenSupportOrbitMap I E τ _).mp hf
    exact (mem_cohenNameOrbit I τ σ).mpr ⟨π, hπ, (kpair_iff.mp he).2⟩
  · intro hσ
    obtain ⟨π, hπ, rfl⟩ := (mem_cohenNameOrbit I τ σ).mp hσ
    exact mem_range_iff.mpr ⟨π ↾ E,
      (mem_cohenSupportOrbitMap I E τ _).mpr ⟨π, hπ, rfl⟩⟩

/-- Every hereditarily symmetric Cohen name has an internal orbit presentation by the
restrictions of permutations to an internally finite set of coordinates. -/
theorem cohenNameOrbit_finiteSupport_presentation {I τ : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions I) (cohenGroup I) (cohenFilter I) τ) :
    ∃ E, E ⊆ I ∧ IsInternallyFinite E ∧
      cohenSupportOrbitMap I E τ ∈ cohenNameOrbit I τ ^ cohenSupportRestrictions I E ∧
      range (cohenSupportOrbitMap I E τ) = cohenNameOrbit I τ := by
  obtain ⟨E, hEI, hEf, hE⟩ := cohenName_finiteSupport hτ
  exact ⟨E, hEI, hEf, cohenSupportOrbitMap_function hτ.1 hEI hE,
    cohenSupportOrbitMap_range I E τ⟩

end ZFVP
