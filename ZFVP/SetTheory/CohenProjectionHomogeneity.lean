import ZFVP.SetTheory.CohenSupportProjection
import ZFVP.SetTheory.FinitePermutationExtension
import ZFVP.SetTheory.CohenLeastSupport
import ZFVP.SetTheory.SymmetricFormulaForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An invariant regular truth set only depends on the rows in its finite support. -/
theorem cohen_regular_restrict {E A p : V}
    (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (hA : IsForcingRegular (cohenConditions (ω : V)) (cohenOrder (ω : V)) A)
    (hinv : ∀ π, IsInternalPermutation (ω : V) π → (∀ i ∈ E, π ‘ i = i) →
      ∀ q ∈ cohenConditions (ω : V), (cohenPermutation (ω : V) π) ‘ q ∈ A ↔ q ∈ A)
    (hp : p ∈ A) : cohenConditionRestrict p E ∈ A := by
  have hpP := hA.1 p hp
  apply hA.2.2 _ (cohenConditionRestrict_condition hpP E)
  intro q hq hqr
  let X := {i ∈ cohenSupport p ; i ∉ E}
  have hX : IsInternallyFinite X := internallyFinite_subset (cohenSupport_finite hpP) sep_subset
  have hXω : X ⊆ (ω : V) := fun i hi ↦ cohenSupport_subset hpP i (mem_sep_iff.mp hi).1
  obtain ⟨π, hπ, hfix, hmove⟩ := exists_permutation_moving_fixing hEf hEω hX hXω
    (cohenSupport_finite hq) (cohenSupport_subset hq) (fun _ hi ↦ (mem_sep_iff.mp hi).2)
  have hc := cohenConditionRestrict_compatible hpP hq hπ hfix
    (fun i hi hiE ↦ hmove i (mem_sep_iff.mpr ⟨hi, hiE⟩))
    ((pair_mem_cohenOrder _ _ _).mp hqr).2.2
  obtain ⟨r, hr, hrq, hrp⟩ := hc
  have hpA := (hinv π hπ hfix p hpP).mpr hp
  rw [cohenPermutation_value hpP] at hpA
  exact ⟨r, hA.2.1 _ hpA r hr hrp, hrq⟩

/-- Equality of supported Cohen names can be forced using only their common support. -/
theorem cohen_atomicEquality_restrict {E τ σ p : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ)
    (hσ : IsForcingName (cohenConditions (ω : V)) σ)
    (hEτ : IsCohenNameSupport τ E) (hEσ : IsCohenNameSupport σ E)
    (hp : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ) :
    cohenConditionRestrict p E ∈
      atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ := by
  apply cohen_regular_restrict hEτ.1 hEτ.2.1
    (atomicEquality_regular (cohen_poset (ω : V)).1 τ σ) ?_ hp
  intro π hπ hfix q hq
  have hh := atomicEquality_nameAction_iff (cohenPermutation_automorphism hπ) hτ hσ hq
  rwa [hEτ.2.2 π hπ hfix, hEσ.2.2 π hπ hfix] at hh

theorem cohen_atomicMembership_restrict {E τ σ p : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ)
    (hσ : IsForcingName (cohenConditions (ω : V)) σ)
    (hEτ : IsCohenNameSupport τ E) (hEσ : IsCohenNameSupport σ E)
    (hp : p ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ) :
    cohenConditionRestrict p E ∈
      atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ := by
  apply cohen_regular_restrict hEτ.1 hEτ.2.1
    (atomicMembership_regular (cohen_poset (ω : V)).1 τ σ) ?_ hp
  intro π hπ hfix q hq
  have hh := atomicMembership_nameAction_iff (cohenPermutation_automorphism hπ) hτ hσ hq
  rwa [hEτ.2.2 π hπ hfix, hEσ.2.2 π hπ hfix] at hh

/-- Jech's support-projection homogeneity lemma, for every standard formula of the symmetric
forcing language. It holds in arbitrary ZF grounds, without a generic filter or ground choice. -/
theorem cohen_symmetricForcingFormula_restrict {E p : V} {n : ℕ}
    (φ : SetTheorySemisentence n) (v : Fin n → V)
    (hv : ∀ i, IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) (v i))
    (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (hE : ∀ i, ∀ π, IsInternalPermutation (ω : V) π → (∀ j ∈ E, π ‘ j = j) →
      nameAction (cohenPermutation (ω : V) π) (v i) = v i)
    (hp : p ∈ symmetricForcingFormula (cohenConditions (ω : V)) (cohenOrder (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) φ (standardTuple v)) :
    cohenConditionRestrict p E ∈
      symmetricForcingFormula (cohenConditions (ω : V)) (cohenOrder (ω : V))
        (cohenGroup (ω : V)) (cohenFilter (ω : V)) φ (standardTuple v) := by
  apply cohen_regular_restrict hEω hEf
    (symmetricForcingFormula_regular (cohen_poset (ω : V)).1 _ _ φ _) ?_ hp
  intro π hπ hfix q hq
  exact symmetricForcingFormula_fixed_iff (cohen_poset (ω : V)).1
    (cohenGroup_group (ω : V)) (cohenFilter_normal (ω : V))
    ((mem_cohenGroup (ω : V) _).mpr ⟨π, hπ, rfl⟩) φ v hv
    (fun i ↦ hE i π hπ hfix) hq

end ZFVP
