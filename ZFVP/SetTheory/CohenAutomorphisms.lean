import ZFVP.SetTheory.CohenForcing
import ZFVP.SetTheory.PartialFunctionAutomorphisms
import ZFVP.SetTheory.ProductPermutations
import ZFVP.SetTheory.SymmetricSystems

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def cohenConditionAction (I π p : V) : V :=
  permutedGraph (productPermutation I (ω : V) π) p

instance cohenConditionAction_definable : ℒₛₑₜ-function₃[V] cohenConditionAction := by
  unfold cohenConditionAction
  definability

noncomputable def cohenPermutation (I π : V) : V :=
  partialFunctionPermutation (I ×ˢ (ω : V)) 2 (productPermutation I (ω : V) π)

instance cohenPermutation_definable : ℒₛₑₜ-function₂[V] cohenPermutation := by
  unfold cohenPermutation
  definability

theorem cohenPermutation_value {I π p : V} (hp : p ∈ cohenConditions I) :
    (cohenPermutation I π) ‘ p = cohenConditionAction I π p := partialFunctionPermutation_value hp

theorem cohenConditionAction_condition {I π p : V} (hπ : IsInternalPermutation I π)
    (hp : p ∈ cohenConditions I) : cohenConditionAction I π p ∈ cohenConditions I :=
  permutedGraph_condition (productPermutation_permutation hπ) hp

theorem cohenPermutation_automorphism {I π : V} (hπ : IsInternalPermutation I π) :
    IsForcingAutomorphism (cohenConditions I) (cohenOrder I) (cohenPermutation I π) :=
  partialFunctionPermutation_automorphism (productPermutation_permutation hπ)

theorem cohenPermutation_identity (I : V) : cohenPermutation I (identity I) = identity (cohenConditions I) := by
  unfold cohenPermutation
  rw [productPermutation_identity, partialFunctionPermutation_identity]
  rfl

theorem cohenPermutation_compose {I π ρ : V}
    (hπ : IsInternalPermutation I π) (hρ : IsInternalPermutation I ρ) :
    cohenPermutation I (compose π ρ) = compose (cohenPermutation I π) (cohenPermutation I ρ) := by
  unfold cohenPermutation
  rw [productPermutation_compose hπ hρ,
    partialFunctionPermutation_compose (productPermutation_permutation hπ) (productPermutation_permutation hρ)]

theorem cohenPermutation_inverse {I π : V} (hπ : IsInternalPermutation I π) :
    cohenPermutation I (converseGraph π) = converseGraph (cohenPermutation I π) := by
  unfold cohenPermutation
  rw [productPermutation_inverse hπ, partialFunctionPermutation_inverse (productPermutation_permutation hπ)]

noncomputable def cohenGroup (I : V) : V := repl (cohenPermutation I) (by definability) (internalPermutations I)

theorem mem_cohenGroup (I σ : V) :
    σ ∈ cohenGroup I ↔ ∃ π, IsInternalPermutation I π ∧ σ = cohenPermutation I π := by
  simp only [cohenGroup, repl_spec, mem_internalPermutations]

instance cohenGroup_definable : ℒₛₑₜ-function₁[V] cohenGroup := by
  have h : ℒₛₑₜ-relation[V] (fun G I ↦ ∀ σ, σ ∈ G ↔
      ∃ π, IsInternalPermutation I π ∧ σ = cohenPermutation I π) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenGroup (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_cohenGroup]

theorem cohenGroup_group (I : V) :
    IsForcingAutomorphismGroup (cohenConditions I) (cohenOrder I) (cohenGroup I) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨π, hπ, rfl⟩ := (mem_cohenGroup I σ).mp hσ
    exact cohenPermutation_automorphism hπ
  · exact (mem_cohenGroup I _).mpr ⟨identity I, internalPermutation_identity I, (cohenPermutation_identity I).symm⟩
  · intro σ hσ τ hτ
    obtain ⟨π, hπ, rfl⟩ := (mem_cohenGroup I σ).mp hσ
    obtain ⟨ρ, hρ, rfl⟩ := (mem_cohenGroup I τ).mp hτ
    exact (mem_cohenGroup I _).mpr ⟨compose π ρ, hπ.comp hρ, (cohenPermutation_compose hπ hρ).symm⟩
  · intro σ hσ
    obtain ⟨π, hπ, rfl⟩ := (mem_cohenGroup I σ).mp hσ
    exact (mem_cohenGroup I _).mpr ⟨converseGraph π, hπ.inv, (cohenPermutation_inverse hπ).symm⟩

theorem cohenConditionAction_pair {I π p i n b : V} (hp : p ∈ cohenConditions I)
    (he : ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ p) : ⟨⟨π ‘ i, n⟩ₖ, b⟩ₖ ∈ cohenConditionAction I π p := by
  have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hp).2.1
  have hic : ⟨i, n⟩ₖ ∈ I ×ˢ (ω : V) := finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem he)
  exact (pair_mem_permutedGraph _ p _ b).mpr
    ⟨⟨i, n⟩ₖ, he, (productPermutation_value (kpair_mem_iff.mp hic).1 (kpair_mem_iff.mp hic).2).symm⟩

theorem cohenConditionAction_pair_iff {I π p x n b : V} (hp : p ∈ cohenConditions I) :
    ⟨⟨x, n⟩ₖ, b⟩ₖ ∈ cohenConditionAction I π p ↔
      ∃ i, ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ p ∧ x = π ‘ i := by
  have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hp).2.1
  constructor
  · intro he
    obtain ⟨z, hz, hez⟩ := (pair_mem_permutedGraph _ p _ b).mp he
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp (finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hz))
    rw [productPermutation_value hi hj] at hez
    obtain ⟨hxi, rfl⟩ := kpair_iff.mp hez
    exact ⟨i, hz, hxi⟩
  · rintro ⟨i, he, rfl⟩
    exact cohenConditionAction_pair hp he

theorem cohenConditionAction_fix {I π p : V} (hp : p ∈ cohenConditions I)
    (hfix : ∀ i ∈ cohenSupport p, π ‘ i = i) : cohenConditionAction I π p = p := by
  have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hp).2.1
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph _ p z).mp hz
    obtain ⟨v, b, rfl⟩ := IsFunction.mem_eq_kpair hu
    obtain ⟨i, hi, n, hn, rfl⟩ := mem_prod_iff.mp (finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hu))
    have hif := hfix i ((mem_cohenSupport p i).mpr ⟨n, b, hu⟩)
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair, productPermutation_value hi hn, hif] using hu
  · intro hz
    obtain ⟨v, b, rfl⟩ := IsFunction.mem_eq_kpair hz
    obtain ⟨i, hi, n, hn, rfl⟩ := mem_prod_iff.mp (finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hz))
    have he := cohenConditionAction_pair (π := π) hp hz
    rwa [hfix i ((mem_cohenSupport p i).mpr ⟨n, b, hz⟩)] at he

end ZFVP
