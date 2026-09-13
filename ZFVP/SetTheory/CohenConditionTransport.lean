import ZFVP.SetTheory.CohenSupportProjection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cohenConditionAction_union (I π p q : V) :
    cohenConditionAction I π (p ∪ q) = cohenConditionAction I π p ∪ cohenConditionAction I π q := by
  apply mem_ext
  intro z
  simp only [cohenConditionAction, mem_permutedGraph, mem_union_iff]
  constructor
  · rintro ⟨u, hu | hu, he⟩
    · exact Or.inl ⟨u, hu, he⟩
    · exact Or.inr ⟨u, hu, he⟩
  · rintro (⟨u, hu, he⟩ | ⟨u, hu, he⟩)
    · exact ⟨u, Or.inl hu, he⟩
    · exact ⟨u, Or.inr hu, he⟩

theorem cohenConditionAction_mono {I π p q : V} (h : p ⊆ q) :
    cohenConditionAction I π p ⊆ cohenConditionAction I π q := permutedGraph_mono h

theorem cohenConditionAction_eq_of_agree {I p π ρ : V}
    (hp : p ∈ cohenConditions I)
    (hagree : ∀ i ∈ cohenSupport p, π ‘ i = ρ ‘ i) :
    cohenConditionAction I π p = cohenConditionAction I ρ p := by
  have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hp).2.1
  have he : ∀ z ∈ p,
      permutedGraphEntry (productPermutation I (ω : V) π) z =
        permutedGraphEntry (productPermutation I (ω : V) ρ) z := by
    intro z hz
    obtain ⟨x, b, rfl⟩ := IsFunction.mem_eq_kpair hz
    obtain ⟨i, hi, n, hn, rfl⟩ := mem_prod_iff.mp
      (finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hz))
    simp only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair, productPermutation_value hi hn,
      hagree i ((mem_cohenSupport p i).mpr ⟨n, b, hz⟩)]
  apply mem_ext
  intro z
  simp only [cohenConditionAction, mem_permutedGraph]
  constructor
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu, hz.trans (he u hu)⟩
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu, hz.trans (he u hu).symm⟩

theorem cohenConditionAction_compose {I π ρ p : V}
    (hπ : IsInternalPermutation I π) (hρ : IsInternalPermutation I ρ)
    (hp : p ∈ cohenConditions I) :
    cohenConditionAction I ρ (cohenConditionAction I π p) = cohenConditionAction I (compose π ρ) p := by
  rw [← cohenPermutation_value (cohenConditionAction_condition hπ hp),
    ← cohenPermutation_value hp, ← cohenPermutation_value hp,
    cohenPermutation_compose hπ hρ,
    value_compose_of_mem_function (cohenPermutation_automorphism hπ).1
      (cohenPermutation_automorphism hρ).1 hp]

theorem cohenConditionAction_support {I π p : V} (hp : p ∈ cohenConditions I) :
    cohenSupport (cohenConditionAction I π p) =
      repl (fun i ↦ π ‘ i) (by definability) (cohenSupport p) := by
  apply mem_ext
  intro j
  simp only [mem_cohenSupport, cohenConditionAction_pair_iff hp, repl_spec]
  constructor
  · rintro ⟨n, b, i, hi, he⟩
    exact ⟨i, ⟨n, b, hi⟩, he⟩
  · rintro ⟨i, ⟨n, b, hi⟩, he⟩
    exact ⟨n, b, i, hi, he⟩

end ZFVP
