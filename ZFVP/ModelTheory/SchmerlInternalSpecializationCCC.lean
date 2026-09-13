import ZFVP.ModelTheory.SchmerlInternalStrictFamilies

/-! The internal countable chain condition for strict specialization.
Induction and the final countable union use the model's own omega, so the
argument includes conditions of nonstandard finite cardinality. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Each antichain whose conditions have one internal finite cardinal bound
is internally countable. -/
theorem internalSpecialization_countable_antichain_of_bound (hAC : InternalChoice V)
    {D S : V} (href : ∀ x ∈ D, ⟨x, x⟩ₖ ∈ S)
    (hbelow : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
      ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S)
    (hchains : ∀ C : V, C ⊆ D →
      (∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) → IsInternallyCountable C) :
    ∀ n ∈ (ω : V), ∀ A : V,
      IsForcingAntichain (internalSpecialization D S)
        (reverseInclusionOrder (internalSpecialization D S)) A →
      (∀ p ∈ A, p ≤# n) → IsInternallyCountable A := by
  apply naturalNumber_induction (fun n ↦ ∀ A : V,
    IsForcingAntichain (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) A →
    (∀ p ∈ A, p ≤# n) → IsInternallyCountable A) (by definability)
  · intro A _ hsize
    exact internalSpecialization_antichain_zero_bound hsize
  · intro n hn ih A hA hsize
    by_cases he : (∅ : V) ∈ A
    · exact internalSpecialization_antichain_countable_of_empty_mem hA he
    have hne : ∀ p ∈ A, p ≠ (∅ : V) := by
      intro p hp hpe
      exact he (hpe ▸ hp)
    have hpairs (a : V) : IsInternallyCountable {p ∈ A ; a ∈ p} :=
      internalSpecialization_assignment_fiber_countable ih hA hsize a
    have hnode (x : V) : IsInternallyCountable {p ∈ A ; x ∈ domain p} :=
      internalSpecialization_node_fiber_countable hAC hA.1 hpairs x
    obtain ⟨t, ht, hr⟩ := internalSpecialization_domain_tuples hAC hA.1 hne hsize
    exact internal_countable_of_sparse_cross_comparability hAC (ω_succ_closed hn)
      ht href hbelow hchains
      (fun x _ ↦ internalSpecialization_tuple_occurrences_countable ht hr hnode x)
      (internalSpecialization_tuples_cross_comparable hA href ht hr)

/-- Every internal antichain of the actual finite strict-specialization poset
is internally countable, assuming internal choice and countable tree chains. -/
theorem internalSpecialization_countable_antichains (hAC : InternalChoice V)
    {D S : V} (href : ∀ x ∈ D, ⟨x, x⟩ₖ ∈ S)
    (hbelow : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
      ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S)
    (hchains : ∀ C : V, C ⊆ D →
      (∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) → IsInternallyCountable C)
    (A : V) (hA : IsForcingAntichain (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) A) : IsInternallyCountable A := by
  apply internalSpecialization_countable_of_bounded_slices hAC hA.1
  intro n hn
  apply internalSpecialization_countable_antichain_of_bound hAC href hbelow hchains n hn
  · refine ⟨fun p hp ↦ hA.1 p (mem_sep_iff.mp hp).1, ?_⟩
    intro p hp q hq hpq
    exact hA.2 p (mem_sep_iff.mp hp).1 q (mem_sep_iff.mp hq).1 hpq
  · intro p hp
    exact (mem_sep_iff.mp hp).2

end ZFVP.Schmerl
