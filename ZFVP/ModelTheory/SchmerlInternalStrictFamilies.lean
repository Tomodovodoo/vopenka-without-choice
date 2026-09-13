import ZFVP.ModelTheory.SchmerlInternalStrictConditions
import ZFVP.ModelTheory.SchmerlInternalBMR
import ZFVP.SetTheory.InjectionRetraction
import ZFVP.SetTheory.MaximalAntichains

/-! Internal antichain fibers and uniformly bounded domain enumerations.
These are the induction steps preceding the sparse-tuple argument. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalSpecialization_antichain_zero_bound {A : V}
    (hsize : ∀ p ∈ A, p ≤# (∅ : V)) : IsInternallyCountable A := by
  apply internallyCountable_subset (internallyCountable_singleton (∅ : V))
  intro p hp
  apply mem_singleton_iff.mpr
  obtain ⟨f, hf, _⟩ := hsize p hp
  apply mem_ext
  intro z
  simp only [not_mem_empty, iff_false]
  exact fun hz ↦ not_mem_empty (function_value_mem hf hz)

theorem internalSpecialization_antichain_countable_of_empty_mem {D S A : V}
    (hA : IsForcingAntichain (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) A) (he : (∅ : V) ∈ A) :
    IsInternallyCountable A := by
  apply internallyCountable_subset (internallyCountable_singleton (∅ : V))
  intro p hp
  apply mem_singleton_iff.mpr
  by_contra hpe
  apply hA.2 p hp ∅ he hpe
  have hpP := hA.1 p hp
  have heP := empty_mem_internalSpecialization D S
  exact ⟨p, hpP,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hpP, hpP, subset_refl _⟩,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hpP, heP, by simp⟩⟩

/-- The induction hypothesis applies to the image obtained by erasing one
assignment shared by every member of the fiber. -/
theorem internalSpecialization_assignment_fiber_countable {D S A n : V}
    (ih : ∀ B : V, IsForcingAntichain (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) B →
      (∀ p ∈ B, p ≤# n) → IsInternallyCountable B)
    (hA : IsForcingAntichain (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) A)
    (hsize : ∀ p ∈ A, p ≤# succ n) (a : V) :
    IsInternallyCountable {p ∈ A ; a ∈ p} := by
  let B : V := {p ∈ A ; a ∈ p}
  let F : V → V := fun p ↦ p \ {a}
  have hF : ℒₛₑₜ-function₁ F := by dsimp [F]; definability
  have hanti : IsForcingAntichain (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) (repl F hF B) := by
    constructor
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := (repl_spec hF).mp hq
      exact internalSpecialization_erase (hA.1 p (mem_sep_iff.mp hp).1)
    · intro r hr t ht hne hcomp
      obtain ⟨p, hp, rfl⟩ := (repl_spec hF).mp hr
      obtain ⟨q, hq, rfl⟩ := (repl_spec hF).mp ht
      obtain ⟨hpA, hap⟩ := mem_sep_iff.mp hp
      obtain ⟨hqA, haq⟩ := mem_sep_iff.mp hq
      exact hA.2 p hpA q hqA (fun heq ↦ hne (congrArg F heq))
        (internalSpecialization_compatible_of_erase (hA.1 p hpA) (hA.1 q hqA) hap haq hcomp)
  have hnewsize : ∀ p ∈ repl F hF B, p ≤# n := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := (repl_spec hF).mp hq
    exact internal_erase_cardLE (hsize p (mem_sep_iff.mp hp).1) (mem_sep_iff.mp hp).2
  apply internallyCountable_of_cardLE (ih _ hanti hnewsize)
  apply cardLE_of_injective_map F hF
  · intro p hp
    exact (repl_spec hF).mpr ⟨p, hp, rfl⟩
  · intro p hp q hq heq
    exact internal_erase_injective (mem_sep_iff.mp hp).2 (mem_sep_iff.mp hq).2 heq

theorem internalSpecialization_node_fiber_countable (hAC : InternalChoice V)
    {D S A : V}
    (hA : A ⊆ internalSpecialization D S)
    (hpairs : ∀ a : V, IsInternallyCountable {p ∈ A ; a ∈ p}) (x : V) :
    IsInternallyCountable {p ∈ A ; x ∈ domain p} := by
  let F : V → V := fun c ↦ {p ∈ A ; ⟨x, c⟩ₖ ∈ p}
  have hF : ℒₛₑₜ-function₁ F := internal_fiber_definable A _ (by definability)
  apply internallyCountable_subset (internal_countable_union hAC internallyCountable_omega
    F hF (fun c _ ↦ hpairs ⟨x, c⟩ₖ))
  intro p hp
  obtain ⟨hpA, hxp⟩ := mem_sep_iff.mp hp
  obtain ⟨c, hxc⟩ := mem_domain_iff.mp hxp
  have hc : c ∈ (ω : V) := finitePartialFunction_range
    ((mem_internalSpecialization _ _ _).mp (hA p hpA)).1 c (mem_range_of_kpair_mem hxc)
  exact mem_sUnion_iff.mpr ⟨F c, (repl_spec hF).mpr ⟨c, hc, rfl⟩,
    mem_sep_iff.mpr ⟨hpA, hxc⟩⟩

theorem internal_domain_cardLE_graph (p : V) [IsFunction p] : domain p ≤# p := by
  apply cardLE_of_injective_map (fun x ↦ ⟨x, p ‘ x⟩ₖ) (by definability)
  · intro x hx
    exact kpair_value_mem hx
  · intro x _ y _ heq
    exact (kpair_iff.mp heq).1

/-- Internal choice selects, for every nonempty condition, an internal tuple
of one fixed length whose range is exactly its domain. Repetition is allowed. -/
theorem internalSpecialization_domain_tuples (hAC : InternalChoice V) {D S A n : V}
    (hA : A ⊆ internalSpecialization D S)
    (hne : ∀ p ∈ A, p ≠ (∅ : V)) (hsize : ∀ p ∈ A, p ≤# n) :
    ∃ t ∈ (D ^ n) ^ A, ∀ p ∈ A, range (t ‘ p) = domain p := by
  let F : V → V := fun p ↦ {e ∈ D ^ n ; range e = domain p}
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation[V] (fun E p ↦ ∀ e,
      e ∈ E ↔ e ∈ D ^ n ∧ range e = domain p) := by definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [F, mem_sep_iff]
    rfl
  have hneF : ∀ p ∈ A, IsNonempty (F p) := by
    intro p hp
    have hpfin := ((mem_internalSpecialization _ _ _).mp (hA p hp)).1
    have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hpfin).2.1
    have hpne : IsNonempty p :=
      not_isEmpty_iff_isNonempty.mp (fun he ↦ hne p hp (isEmpty_iff_eq_empty.mp he))
    obtain ⟨a, ha⟩ := hpne.nonempty
    obtain ⟨x, c, rfl⟩ := IsFunction.mem_eq_kpair ha
    have hdne : IsNonempty (domain p) := ⟨x, mem_domain_of_kpair_mem ha⟩
    obtain ⟨e, he, hr⟩ := surjection_of_injection
      ((internal_domain_cardLE_graph p).trans (hsize p hp)) hdne
    have heD : e ∈ D ^ n := mem_function_of_mem_function_of_subset he
      (finitePartialFunction_domain hpfin)
    exact ⟨e, mem_sep_iff.mpr ⟨heD, hr⟩⟩
  obtain ⟨t, ht, htd, htsel⟩ := choice_for_definable_family hAC A F hF hneF
  have : IsFunction t := ht
  have hr : range t ⊆ D ^ n := by
    intro e he
    obtain ⟨p, hpe⟩ := mem_range_iff.mp he
    have hp : p ∈ A := htd ▸ mem_domain_of_kpair_mem hpe
    have hv := (mem_sep_iff.mp (htsel p hp)).1
    rwa [value_eq_of_kpair_mem hpe] at hv
  refine ⟨t, ?_, fun p hp ↦ (mem_sep_iff.mp (htsel p hp)).2⟩
  simpa only [htd] using mem_function_of_mem_function_of_subset (IsFunction.mem_function t) hr

theorem internalSpecialization_tuple_occurrences_countable {D A n t : V}
    (ht : t ∈ (D ^ n) ^ A) (hr : ∀ p ∈ A, range (t ‘ p) = domain p)
    (hnode : ∀ x, IsInternallyCountable {p ∈ A ; x ∈ domain p}) (x : V) :
    IsInternallyCountable {p ∈ A ; ∃ i ∈ n, (t ‘ p) ‘ i = x} := by
  apply internallyCountable_subset (hnode x)
  intro p hp
  obtain ⟨hpA, i, hi, hix⟩ := mem_sep_iff.mp hp
  exact mem_sep_iff.mpr ⟨hpA, hr p hpA ▸ hix ▸ value_mem_range (function_value_mem ht hpA) hi⟩

theorem internalSpecialization_tuples_cross_comparable {D S A n t : V}
    (hA : IsForcingAntichain (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) A)
    (href : ∀ x ∈ D, ⟨x, x⟩ₖ ∈ S)
    (ht : t ∈ (D ^ n) ^ A) (hr : ∀ p ∈ A, range (t ‘ p) = domain p) :
    ∀ p ∈ A, ∀ q ∈ A, p ≠ q → ∃ i ∈ n, ∃ j ∈ n,
      ⟨(t ‘ p) ‘ i, (t ‘ q) ‘ j⟩ₖ ∈ S ∨ ⟨(t ‘ q) ‘ j, (t ‘ p) ‘ i⟩ₖ ∈ S := by
  intro p hp q hq hpq
  obtain ⟨a, ha, b, hb, hab⟩ := internalSpecialization_exists_comparable_of_not_compatible
    (hA.1 p hp) (hA.1 q hq) href (hA.2 p hp q hq hpq)
  have hdom (p : V) (hp : p ∈ A) (a : V) (ha : a ∈ p) : kpair.π₁ a ∈ domain p := by
    have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp
      ((mem_internalSpecialization _ _ _).mp (hA.1 p hp)).1).2.1
    obtain ⟨x, c, rfl⟩ := IsFunction.mem_eq_kpair ha
    simpa only [kpair.π₁_kpair] using mem_domain_of_kpair_mem ha
  obtain ⟨i, hi⟩ := mem_range_iff.mp ((hr p hp).symm ▸ hdom p hp a ha)
  obtain ⟨j, hj⟩ := mem_range_iff.mp ((hr q hq).symm ▸ hdom q hq b hb)
  have hip : i ∈ n := (mem_of_mem_functions (function_value_mem ht hp) hi).1
  have hjq : j ∈ n := (mem_of_mem_functions (function_value_mem ht hq) hj).1
  have : IsFunction (t ‘ p) := IsFunction.of_mem (function_value_mem ht hp)
  have : IsFunction (t ‘ q) := IsFunction.of_mem (function_value_mem ht hq)
  exact ⟨i, hip, j, hjq, by simpa only [value_eq_of_kpair_mem hi, value_eq_of_kpair_mem hj] using hab⟩

/-- The model's own omega covers every condition by an internal finite
cardinality bound, including conditions of nonstandard finite size. -/
theorem internalSpecialization_countable_of_bounded_slices (hAC : InternalChoice V)
    {D S A : V} (hA : A ⊆ internalSpecialization D S)
    (hslices : ∀ n ∈ (ω : V), IsInternallyCountable {p ∈ A ; p ≤# n}) :
    IsInternallyCountable A := by
  let F : V → V := fun n ↦ {p ∈ A ; p ≤# n}
  have hF : ℒₛₑₜ-function₁ F := internal_fiber_definable A _ (by definability)
  apply internallyCountable_subset (internal_countable_union hAC internallyCountable_omega
    F hF hslices)
  intro p hp
  have hpfin := (mem_finitePartialFunctions _ _ _).mp
    ((mem_internalSpecialization _ _ _).mp (hA p hp)).1
  have : IsFunction p := hpfin.2.1
  obtain ⟨n, hn, hpn, _⟩ := internallyFinite_function hpfin.2.2
  exact mem_sUnion_iff.mpr ⟨F n, (repl_spec hF).mpr ⟨n, hn, rfl⟩,
    mem_sep_iff.mpr ⟨hp, hpn⟩⟩

end ZFVP.Schmerl
