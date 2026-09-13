import ZFVP.SetTheory.HartogsBound

/-! Hartogs' number is the least ordinal that does not inject into a given set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsHartogsNumber (A α : V) : Prop := IsLeastOrdinal (fun β ↦ ¬β ≤# A) α

instance isHartogsNumber_definable : ℒₛₑₜ-relation[V] IsHartogsNumber := by
  unfold IsHartogsNumber IsLeastOrdinal
  definability

theorem hartogs_existsUnique (A : V) : ∃! α, IsHartogsNumber A α :=
  leastOrdinal_existsUnique _ (by definability) (exists_ordinal_not_cardLE A)

noncomputable def hartogsNumber (A : V) : V := Classical.choose! (hartogs_existsUnique A)

theorem hartogsNumber_spec (A : V) : IsHartogsNumber A (hartogsNumber A) :=
  Classical.choose!_spec (hartogs_existsUnique A)

instance hartogsNumber_ordinal (A : V) : IsOrdinal (hartogsNumber A) := (hartogsNumber_spec A).1

theorem not_hartogsNumber_cardLE (A : V) : ¬hartogsNumber A ≤# A := (hartogsNumber_spec A).2.1

theorem hartogsNumber_minimal {A α : V} [IsOrdinal α] (hα : ¬α ≤# A) : hartogsNumber A ⊆ α :=
  (hartogsNumber_spec A).2.2 α inferInstance hα

theorem hartogsNumber_eq_iff (A α : V) : hartogsNumber A = α ↔ IsHartogsNumber A α := by
  constructor
  · rintro rfl
    exact hartogsNumber_spec A
  · intro hα
    exact (hartogs_existsUnique A).unique (hartogsNumber_spec A) hα

instance hartogsNumber_definable : ℒₛₑₜ-function₁[V] hartogsNumber := by
  have h : ℒₛₑₜ-relation (fun α A : V ↦ IsHartogsNumber A α) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (hartogsNumber_eq_iff (v 1) (v 0))

theorem cardLE_of_mem_hartogsNumber {A α : V} (hα : α ∈ hartogsNumber A) : α ≤# A := by
  have : IsOrdinal α := IsOrdinal.of_mem hα
  by_contra h
  exact mem_irrefl α (hartogsNumber_minimal h α hα)

theorem ordinal_cardLE_iff_mem_hartogsNumber {A α : V} [IsOrdinal α] :
    α ≤# A ↔ α ∈ hartogsNumber A := by
  constructor
  · intro h
    rcases IsOrdinal.mem_trichotomy α (hartogsNumber A) with hlt | heq | hgt
    · exact hlt
    · exact False.elim (not_hartogsNumber_cardLE A (heq ▸ h))
    · have hsub : hartogsNumber A ⊆ α := IsOrdinal.toIsTransitive.transitive _ hgt
      exact False.elim (not_hartogsNumber_cardLE A ((cardLE_of_subset hsub).trans h))
  · exact cardLE_of_mem_hartogsNumber

theorem hartogsNumber_mono {A B : V} (h : A ≤# B) : hartogsNumber A ⊆ hartogsNumber B :=
  hartogsNumber_minimal (fun hbad ↦ not_hartogsNumber_cardLE B (hbad.trans h))

theorem hartogsNumber_ne_zero (A : V) : hartogsNumber A ≠ (0 : V) := by
  intro h
  apply not_hartogsNumber_cardLE A
  rw [h]
  exact cardLE_empty A

def IsInitialOrdinal (κ : V) : Prop := IsOrdinal κ ∧ ∀ α ∈ κ, ¬κ ≤# α

instance isInitialOrdinal_definable : ℒₛₑₜ-predicate[V] IsInitialOrdinal := by
  unfold IsInitialOrdinal
  definability

theorem hartogsNumber_initial (A : V) : IsInitialOrdinal (hartogsNumber A) := by
  refine ⟨inferInstance, ?_⟩
  intro α hα hbad
  exact not_hartogsNumber_cardLE A (hbad.trans (cardLE_of_mem_hartogsNumber hα))

theorem orderType_cardLE {R D : V} (hR : IsInternalWellOrder R D) : internalOrderType R D ≤# D := by
  have hc := mostowskiMap_isTransitiveCollapse hR.2.1 (internalWellOrder_extensional hR)
  have hf : IsFunction (mostowskiMap R D) := IsFunction.of_mem hc.2.1
  have hinj : Injective (mostowskiMap R D) := by
    intro x y z hx hy
    have hxD : x ∈ D := domain_eq_of_mem_function hc.2.1 ▸ mem_domain_of_kpair_mem hx
    have hyD : y ∈ D := domain_eq_of_mem_function hc.2.1 ▸ mem_domain_of_kpair_mem hy
    exact hc.2.2.2.1 x hxD y hyD ((value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm)
  exact ⟨converseGraph (mostowskiMap R D), converseGraph_mem_function hc.2.1 hinj,
    converseGraph_injective _⟩

theorem orderTypesOfSubsets_eq_hartogsNumber (A : V) : orderTypesOfSubsets A = hartogsNumber A := by
  apply mem_ext
  intro α
  constructor
  · intro hα
    obtain ⟨D, R, hD, hR, rfl⟩ := (mem_orderTypesOfSubsets A α).mp hα
    have : IsOrdinal (internalOrderType R D) := internalOrderType_ordinal hR
    exact ordinal_cardLE_iff_mem_hartogsNumber.mp ((orderType_cardLE hR).trans (cardLE_of_subset hD))
  · intro hα
    have : IsOrdinal α := IsOrdinal.of_mem hα
    exact ordinal_cardLE_mem_orderTypes (cardLE_of_mem_hartogsNumber hα)

end ZFVP
