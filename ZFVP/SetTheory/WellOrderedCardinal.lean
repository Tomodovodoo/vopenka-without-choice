import ZFVP.SetTheory.Hartogs

/-! Cardinal representatives for well-orderable internal sets, with no use of AC. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWellOrderable (A : V) : Prop := ∃ R, IsInternalWellOrder R A

instance isWellOrderable_definable : ℒₛₑₜ-predicate[V] IsWellOrderable := by
  unfold IsWellOrderable
  definability

theorem internalOrderType_cardEQ {R D : V} (hR : IsInternalWellOrder R D) : internalOrderType R D ≋ D := by
  refine ⟨orderType_cardLE hR, ?_⟩
  have hc := mostowskiMap_isTransitiveCollapse hR.2.1 (internalWellOrder_extensional hR)
  have : IsFunction (mostowskiMap R D) := IsFunction.of_mem hc.2.1
  refine ⟨mostowskiMap R D, hc.2.1, ?_⟩
  intro x y z hx hy
  have hxD : x ∈ D := domain_eq_of_mem_function hc.2.1 ▸ mem_domain_of_kpair_mem hx
  have hyD : y ∈ D := domain_eq_of_mem_function hc.2.1 ▸ mem_domain_of_kpair_mem hy
  exact hc.2.2.2.1 x hxD y hyD ((value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm)

theorem wellOrderable_iff_cardLE_ordinal (A : V) :
    IsWellOrderable A ↔ ∃ α : V, IsOrdinal α ∧ A ≤# α := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨internalOrderType R A, internalOrderType_ordinal hR, (internalOrderType_cardEQ hR).2⟩
  · rintro ⟨α, hα, f, hf, hinj⟩
    have : IsOrdinal α := hα
    exact ⟨pulledMembership A f, pulledMembership_wellOrder hf hinj⟩

theorem wellOrderable_of_cardLE {A B : V} (hA : A ≤# B) (hB : IsWellOrderable B) : IsWellOrderable A := by
  obtain ⟨α, hα, hBα⟩ := (wellOrderable_iff_cardLE_ordinal B).mp hB
  exact (wellOrderable_iff_cardLE_ordinal A).mpr ⟨α, hα, hA.trans hBα⟩

theorem ordinal_wellOrderable (α : V) [IsOrdinal α] : IsWellOrderable α :=
  ⟨membershipRelation α, ordinal_membership_wellOrder α⟩

def IsCardinalOf (A κ : V) : Prop := IsLeastOrdinal (fun α ↦ α ≋ A) κ

instance isCardinalOf_definable : ℒₛₑₜ-relation[V] IsCardinalOf := by
  unfold IsCardinalOf IsLeastOrdinal
  definability

theorem cardinalOf_existsUnique {A : V} (hA : IsWellOrderable A) : ∃! κ, IsCardinalOf A κ := by
  obtain ⟨R, hR⟩ := hA
  exact leastOrdinal_existsUnique _ (by definability)
    ⟨internalOrderType R A, internalOrderType_ordinal hR, internalOrderType_cardEQ hR⟩

theorem IsCardinalOf.wellOrderable {A κ : V} (h : IsCardinalOf A κ) : IsWellOrderable A :=
  (wellOrderable_iff_cardLE_ordinal A).mpr ⟨κ, h.1, h.2.1.2⟩

theorem IsCardinalOf.initial {A κ : V} (h : IsCardinalOf A κ) : IsInitialOrdinal κ := by
  have : IsOrdinal κ := h.1
  refine ⟨h.1, ?_⟩
  intro α hα hbad
  have : IsOrdinal α := IsOrdinal.of_mem hα
  have hακ : α ≤# κ := cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hα)
  have hαA : α ≋ A := (show α ≋ κ from ⟨hακ, hbad⟩).trans h.2.1
  exact mem_irrefl α (h.2.2 α inferInstance hαA α hα)

noncomputable def wellOrderedCardinal (A : V) : V := by
  classical
  exact if hA : IsWellOrderable A then Classical.choose! (cardinalOf_existsUnique hA) else ∅

theorem wellOrderedCardinal_spec {A : V} (hA : IsWellOrderable A) :
    IsCardinalOf A (wellOrderedCardinal A) := by
  simpa [wellOrderedCardinal, hA] using Classical.choose!_spec (cardinalOf_existsUnique hA)

theorem wellOrderedCardinal_eq_iff (A κ : V) : wellOrderedCardinal A = κ ↔
    IsCardinalOf A κ ∨ (¬IsWellOrderable A ∧ κ = ∅) := by
  by_cases hA : IsWellOrderable A
  · simp only [hA, not_true_eq_false, false_and, or_false]
    constructor
    · rintro rfl
      exact wellOrderedCardinal_spec hA
    · intro hκ
      exact (cardinalOf_existsUnique hA).unique (wellOrderedCardinal_spec hA) hκ
  · have hn : ¬IsCardinalOf A κ := fun h ↦ hA h.wellOrderable
    simp [wellOrderedCardinal, hA, hn, eq_comm]

instance wellOrderedCardinal_definable : ℒₛₑₜ-function₁[V] wellOrderedCardinal := by
  have h : ℒₛₑₜ-relation (fun κ A : V ↦ IsCardinalOf A κ ∨ (¬IsWellOrderable A ∧ κ = ∅)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (wellOrderedCardinal_eq_iff (v 1) (v 0))

theorem wellOrderedCardinal_initial {A : V} (hA : IsWellOrderable A) : IsInitialOrdinal (wellOrderedCardinal A) :=
  (wellOrderedCardinal_spec hA).initial

theorem wellOrderedCardinal_cardEQ {A : V} (hA : IsWellOrderable A) : wellOrderedCardinal A ≋ A :=
  (wellOrderedCardinal_spec hA).2.1

theorem wellOrderedCardinal_lt_hartogs {A : V} (hA : IsWellOrderable A) :
    wellOrderedCardinal A ∈ hartogsNumber A := by
  have : IsOrdinal (wellOrderedCardinal A) := (wellOrderedCardinal_spec hA).1
  exact ordinal_cardLE_iff_mem_hartogsNumber.mp (wellOrderedCardinal_cardEQ hA).1

theorem initialOrdinal_cardLE_iff {κ μ : V} (hκ : IsInitialOrdinal κ) [IsOrdinal μ] :
    κ ≤# μ ↔ κ ⊆ μ := by
  have : IsOrdinal κ := hκ.1
  constructor
  · intro h
    rcases IsOrdinal.mem_trichotomy κ μ with hlt | heq | hgt
    · exact IsOrdinal.toIsTransitive.transitive _ hlt
    · exact heq ▸ subset_refl κ
    · exact False.elim (hκ.2 μ hgt h)
  · exact cardLE_of_subset

theorem wellOrderedCardinal_mono {A B : V} (hA : IsWellOrderable A) (hB : IsWellOrderable B)
    (h : A ≤# B) : wellOrderedCardinal A ⊆ wellOrderedCardinal B := by
  have : IsOrdinal (wellOrderedCardinal B) := (wellOrderedCardinal_spec hB).1
  exact (initialOrdinal_cardLE_iff (wellOrderedCardinal_initial hA)).mp
    ((wellOrderedCardinal_cardEQ hA).1.trans (h.trans (wellOrderedCardinal_cardEQ hB).2))

theorem initialOrdinal_isCardinalOf_self {κ : V} (hκ : IsInitialOrdinal κ) : IsCardinalOf κ κ := by
  refine ⟨hκ.1, CardEQ.refl κ, ?_⟩
  intro α hα heq
  have : IsOrdinal α := hα
  exact (initialOrdinal_cardLE_iff hκ).mp heq.2

theorem wellOrderedCardinal_of_initial {κ : V} (hκ : IsInitialOrdinal κ) : wellOrderedCardinal κ = κ :=
  (wellOrderedCardinal_eq_iff κ κ).mpr (Or.inl (initialOrdinal_isCardinalOf_self hκ))

theorem cardEQ_iff_wellOrderedCardinal_eq {A B : V} (hA : IsWellOrderable A) (hB : IsWellOrderable B) :
    A ≋ B ↔ wellOrderedCardinal A = wellOrderedCardinal B := by
  constructor
  · intro h
    exact SetTheory.subset_antisymm (wellOrderedCardinal_mono hA hB h.1) (wellOrderedCardinal_mono hB hA h.2)
  · intro h
    exact (wellOrderedCardinal_cardEQ hA).symm.trans (h.symm ▸ wellOrderedCardinal_cardEQ hB)

theorem wellOrderable_iff_cardLE_hartogsNumber (A : V) : IsWellOrderable A ↔ A ≤# hartogsNumber A := by
  constructor
  · intro hA
    have hlt := wellOrderedCardinal_lt_hartogs hA
    exact (wellOrderedCardinal_cardEQ hA).2.trans (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hlt))
  · intro h
    exact (wellOrderable_iff_cardLE_ordinal A).mpr ⟨hartogsNumber A, inferInstance, h⟩

theorem wellOrderable_iff_cardLT_hartogsNumber (A : V) : IsWellOrderable A ↔ A <# hartogsNumber A := by
  rw [CardLT, ← wellOrderable_iff_cardLE_hartogsNumber]
  exact ⟨fun h ↦ ⟨h, not_hartogsNumber_cardLE A⟩, fun h ↦ h.1⟩

end ZFVP
