import ZFVP.SetTheory.FiniteCardinalArithmetic

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def familyInputs (H : V) : V := ⋃ˢ repl domain (by definability) (range H)

instance familyInputs_definable : ℒₛₑₜ-function₁[V] familyInputs := by
  unfold familyInputs
  definability

theorem mem_familyInputs (H a : V) : a ∈ familyInputs H ↔ ∃ f ∈ range H, a ∈ domain f := by
  simp only [familyInputs, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨D, ⟨f, hf, rfl⟩, ha⟩
    exact ⟨f, hf, ha⟩
  · rintro ⟨f, hf, ha⟩
    exact ⟨domain f, ⟨f, hf, rfl⟩, ha⟩

noncomputable def familyAssignments (H x : V) : V :=
  {a ∈ familyInputs H ; ∃ j ∈ domain H, ⟨a, x⟩ₖ ∈ H ‘ j}

instance familyAssignments_definable : ℒₛₑₜ-function₂[V] familyAssignments := by
  have h : ℒₛₑₜ-relation₃[V] (fun A H x ↦ ∀ a, a ∈ A ↔
      a ∈ familyInputs H ∧ ∃ j ∈ domain H, ⟨a, x⟩ₖ ∈ H ‘ j) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = familyAssignments (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [familyAssignments, mem_sep_iff]

theorem mem_familyAssignments (H x a : V) : a ∈ familyAssignments H x ↔
    a ∈ familyInputs H ∧ ∃ j ∈ domain H, ⟨a, x⟩ₖ ∈ H ‘ j := mem_sep_iff

theorem familyAssignments_of_pair {H j a x : V} [IsFunction H]
    (hj : j ∈ domain H) (ha : ⟨a, x⟩ₖ ∈ H ‘ j) : a ∈ familyAssignments H x := by
  apply (mem_familyAssignments H x a).mpr
  refine ⟨?_, j, hj, ha⟩
  exact (mem_familyInputs H a).mpr
    ⟨H ‘ j, mem_range_of_kpair_mem (kpair_value_mem hj), mem_domain_of_kpair_mem ha⟩

noncomputable def familySupport (H x : V) : V :=
  ⋂ˢ repl range (by definability) (familyAssignments H x)

instance familySupport_definable : ℒₛₑₜ-function₂[V] familySupport := by
  unfold familySupport
  definability

theorem mem_familySupport (H x y : V) : y ∈ familySupport H x ↔
    (∃ a, a ∈ familyAssignments H x) ∧ ∀ a ∈ familyAssignments H x, y ∈ range a := by
  rw [familySupport, mem_sInter_iff]
  constructor
  · rintro ⟨hne, hall⟩
    obtain ⟨K, hK⟩ := isNonempty_def.mp hne
    obtain ⟨a, ha, _⟩ := (repl_spec _).mp hK
    exact ⟨⟨a, ha⟩, fun a ha ↦ hall _ ((repl_spec _).mpr ⟨a, ha, rfl⟩)⟩
  · rintro ⟨⟨a, ha⟩, hall⟩
    refine ⟨isNonempty_def.mpr ⟨range a, (repl_spec _).mpr ⟨a, ha, rfl⟩⟩, ?_⟩
    intro K hK
    obtain ⟨b, hb, rfl⟩ := (repl_spec _).mp hK
    exact hall b hb

/-- If a matching assignment realizes the least range, the intersection is that range. -/
theorem familySupport_eq_range {H x a : V} (ha : a ∈ familyAssignments H x)
    (hmin : ∀ b ∈ familyAssignments H x, range a ⊆ range b) :
    familySupport H x = range a := by
  apply SetTheory.subset_antisymm
  · intro y hy
    exact ((mem_familySupport H x y).mp hy).2 a ha
  · intro y hy
    exact (mem_familySupport H x y).mpr ⟨⟨a, ha⟩, fun b hb ↦ hmin b hb y hy⟩

noncomputable def exactSupportFiber (H j x : V) : V :=
  {a ∈ domain (H ‘ j) ; ⟨a, x⟩ₖ ∈ H ‘ j ∧ range a = familySupport H x}

instance exactSupportFiber_definable : ℒₛₑₜ-function₃[V] exactSupportFiber := by
  have h : ℒₛₑₜ-relation₄[V] (fun A H j x ↦ ∀ a, a ∈ A ↔
      a ∈ domain (H ‘ j) ∧ ⟨a, x⟩ₖ ∈ H ‘ j ∧ range a = familySupport H x) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = exactSupportFiber (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [exactSupportFiber, mem_sep_iff]

theorem mem_exactSupportFiber (H j x a : V) : a ∈ exactSupportFiber H j x ↔
    a ∈ domain (H ‘ j) ∧ ⟨a, x⟩ₖ ∈ H ‘ j ∧ range a = familySupport H x := mem_sep_iff

/-- The internal power set of an internally finite set is internally finite. -/
theorem internallyFinite_powerSet {A : V} (hA : IsInternallyFinite A) :
    IsInternallyFinite (℘ A) := by
  classical
  apply internallyFinite_induction (fun A ↦ IsInternallyFinite (℘ A)) (by definability) ?_ ?_ A hA
  · have he : ℘ (∅ : V) = {∅} := by ext x; simp
    rw [he]
    simpa using internallyFinite_insert (internallyFinite_empty (V := V)) (∅ : V)
  · intro A a ih
    apply internallyFinite_subset
      (internallyFinite_union ih (internallyFinite_repl (fun B ↦ insert a B) (by definability) ih))
    intro X hX
    have hsub := mem_power_iff.mp hX
    by_cases ha : a ∈ X
    · let Y := {y ∈ X ; y ≠ a}
      have hYA : Y ⊆ A := by
        intro y hy
        obtain ⟨hyX, hya⟩ := mem_sep_iff.mp hy
        exact (mem_insert.mp (hsub y hyX)).resolve_left hya
      have hXY : X = insert a Y := by
        apply mem_ext
        intro y
        constructor
        · intro hy
          by_cases hya : y = a
          · exact mem_insert.mpr (Or.inl hya)
          · exact mem_insert.mpr (Or.inr (mem_sep_iff.mpr ⟨hy, hya⟩))
        · intro hy
          rcases mem_insert.mp hy with rfl | hy
          · exact ha
          · exact (mem_sep_iff.mp hy).1
      exact mem_union_iff.mpr (Or.inr ((repl_spec _).mpr ⟨Y, mem_power_iff.mpr hYA, hXY⟩))
    · apply mem_union_iff.mpr ∘ Or.inl ∘ mem_power_iff.mpr
      intro y hy
      rcases mem_insert.mp (hsub y hy) with rfl | hyA
      · exact (ha hy).elim
      · exact hyA

/-- Functions between internally finite sets form an internally finite set. -/
theorem internallyFinite_functionSpace {A B : V}
    (hA : IsInternallyFinite A) (hB : IsInternallyFinite B) : IsInternallyFinite (B ^ A) :=
  internallyFinite_subset (internallyFinite_powerSet (internallyFinite_prod hA hB))
    (fun _f hf ↦ mem_power_iff.mpr (mem_function_iff.mp hf).1)

/-- Fixing the domain and the exact finite range leaves only internally finitely many assignments. -/
theorem exactSupportFiber_finite {H j x B : V} (hB : IsInternallyFinite B)
    (hs : IsInternallyFinite (familySupport H x))
    (hfun : ∀ a ∈ domain (H ‘ j), IsFunction a ∧ domain a = B) :
    IsInternallyFinite (exactSupportFiber H j x) := by
  apply internallyFinite_subset (internallyFinite_functionSpace hB hs)
  intro a ha
  obtain ⟨haD, _, hra⟩ := (mem_exactSupportFiber H j x a).mp ha
  obtain ⟨hfa, hda⟩ := hfun a haD
  have : IsFunction a := hfa
  simpa only [hra, hda] using IsFunction.mem_function a

theorem exactSupportFiber_finite_of_functions {H j x B K : V} (hB : IsInternallyFinite B)
    (hs : IsInternallyFinite (familySupport H x))
    (hfun : ∀ a ∈ domain (H ‘ j), a ∈ K ^ B) :
    IsInternallyFinite (exactSupportFiber H j x) :=
  exactSupportFiber_finite hB hs (fun a ha ↦
    ⟨IsFunction.of_mem (hfun a ha), domain_eq_of_mem_function (hfun a ha)⟩)

end ZFVP


