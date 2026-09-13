import ZFVP.ModelTheory.SchmerlFunctionCandidates

/-! Extracting the finite-domain index order from the predicates used in the
uniform infinitary sentence. All order and cofinality facts are consequences of
the displayed semantic clauses. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory Set Order

universe u

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The literal requirements on the selected finite domains for one set. -/
structure SelectedDomainClauses (s : V) (D : V → Prop) : Prop where
  finite : ∀ d, D d → IsInternallyFinite d ∧ d ⊆ s
  linear : ∀ d e, D d → D e → d ⊆ e ∨ e ⊆ d
  cofinal : ∀ a, IsInternallyFinite a → a ⊆ s → ∃ d, D d ∧ a ⊆ d
  uncountable : ¬ ({d | D d} : Set V).Countable
  initial : ∀ d, D d → ({e | D e ∧ e ⊆ d} : Set V).Countable

/-- The cofinal omega-one chain supplied by the Rubin construction satisfies
the exact selected-domain requirements of the infinitary sentence. -/
theorem selectedDomainClauses_of_omegaOne_chain {s : V}
    (C : FiniteDomainChain s (Ordinal.ToType (Ordinal.omega.{u} 1))) :
    SelectedDomainClauses s (fun d ↦ d ∈ Set.range C.domain) := by
  let Ω := Ordinal.ToType (Ordinal.omega.{u} 1)
  have hI : Cardinal.aleph0 < Order.cof Ω := by
    rw [Ordinal.cof_toType, Cardinal.cof_omega_one]
    exact Cardinal.aleph0_lt_aleph_one
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro d ⟨i, rfl⟩
    exact ⟨C.finite i, C.subset i⟩
  · rintro d e ⟨i, rfl⟩ ⟨j, rfl⟩
    exact (le_total i j).imp (fun hij ↦ C.monotone hij) (fun hji ↦ C.monotone hji)
  · intro a ha hsub
    obtain ⟨i, hi⟩ := C.cofinal a hsub ha
    exact ⟨C.domain i, Set.mem_range_self i, hi⟩
  · intro hcount
    change (Set.range C.domain).Countable at hcount
    have hu : (Set.univ : Set Ω).Countable :=
      Set.countable_of_injective_of_countable_image C.injective.injOn
        (by simpa only [Set.image_univ] using hcount)
    have hcard := Cardinal.mk_le_aleph0_iff.mpr (Set.countable_univ_iff.mp hu)
    rw [Cardinal.mk_toType, Ordinal.card_omega] at hcard
    exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hcard
  · rintro d ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := exists_bound_of_countable hI (Set.countable_singleton i)
    apply ((omegaOne_initial_countable j).image C.domain).mono
    rintro e ⟨⟨k, rfl⟩, hki⟩
    exact ⟨k, ((C.domain_subset_iff k i).mp hki).trans_lt
      (hj i (Set.mem_singleton i)), rfl⟩

/-- Inclusion is a linear order on the selected domains. -/
@[instance_reducible] noncomputable def SelectedDomainClauses.order {s : V} {D : V → Prop}
    (h : SelectedDomainClauses s D) : LinearOrder {d // D d} where
  le a b := a.val ⊆ b.val
  le_refl _ := SetTheory.subset_refl _
  le_trans _ _ _ := SetTheory.subset_trans
  le_antisymm _ _ hab hba := Subtype.ext (SetTheory.subset_antisymm hab hba)
  le_total a b := h.linear a.val b.val a.property b.property
  toDecidableLE := Classical.decRel _

/-- No choice of an omega-one enumeration is needed in the reduct theorem. -/
noncomputable def SelectedDomainClauses.chain {s : V} {D : V → Prop}
    (h : SelectedDomainClauses s D) :
    let : LinearOrder {d // D d} := h.order
    FiniteDomainChain s {d // D d} := by
  let : LinearOrder {d // D d} := h.order
  exact {
    domain := Subtype.val
    finite := fun i ↦ (h.finite i.val i.property).1
    subset := fun i ↦ (h.finite i.val i.property).2
    monotone := fun {_ _} hij ↦ hij
    injective := Subtype.val_injective
    cofinal := fun a ha hfin ↦ by
      obtain ⟨d, hd, had⟩ := h.cofinal a hfin ha
      exact ⟨⟨d, hd⟩, had⟩ }

theorem SelectedDomainClauses.chain_range {s : V} {D : V → Prop}
    (h : SelectedDomainClauses s D) :
    let : LinearOrder {d // D d} := h.order
    Set.range h.chain.domain = {d | D d} := by
  dsimp only
  ext d
  exact ⟨fun ⟨i, he⟩ ↦ he ▸ i.property, fun hd ↦ ⟨⟨d, hd⟩, rfl⟩⟩

theorem SelectedDomainClauses.uncountable_cofinality {s : V} {D : V → Prop}
    (h : SelectedDomainClauses s D) :
    let : LinearOrder {d // D d} := h.order
    Cardinal.aleph0 < Order.cof {d // D d} := by
  let : LinearOrder {d // D d} := h.order
  let : Uncountable {d // D d} :=
    not_countable_iff.mp (fun hc ↦ h.uncountable (Set.countable_coe_iff.mp hc))
  apply uncountable_cof_of_countable_initials
  intro d
  have hc := (h.initial d.val d.property).preimage
    (Subtype.val_injective : Function.Injective (Subtype.val : {d // D d} → V))
  change ({e : {d // D d} | D e.val ∧ e.val ⊆ d.val}).Countable at hc
  change ({e : {d // D d} | e.val ⊆ d.val}).Countable
  apply hc.mono
  intro e he
  exact ⟨e.property, he⟩

/-- For a selected-domain family, a countable weak coloring and the explicit
one-node code clause imply internal codes for every full branch filter. -/
theorem SelectedDomainClauses.filters_coded {s : V} {D : V → Prop}
    (h : SelectedDomainClauses s D) (f : V → V)
    (hcount : (Set.range f).Countable)
    (hweak : ∀ x y z : V,
      x ∈ finitePartialFunctions s ((2 : ℕ) : V) → D (domain x) →
      y ∈ finitePartialFunctions s ((2 : ℕ) : V) → D (domain y) →
      z ∈ finitePartialFunctions s ((2 : ℕ) : V) → D (domain z) →
      x ⊆ y → x ⊆ z → f x = f y → f x = f z → y ⊆ z ∨ z ⊆ y)
    (hcodes : ∀ b : V, b ∈ finitePartialFunctions s ((2 : ℕ) : V) → D (domain b) →
      (∀ d : V, D d → ∃ p : V, functionFilterCandidate s D
        (fun x y ↦ f x = f y) b p ∧ d ⊆ domain p) →
      ∃ m : V, ∀ p : V, p ∈ m ↔ functionFilterCandidate s D
        (fun x y ↦ f x = f y) b p) :
    let : LinearOrder {d // D d} := h.order
    ∀ B : Set (FunctionTreeNode h.chain),
      (FunctionTreeNode.rankedTree (C := h.chain)).IsBranch B →
      ∃ m : V, ∀ p : V, p ∈ m ↔ filterOfBranch h.chain B p := by
  classical
  let : LinearOrder {d // D d} := h.order
  let : Uncountable {d // D d} :=
    not_countable_iff.mp (fun hc ↦ h.uncountable (Set.countable_coe_iff.mp hc))
  have hrange (d : V) : d ∈ Set.range h.chain.domain ↔ D d := by
    rw [h.chain_range]
    rfl
  have hw : WeaklySpecializes (· ≤ ·) (fun x : FunctionTreeNode h.chain ↦ f x.graph) := by
    intro x y z hxy hxz hfxy hfxz
    have hd (a : FunctionTreeNode h.chain) : D (domain a.graph) := by
      rw [FunctionTreeNode.domain_graph]
      exact a.level.property
    have he := hweak x.graph y.graph z.graph
      x.graph_mem_finitePartialFunctions (hd x)
      y.graph_mem_finitePartialFunctions (hd y)
      z.graph_mem_finitePartialFunctions (hd z) hxy.2 hxz.2 hfxy hfxz
    exact he.imp (FunctionTreeNode.le_iff_graph_subset _ _).mpr
      (FunctionTreeNode.le_iff_graph_subset _ _).mpr
  apply (forall_filter_codes_iff_firstOrder_candidates h.chain f
    h.uncountable_cofinality hw (hcount.mono (Set.range_comp_subset_range _ _))).mpr
  intro b hb
  have hd : D (domain b.graph) := by
    rw [FunctionTreeNode.domain_graph]
    exact b.level.property
  have heD : (fun d ↦ d ∈ Set.range h.chain.domain) = D := funext fun d ↦ propext (hrange d)
  rw [heD] at hb ⊢
  simp only [hrange] at hb
  exact hcodes b.graph b.graph_mem_finitePartialFunctions hd hb

/-- Preserved codes for all branches give the first-order candidate code clause
used when building a model of the sentence. -/
theorem SelectedDomainClauses.candidates_coded {s : V} {D : V → Prop}
    (h : SelectedDomainClauses s D) (f : V → V)
    (hcount : (Set.range f).Countable)
    (hweak : ∀ x y z : V,
      x ∈ finitePartialFunctions s ((2 : ℕ) : V) → D (domain x) →
      y ∈ finitePartialFunctions s ((2 : ℕ) : V) → D (domain y) →
      z ∈ finitePartialFunctions s ((2 : ℕ) : V) → D (domain z) →
      x ⊆ y → x ⊆ z → f x = f y → f x = f z → y ⊆ z ∨ z ⊆ y)
    (hfilters : let : LinearOrder {d // D d} := h.order
      ∀ B : Set (FunctionTreeNode h.chain),
        (FunctionTreeNode.rankedTree (C := h.chain)).IsBranch B →
        ∃ m : V, ∀ p : V, p ∈ m ↔ filterOfBranch h.chain B p) :
    ∀ b : V, b ∈ finitePartialFunctions s ((2 : ℕ) : V) → D (domain b) →
      (∀ d : V, D d → ∃ p : V, functionFilterCandidate s D
        (fun x y ↦ f x = f y) b p ∧ d ⊆ domain p) →
      ∃ m : V, ∀ p : V, p ∈ m ↔ functionFilterCandidate s D
        (fun x y ↦ f x = f y) b p := by
  classical
  let : LinearOrder {d // D d} := h.order
  let : Uncountable {d // D d} :=
    not_countable_iff.mp (fun hc ↦ h.uncountable (Set.countable_coe_iff.mp hc))
  have hrange (d : V) : d ∈ Set.range h.chain.domain ↔ D d := by
    rw [h.chain_range]
    rfl
  have hw : WeaklySpecializes (· ≤ ·) (fun x : FunctionTreeNode h.chain ↦ f x.graph) := by
    intro x y z hxy hxz hfxy hfxz
    have hd (a : FunctionTreeNode h.chain) : D (domain a.graph) := by
      rw [FunctionTreeNode.domain_graph]
      exact a.level.property
    have he := hweak x.graph y.graph z.graph
      x.graph_mem_finitePartialFunctions (hd x)
      y.graph_mem_finitePartialFunctions (hd y)
      z.graph_mem_finitePartialFunctions (hd z) hxy.2 hxz.2 hfxy hfxz
    exact he.imp (FunctionTreeNode.le_iff_graph_subset _ _).mpr
      (FunctionTreeNode.le_iff_graph_subset _ _).mpr
  have hcodes := (forall_filter_codes_iff_firstOrder_candidates h.chain f
    h.uncountable_cofinality hw (hcount.mono (Set.range_comp_subset_range _ _))).mp hfilters
  have heD : (fun d ↦ d ∈ Set.range h.chain.domain) = D := funext fun d ↦ propext (hrange d)
  rw [heD] at hcodes
  simp only [hrange] at hcodes
  intro b hb hd hcof
  obtain ⟨a, rfl⟩ := (FunctionTreeNode.mem_graph_range_iff (C := h.chain) b).mpr
    ⟨hb, (hrange _).mpr hd⟩
  exact hcodes a hcof

end ZFVP.Schmerl
