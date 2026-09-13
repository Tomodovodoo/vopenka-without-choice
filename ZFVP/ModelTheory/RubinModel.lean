import ZFVP.ModelTheory.WeaklyRubinDeadEnd

/-! The vocabulary of Enayat's Definition 5.10 (filters on a definable poset) from "Models of set
theory: extensions and dead ends", in the class-sized form Definition 5.13 needs.

A poset is given here by a carrier predicate `P : V → Prop` together with an order
`le : V → V → Prop`, both allowed to be arbitrary definable classes. The version in
`ZFVP.ModelTheory.MaximalFilters` covers only the case of an internal poset ordered by inclusion,
which is what Definition 5.16 uses; Definition 5.13 quantifies over all definable posets, and the
tree of classes in Enayat's Remark 5.14 is not ordered by inclusion, so the order cannot be fixed
to `⊆` here.

The compatibility lemmas `isFilterOn_subset_iff`, `isMaximalFilterOn_subset_iff` and
`hasCofinalOmegaOneChainOn_subset_iff` say that the two vocabularies agree on the inclusion-ordered
internal case.

Definition 5.13 itself is not here. Its literal reading is refutable in ZF, so it lives in
`ZFVP.ModelTheory.RubinDefinableFilters` next to the refutation `ZFVP.not_isRubin`, together with
the corrected `IsRubinDefinable` that the development uses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Definition 5.10 for a definable poset -/

/-- Enayat 5.10(b) for a poset given by a carrier predicate `P` and an order `le`: `F` is a subset
of `P` whose subposet is directed. -/
def IsFilterOn (P : V → Prop) (le : V → V → Prop) (F : V → Prop) : Prop :=
  (∀ x, F x → P x) ∧ ∀ x y, F x → F y → ∃ z, F z ∧ le x z ∧ le y z

/-- Enayat 5.10(c): a filter with no proper extension to a filter. -/
def IsMaximalFilterOn (P : V → Prop) (le : V → V → Prop) (F : V → Prop) : Prop :=
  IsFilterOn P le F ∧
    ∀ F' : V → Prop, IsFilterOn P le F' → (∀ x, F x → F' x) → ∀ x, F' x → F x

/-- A chain of order type `ω₁` inside `F`, strictly increasing for `le` and cofinal in `F`. The
index order is the one used by `ZFVP.IsCofinalOmegaOneChain`. -/
def IsCofinalOmegaOneChainOn (le : V → V → Prop) (F : V → Prop)
    (p : Ordinal.ToType (Ordinal.omega.{0} 1) → V) : Prop :=
  (∀ i, F (p i)) ∧ (∀ i i', i < i' → le (p i) (p i') ∧ p i ≠ p i') ∧
    (∀ x, F x → ∃ i, le x (p i))

/-- `F` has a cofinal chain of length `ω₁`. -/
def HasCofinalOmegaOneChainOn (le : V → V → Prop) (F : V → Prop) : Prop :=
  ∃ p, IsCofinalOmegaOneChainOn le F p

/-- A class is coded in the model if it is the extension of one of its own sets. -/
def IsCoded (F : V → Prop) : Prop := ∃ m : V, ∀ x, x ∈ m ↔ F x

/-- `le` is a partial order on the carrier `P`: reflexive, transitive and antisymmetric there.
Enayat says "poset", so this is stated rather than left implicit. -/
def IsPartialOrderOn (P : V → Prop) (le : V → V → Prop) : Prop :=
  (∀ x, P x → le x x) ∧
    (∀ x y z, P x → P y → P z → le x y → le y z → le x z) ∧
    (∀ x y, P x → P y → le x y → le y x → x = y)

/-- `(P, le)` is a directed poset with no maximum element. Directedness includes the requirement
that `P` be nonempty, as usual for directed sets: without it the empty class would count as a
directed poset with no maximum, and no chain can live inside it, so clause (a) of Definition 5.13
would be contradictory. -/
def IsDirectedNoMaxOn (P : V → Prop) (le : V → V → Prop) : Prop :=
  (∃ x, P x) ∧
    (∀ x y, P x → P y → ∃ z, P z ∧ le x z ∧ le y z) ∧
    ¬ ∃ m, P m ∧ ∀ x, P x → le x m

/-! ### Agreement with the inclusion-ordered internal case -/

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- For an internal poset ordered by inclusion, 5.10(b) here is the definition already in
`ZFVP.ModelTheory.MaximalFilters`. -/
theorem isFilterOn_subset_iff (P : V) (F : V → Prop) :
    IsFilterOn (· ∈ P) (· ⊆ ·) F ↔ IsInternalFilter P F := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- The same for 5.10(c). -/
theorem isMaximalFilterOn_subset_iff (P : V) (F : V → Prop) :
    IsMaximalFilterOn (· ∈ P) (· ⊆ ·) F ↔ IsMaximalInternalFilter P F := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- The same for cofinal `ω₁`-chains. -/
theorem isCofinalOmegaOneChainOn_subset_iff (F : V → Prop)
    (p : Ordinal.ToType (Ordinal.omega.{0} 1) → V) :
    IsCofinalOmegaOneChainOn (· ⊆ ·) F p ↔ IsCofinalOmegaOneChain F p := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- The same for the existence of a cofinal `ω₁`-chain. -/
theorem hasCofinalOmegaOneChainOn_subset_iff (F : V → Prop) :
    HasCofinalOmegaOneChainOn (· ⊆ ·) F ↔ HasCofinalOmegaOneChain F := Iff.rfl

/-! ### The two posets used in Definition 5.16 -/

/-- Inclusion is a partial order on any carrier. -/
theorem isPartialOrderOn_subset (P : V → Prop) : IsPartialOrderOn P (· ⊆ ·) :=
  ⟨fun x _ ↦ subset_refl x, fun _ _ _ _ _ _ hxy hyz ↦ subset_trans hxy hyz,
    fun _ _ _ _ hxy hyx ↦ subset_antisymm hxy hyx⟩

/-- Membership in `[a]^{<ω}` is definable with `a` as a parameter. -/
theorem mem_finiteSubsets_definable (a : V) :
    ℒₛₑₜ-predicate[V] (fun x ↦ x ∈ finiteSubsets a) := by definability

/-- Membership in `Fin(a,2)` is definable with `a` as a parameter. -/
theorem mem_finitePartialFunctions_definable (a : V) :
    ℒₛₑₜ-predicate[V] (fun x ↦ x ∈ finitePartialFunctions a ((2 : ℕ) : V)) := by definability

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- Inclusion is a definable relation. -/
theorem subset_definable : ℒₛₑₜ-relation[V] (fun x y : V ↦ x ⊆ y) := by definability

/-- For an internally infinite `a`, the poset `[a]^{<ω}` ordered by inclusion is directed and has
no maximum element: it contains `∅`, it is closed under binary unions, and every finite subset of
an infinite set is properly contained in a larger finite subset. -/
theorem isDirectedNoMaxOn_finiteSubsets {a : V} (ha : IsInternallyInfinite a) :
    IsDirectedNoMaxOn (fun x ↦ x ∈ finiteSubsets a) (· ⊆ ·) := by
  refine ⟨⟨∅, empty_mem_finiteSubsets a⟩, ?_, ?_⟩
  · intro x y hx hy
    exact ⟨x ∪ y, finiteSubsets_union hx hy, fun z hz ↦ mem_union_iff.mpr (Or.inl hz),
      fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩
  · rintro ⟨m, hm, hmax⟩
    obtain ⟨y, hy, hmy, hne⟩ := finiteSubsets_no_maximum ha hm
    exact hne (subset_antisymm hmy (hmax y hy))

end ZFVP
