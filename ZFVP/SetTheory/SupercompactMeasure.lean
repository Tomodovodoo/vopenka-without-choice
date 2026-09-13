import ZFVP.SetTheory.SetUltrafilter
import ZFVP.SetTheory.GroundUniqueness

/-! # Supercompactness in the measure sense

This module defines supercompactness by a measure rather than by an embedding. Nothing here
mentions an elementary embedding or an ultrapower.

The base set is `smallSubsetsBelow κ lam`, which is exactly `P_κ(lam)`: the subsets of `lam`
whose size is below `κ`. It comes from `ZFVP.SetTheory.GroundUniqueness`, where it is
`sep (℘ lam) (USmall κ)` and `mem_smallSubsetsBelow_iff` characterizes its members.

A measure on `P_κ(lam)` is an ultrafilter `U` on that base set which is `κ`-complete
(`IsOrdinalCompleteOn`), fine (`IsFineOn`) and normal (`IsNormalOn`). `IsOrdinalCompleteOn K κ U`
is stated for a general base set `K`, unlike `IsOrdinalComplete` in
`ZFVP.SetTheory.SetUltrafilter`, whose base set is hardwired to `κ` itself.

`IsSupercompact κ` says that `κ` is an initial ordinal above `ω` carrying such a measure on
`P_κ(lam)` for every ordinal `lam` at or above `κ`. This is the definition of supercompactness
used by Bagaria, "C(n)-cardinals", section 2, and by the paper this project formalizes.

The equivalence of `IsSupercompact` with Magidor's small-embedding predicate
`IsMagidorSupercompact` is Magidor's theorem (Magidor 1971; Kanamori, *The Higher Infinite*,
22.10). It is proved in later modules of this wave, not here.

The auxiliary definitions `fineSetOn`, `regressiveSetOn`, `constantSetOn`, `IsFineIn` and
`IsNormalIn` take the base set as an argument. They exist so that the `definability` tactic
sees formulas with one fewer varying argument; the exported predicates are the ones above.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance uSmall_definable_two : ℒₛₑₜ-relation[V] USmall := by
  unfold USmall
  definability

instance smallSubsetsBelow_definable : ℒₛₑₜ-function₂[V] smallSubsetsBelow := by
  have hd : ℒₛₑₜ-relation₃[V] (fun S δ θ ↦ ∀ x, x ∈ S ↔ x ⊆ θ ∧ USmall δ x) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = smallSubsetsBelow (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_smallSubsetsBelow_iff]

/-- `U` is closed under intersections of families of fewer than `κ` of its members, taken
inside the base set `K`. -/
def IsOrdinalCompleteOn (K κ U : V) : Prop :=
  ∀ α ∈ κ, ∀ g ∈ U ^ α, indexedIntersection K α g ∈ U

/-- The members of the base set `S` that contain `ξ`. -/
noncomputable def fineSetOn (S ξ : V) : V := {x ∈ S ; ξ ∈ x}

instance fineSetOn_definable : ℒₛₑₜ-function₂[V] fineSetOn := by
  have hd : ℒₛₑₜ-relation₃[V] (fun Y S ξ ↦ ∀ x, x ∈ Y ↔ x ∈ S ∧ ξ ∈ x) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = fineSetOn (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [fineSetOn, mem_sep_iff]

/-- The members of the base set `S` on which `f` is regressive. -/
noncomputable def regressiveSetOn (S f : V) : V := {x ∈ S ; f ‘ x ∈ x}

instance regressiveSetOn_definable : ℒₛₑₜ-function₂[V] regressiveSetOn := by
  have hd : ℒₛₑₜ-relation₃[V] (fun Y S f ↦ ∀ x, x ∈ Y ↔ x ∈ S ∧ f ‘ x ∈ x) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = regressiveSetOn (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [regressiveSetOn, mem_sep_iff]

/-- The members of the base set `S` on which `f` takes the value `ξ`. -/
noncomputable def constantSetOn (S f ξ : V) : V := {x ∈ S ; f ‘ x = ξ}

instance constantSetOn_definable : ℒₛₑₜ-function₃[V] constantSetOn := by
  have hd : ℒₛₑₜ-relation₄[V] (fun Y S f ξ ↦ ∀ x, x ∈ Y ↔ x ∈ S ∧ f ‘ x = ξ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = constantSetOn (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [constantSetOn, mem_sep_iff]

/-- Fineness stated for a general base set `S`. -/
def IsFineIn (S lam U : V) : Prop := ∀ ξ ∈ lam, fineSetOn S ξ ∈ U

instance isFineIn_definable : ℒₛₑₜ-relation₃[V] IsFineIn := by
  unfold IsFineIn
  definability

/-- Normality stated for a general base set `S`. -/
def IsNormalIn (S lam U : V) : Prop :=
  ∀ f ∈ lam ^ S, regressiveSetOn S f ∈ U → ∃ ξ ∈ lam, constantSetOn S f ξ ∈ U

instance isNormalIn_definable : ℒₛₑₜ-relation₃[V] IsNormalIn := by
  unfold IsNormalIn
  definability

/-- Every ordinal below `lam` belongs to almost every member of `P_κ lam`. -/
def IsFineOn (κ lam U : V) : Prop :=
  ∀ ξ ∈ lam, {x ∈ smallSubsetsBelow κ lam ; ξ ∈ x} ∈ U

/-- A function on `P_κ lam` that is regressive on a set in `U` is constant on a set in `U`. -/
def IsNormalOn (κ lam U : V) : Prop :=
  ∀ f ∈ lam ^ (smallSubsetsBelow κ lam),
    {x ∈ smallSubsetsBelow κ lam ; f ‘ x ∈ x} ∈ U →
      ∃ ξ ∈ lam, {x ∈ smallSubsetsBelow κ lam ; f ‘ x = ξ} ∈ U

def IsNormalFineMeasure (κ lam U : V) : Prop :=
  IsSetUltrafilter (smallSubsetsBelow κ lam) U ∧
    IsOrdinalCompleteOn (smallSubsetsBelow κ lam) κ U ∧ IsFineOn κ lam U ∧ IsNormalOn κ lam U

/-- Supercompactness in the measure sense: a normal fine `κ`-complete ultrafilter on
`P_κ lam` for every `lam` at or above `κ`. -/
def IsSupercompact (κ : V) : Prop :=
  IsInitialOrdinal κ ∧ (ω : V) ∈ κ ∧
    ∀ lam, IsOrdinal lam → κ ⊆ lam → ∃ U, IsNormalFineMeasure κ lam U

instance isOrdinalCompleteOn_definable : ℒₛₑₜ-relation₃[V] IsOrdinalCompleteOn := by
  unfold IsOrdinalCompleteOn
  definability

instance isFineOn_definable : ℒₛₑₜ-relation₃[V] IsFineOn := by
  have hd : ℒₛₑₜ-relation₃[V] (fun κ lam U ↦ IsFineIn (smallSubsetsBelow κ lam) lam U) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  exact Iff.rfl

instance isNormalOn_definable : ℒₛₑₜ-relation₃[V] IsNormalOn := by
  have hd : ℒₛₑₜ-relation₃[V] (fun κ lam U ↦ IsNormalIn (smallSubsetsBelow κ lam) lam U) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  exact Iff.rfl

instance isNormalFineMeasure_definable : ℒₛₑₜ-relation₃[V] IsNormalFineMeasure := by
  unfold IsNormalFineMeasure
  definability

instance isSupercompact_definable : ℒₛₑₜ-predicate[V] IsSupercompact := by
  unfold IsSupercompact
  definability

theorem IsSupercompact.isOrdinal {κ : V} (h : IsSupercompact κ) : IsOrdinal κ := h.1.1

theorem IsSupercompact.measure {κ lam : V} (h : IsSupercompact κ) (hlam : IsOrdinal lam)
    (hle : κ ⊆ lam) : ∃ U, IsNormalFineMeasure κ lam U := h.2.2 lam hlam hle

/-- The measure of a normal fine measure is a set of subsets of `P_κ lam`, is nonempty and
omits the empty set. -/
theorem IsNormalFineMeasure.base_mem {κ lam U : V} (h : IsNormalFineMeasure κ lam U) :
    smallSubsetsBelow κ lam ∈ U := h.1.2.1

theorem IsNormalFineMeasure.empty_not_mem {κ lam U : V} (h : IsNormalFineMeasure κ lam U) :
    (∅ : V) ∉ U := h.1.2.2.1

/-- A set containing a set of the measure is in the measure. -/
theorem IsNormalFineMeasure.upward {κ lam U X Y : V} (h : IsNormalFineMeasure κ lam U)
    (hX : X ∈ U) (hY : Y ⊆ smallSubsetsBelow κ lam) (hXY : X ⊆ Y) : Y ∈ U :=
  h.1.2.2.2.1 X hX Y hY hXY

/-- If a subset of the base set is not in the measure, its relative complement is. -/
theorem IsNormalFineMeasure.complement {κ lam U X : V} (h : IsNormalFineMeasure κ lam U)
    (hX : X ⊆ smallSubsetsBelow κ lam) (hnot : X ∉ U) :
    relativeComplement (smallSubsetsBelow κ lam) X ∈ U :=
  (h.1.2.2.2.2.2 X hX).resolve_left hnot

end ZFVP
