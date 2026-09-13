import ZFVP.SetTheory.MonotoneCofinality
import ZFVP.SetTheory.CardinalDictionary

/-! Shared cofinality and infinite regular-cardinal definitions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def cofinalMapFormula : SetTheorySemisentence 3 :=
  f“α β f. f ∈ !function.dfn α β ∧ ∀ ξ ∈ α, ∃ i ∈ β, ξ ⊆ !value.dfn f i”

def cofinalityFormula : SetTheorySemisentence 2 :=
  “α κ. !IsOrdinal.dfn α ∧ !IsOrdinal.dfn κ ∧ (∃ f, !cofinalMapFormula α κ f) ∧
    ∀ β, !IsOrdinal.dfn β → (∃ f, !cofinalMapFormula α β f) → κ ⊆ β”

def internalCofinalityFormula : SetTheorySemisentence 2 :=
  “κ α. !cofinalityFormula α κ ∨ (¬!IsOrdinal.dfn α ∧ !isEmpty κ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsRegularCardinal (κ : V) : Prop :=
  IsInitialOrdinal κ ∧ (ω : V) ⊆ κ ∧ internalCofinality κ = κ

theorem internalCofinality_regular (α : V) [IsOrdinal α]
    (hω : (ω : V) ⊆ internalCofinality α) : IsRegularCardinal (internalCofinality α) :=
  ⟨internalCofinality_initial α, hω, internalCofinality_idempotent α⟩

theorem regularCardinal_maps_bounded {κ β f : V} (hκ : IsRegularCardinal κ)
    (hβ : β ∈ κ) (hf : f ∈ κ ^ β) : ∃ ξ ∈ κ, ∀ i ∈ β, f ‘ i ∈ ξ := by
  have : IsOrdinal κ := hκ.1.1
  exact map_below_cofinality_bounded (hκ.2.2.symm ▸ hβ) hf

def regularCardinalFormula : SetTheorySemisentence 1 :=
  f“κ. !initialOrdinalFormula κ ∧ !isω ⊆ κ ∧ !internalCofinalityFormula κ κ”

instance cofinalMapFormula_defined : ℒₛₑₜ-relation₃[V] IsCofinalMap via cofinalMapFormula :=
  ⟨fun v ↦ by simp [cofinalMapFormula, IsCofinalMap]⟩

instance cofinalityFormula_defined : ℒₛₑₜ-relation[V] IsCofinality via cofinalityFormula :=
  ⟨fun v ↦ by simp [cofinalityFormula, IsCofinality, IsLeastOrdinal]⟩

instance internalCofinalityFormula_defined : ℒₛₑₜ-function₁[V] internalCofinality via internalCofinalityFormula :=
  ⟨fun v ↦ by
    change internalCofinalityFormula.Evalb v ↔ v 0 = internalCofinality (v 1)
    rw [eq_comm, internalCofinality_eq_iff]
    simp [internalCofinalityFormula, isEmpty_iff_eq_empty]⟩

instance regularCardinalFormula_defined : ℒₛₑₜ-predicate[V] IsRegularCardinal via regularCardinalFormula :=
  ⟨fun v ↦ by simp [regularCardinalFormula, IsRegularCardinal, eq_comm]⟩

instance isRegularCardinal_definable : ℒₛₑₜ-predicate[V] IsRegularCardinal :=
  regularCardinalFormula_defined.to_definable

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_internalCofinality (j : ElementaryMap V W) (α : V) :
    j (internalCofinality α) = internalCofinality (j α) :=
  j.map_definedFunction₁ internalCofinalityFormula internalCofinality internalCofinality α

theorem map_regularCardinal_iff (j : ElementaryMap V W) (κ : V) : IsRegularCardinal (j κ) ↔ IsRegularCardinal κ :=
  (j.map_defined regularCardinalFormula (fun v ↦ IsRegularCardinal (v 0))
    (fun v ↦ IsRegularCardinal (v 0)) ![κ]).symm

end ElementaryMap
end ZFVP
