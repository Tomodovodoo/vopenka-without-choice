import ZFVP.SetTheory.WellOrderedCardinal
import ZFVP.SetTheory.HartogsDictionary

/-! The cardinal dictionary retains the well-orderability guard on its total operation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def wellOrderableFormula : SetTheorySemisentence 1 :=
  “A. ∃ α, !IsOrdinal.dfn α ∧ !CardLE.dfn A α”

def cardinalOfFormula : SetTheorySemisentence 2 :=
  “A κ. !IsOrdinal.dfn κ ∧ !CardEQ.dfn κ A ∧
    ∀ α, !IsOrdinal.dfn α → !CardEQ.dfn α A → κ ⊆ α”

def wellOrderedCardinalFormula : SetTheorySemisentence 2 :=
  “κ A. !cardinalOfFormula A κ ∨ (¬!wellOrderableFormula A ∧ !isEmpty κ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance wellOrderableFormula_defined : ℒₛₑₜ-predicate[V] IsWellOrderable via wellOrderableFormula :=
  ⟨fun v ↦ by simp [wellOrderableFormula, wellOrderable_iff_cardLE_ordinal]⟩

instance cardinalOfFormula_defined : ℒₛₑₜ-relation[V] IsCardinalOf via cardinalOfFormula :=
  ⟨fun v ↦ by simp [cardinalOfFormula, IsCardinalOf, IsLeastOrdinal]⟩

instance wellOrderedCardinalFormula_defined : ℒₛₑₜ-function₁[V] wellOrderedCardinal via wellOrderedCardinalFormula :=
  ⟨fun v ↦ by
    change wellOrderedCardinalFormula.Evalb v ↔ v 0 = wellOrderedCardinal (v 1)
    rw [eq_comm, wellOrderedCardinal_eq_iff]
    simp [wellOrderedCardinalFormula, isEmpty_iff_eq_empty]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_wellOrderable_iff (j : ElementaryMap V W) (A : V) : IsWellOrderable (j A) ↔ IsWellOrderable A :=
  (j.map_defined wellOrderableFormula (fun v ↦ IsWellOrderable (v 0))
    (fun v ↦ IsWellOrderable (v 0)) ![A]).symm

theorem map_wellOrderedCardinal (j : ElementaryMap V W) (A : V) :
    j (wellOrderedCardinal A) = wellOrderedCardinal (j A) :=
  j.map_definedFunction₁ wellOrderedCardinalFormula wellOrderedCardinal wellOrderedCardinal A

end ElementaryMap
end ZFVP
