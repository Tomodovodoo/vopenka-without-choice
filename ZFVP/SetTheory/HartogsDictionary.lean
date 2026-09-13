import ZFVP.SetTheory.Hartogs
import ZFVP.SetTheory.UniformRank

/-! A shared first-order Hartogs dictionary and its elementary transport. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def hartogsNumberFormula : SetTheorySemisentence 2 :=
  “α A. !IsOrdinal.dfn α ∧ ¬!CardLE.dfn α A ∧
    ∀ β, !IsOrdinal.dfn β → ¬!CardLE.dfn β A → α ⊆ β”

def initialOrdinalFormula : SetTheorySemisentence 1 :=
  “κ. !IsOrdinal.dfn κ ∧ ∀ α ∈ κ, ¬!CardLE.dfn κ α”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance hartogsNumberFormula_defined : ℒₛₑₜ-function₁[V] hartogsNumber via hartogsNumberFormula :=
  ⟨fun v ↦ by
    change hartogsNumberFormula.Evalb v ↔ v 0 = hartogsNumber (v 1)
    rw [eq_comm, hartogsNumber_eq_iff]
    simp [hartogsNumberFormula, IsHartogsNumber, IsLeastOrdinal]⟩

instance initialOrdinalFormula_defined : ℒₛₑₜ-predicate[V] IsInitialOrdinal via initialOrdinalFormula :=
  ⟨fun v ↦ by simp [initialOrdinalFormula, IsInitialOrdinal]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_hartogsNumber (j : ElementaryMap V W) (A : V) : j (hartogsNumber A) = hartogsNumber (j A) :=
  j.map_definedFunction₁ hartogsNumberFormula hartogsNumber hartogsNumber A

theorem map_initialOrdinal_iff (j : ElementaryMap V W) (κ : V) : IsInitialOrdinal (j κ) ↔ IsInitialOrdinal κ :=
  (j.map_defined initialOrdinalFormula (fun v ↦ IsInitialOrdinal (v 0))
    (fun v ↦ IsInitialOrdinal (v 0)) ![κ]).symm

end ElementaryMap
end ZFVP
