import ZFVP.SetTheory.DedekindFinite
import ZFVP.SetTheory.UniformRank

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def internallyFiniteFormula : SetTheorySemisentence 1 :=
  f“A. ∃ n ∈ !isω, !CardEQ.dfn A n”

def internallyInfiniteFormula : SetTheorySemisentence 1 := “A. ¬!internallyFiniteFormula A”

def dedekindFiniteFormula : SetTheorySemisentence 1 :=
  f“A. ∀ f ∈ !function.dfn A A, !Injective.dfn f → !range.dfn f = A”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance internallyFiniteFormula_defined :
    ℒₛₑₜ-predicate[V] IsInternallyFinite via internallyFiniteFormula :=
  ⟨fun v ↦ by simp [internallyFiniteFormula, IsInternallyFinite]⟩

instance internallyInfiniteFormula_defined :
    ℒₛₑₜ-predicate[V] IsInternallyInfinite via internallyInfiniteFormula :=
  ⟨fun v ↦ by simp [internallyInfiniteFormula, IsInternallyInfinite]⟩

instance dedekindFiniteFormula_defined :
    ℒₛₑₜ-predicate[V] IsInternallyDedekindFinite via dedekindFiniteFormula :=
  ⟨fun v ↦ by simp [dedekindFiniteFormula, IsInternallyDedekindFinite]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_internallyFinite_iff (j : ElementaryMap V W) (A : V) :
    IsInternallyFinite (j A) ↔ IsInternallyFinite A :=
  (j.map_defined internallyFiniteFormula (fun v ↦ IsInternallyFinite (v 0))
    (fun v ↦ IsInternallyFinite (v 0)) ![A]).symm

theorem map_internallyInfinite_iff (j : ElementaryMap V W) (A : V) :
    IsInternallyInfinite (j A) ↔ IsInternallyInfinite A :=
  (j.map_defined internallyInfiniteFormula (fun v ↦ IsInternallyInfinite (v 0))
    (fun v ↦ IsInternallyInfinite (v 0)) ![A]).symm

theorem map_dedekindFinite_iff (j : ElementaryMap V W) (A : V) :
    IsInternallyDedekindFinite (j A) ↔ IsInternallyDedekindFinite A :=
  (j.map_defined dedekindFiniteFormula (fun v ↦ IsInternallyDedekindFinite (v 0))
    (fun v ↦ IsInternallyDedekindFinite (v 0)) ![A]).symm

end ElementaryMap
end ZFVP
