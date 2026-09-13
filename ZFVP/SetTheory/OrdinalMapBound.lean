import ZFVP.SetTheory.Cofinality

/-! Failure of cofinality bounds an ordinal-valued graph. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinalMap_bounded_of_not_cofinal {γ A g : V} [IsOrdinal γ]
    (hg : g ∈ γ ^ A) (hno : ¬IsCofinalMap γ A g) :
    ∃ β ∈ γ, ∀ x ∈ A, g ‘ x ∈ β := by
  classical
  by_contra hn
  apply hno
  refine ⟨hg, ?_⟩
  intro β hβ
  let : IsOrdinal β := IsOrdinal.of_mem hβ
  by_contra hbad
  apply hn
  refine ⟨β, hβ, ?_⟩
  intro x hx
  let : IsOrdinal (g ‘ x) := IsOrdinal.of_mem (function_value_mem hg hx)
  rcases IsOrdinal.mem_trichotomy (g ‘ x) β with hl | he | hh
  · exact hl
  · exact False.elim (hbad ⟨x, hx, subset_of_eq he.symm⟩)
  · exact False.elim (hbad ⟨x, hx, IsOrdinal.toIsTransitive.transitive _ hh⟩)

end ZFVP
