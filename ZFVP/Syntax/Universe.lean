import ZFVP.SetTheory.FiniteCodingClosure
import ZFVP.ModelTheory.LanguageCode

/-! A common internal coding universe for a language and a free-variable set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def syntaxUniverse (L Γ : V) : V := codingUniverse ({L, Γ} : V)

instance syntaxUniverse_definable : ℒₛₑₜ-function₂[V] syntaxUniverse := by
  unfold syntaxUniverse
  definability

instance syntaxUniverse_transitive (L Γ : V) : IsTransitive (syntaxUniverse L Γ) :=
  codingUniverse_transitive _

theorem language_mem_syntaxUniverse (L Γ : V) : L ∈ syntaxUniverse L Γ :=
  (codingUniverse_transitive _).mem_trans (by simp) (self_mem_codingUniverse ({L, Γ} : V))

theorem freeVariables_mem_syntaxUniverse (L Γ : V) : Γ ∈ syntaxUniverse L Γ :=
  (codingUniverse_transitive _).mem_trans (by simp) (self_mem_codingUniverse ({L, Γ} : V))

theorem functionSymbols_mem_syntaxUniverse {L : V} (hL : IsLanguageCode L) (Γ : V) :
    functionSymbols L ∈ syntaxUniverse L Γ := by
  have hp : languageCode (functionSymbols L) (relationSymbols L)
      (functionArities L) (relationArities L) ∈ syntaxUniverse L Γ := by
    rw [← hL.1]
    exact language_mem_syntaxUniverse L Γ
  exact (kpair_components_mem_transitive hp).1

theorem relationSymbols_mem_syntaxUniverse {L : V} (hL : IsLanguageCode L) (Γ : V) :
    relationSymbols L ∈ syntaxUniverse L Γ := by
  have hp : languageCode (functionSymbols L) (relationSymbols L)
      (functionArities L) (relationArities L) ∈ syntaxUniverse L Γ := by
    rw [← hL.1]
    exact language_mem_syntaxUniverse L Γ
  exact (kpair_components_mem_transitive (kpair_components_mem_transitive hp).2).1

end ZFVP
