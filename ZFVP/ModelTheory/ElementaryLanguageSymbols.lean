import ZFVP.Syntax.ElementaryFoundationEncoding

/-! Symbol arities and their standard representations reflect through elementary maps. -/
namespace ZFVP.ElementaryMap
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (j : ElementaryMap V W)

theorem map_functionSymbols (L : V) : j (functionSymbols L) = functionSymbols (j L) :=
  j.map_definedFunction₁ functionSymbolsFormula functionSymbols functionSymbols L

theorem map_relationSymbols (L : V) : j (relationSymbols L) = relationSymbols (j L) :=
  j.map_definedFunction₁ relationSymbolsFormula relationSymbols relationSymbols L

theorem map_functionArities (L : V) : j (functionArities L) = functionArities (j L) :=
  j.map_definedFunction₁ functionAritiesFormula functionArities functionArities L

theorem map_relationArities (L : V) : j (relationArities L) = relationArities (j L) :=
  j.map_definedFunction₁ relationAritiesFormula relationArities relationArities L

theorem functionRepresentation_iff {Λ : Language} (L : V) (F : ∀ {k}, Λ.Func k → V) :
    (∀ k (f : Λ.Func k), j (F f) ∈ functionSymbols (j L) ∧
      (functionArities (j L)) ‘ (j (F f)) = (k : W)) ↔
    (∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧ (functionArities L) ‘ (F f) = (k : V)) := by
  simp only [← j.map_functionSymbols, ← j.map_functionArities, ← j.map_value,
    ← j.map_numeral, j.map_mem_iff, j.injective.eq_iff]

theorem relationRepresentation_iff {Λ : Language} (L : V) (R : ∀ {k}, Λ.Rel k → V) :
    (∀ k (r : Λ.Rel k), j (R r) ∈ relationSymbols (j L) ∧
      (relationArities (j L)) ‘ (j (R r)) = (k : W)) ↔
    (∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧ (relationArities L) ‘ (R r) = (k : V)) := by
  simp only [← j.map_relationSymbols, ← j.map_relationArities, ← j.map_value,
    ← j.map_numeral, j.map_mem_iff, j.injective.eq_iff]

end ZFVP.ElementaryMap
