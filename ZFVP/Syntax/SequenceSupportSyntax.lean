import ZFVP.Syntax.CodingSupportSyntax
import ZFVP.SetTheory.BoundedSequenceSupport

/-! A sequence support containing the symbols contains every internal syntax code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {U L Γ : V} [hU : IsSequenceSupport U]

theorem termSet_subset_sequenceSupport (hL : IsLanguageCode L)
    (hF : functionSymbols L ⊆ U) (hΓ : Γ ⊆ U) {n : V} (hn : n ∈ (ω : V)) :
    termSet L Γ n ⊆ U := by
  apply termSet_minimal
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact hU.kpair_closed _ (IsCodingSupport.numeral_mem 0) _
      (IsCodingSupport.natural_mem (IsOrdinal.toIsTransitive.mem_trans hi hn))
  · intro x hx
    exact hU.kpair_closed _ (IsCodingSupport.numeral_mem 1) _ (hΓ x hx)
  · intro f hf args ha
    exact hU.kpair_closed _ (IsCodingSupport.numeral_mem 2) _
      (hU.kpair_closed _ (hF f hf) _
        (function_mem_sequenceSupport (subset_refl U) (hL.function_arity_natural hf) ha))

theorem atomicArguments_mem_sequenceSupport (hL : IsLanguageCode L)
    (hF : functionSymbols L ⊆ U) (hR : relationSymbols L ⊆ U) (hΓ : Γ ⊆ U)
    {n r args : V} (hn : n ∈ (ω : V)) (ha : IsAtomicArguments L Γ n r args) : r ∈ U ∧ args ∈ U := by
  have hsub := termSet_subset_sequenceSupport hL hF hΓ hn
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · exact ⟨IsCodingSupport.empty_mem, function_mem_sequenceSupport hsub (by simp) ha⟩
  · exact ⟨hU.kpair_closed _ (IsCodingSupport.numeral_mem 1) _ (hR s hs),
      function_mem_sequenceSupport hsub (hL.relation_arity_natural hs) ha⟩

theorem sequenceSupport_formulaClosed (hL : IsLanguageCode L)
    (hF : functionSymbols L ⊆ U) (hR : relationSymbols L ⊆ U) (hΓ : Γ ⊆ U) :
    IsFormulaClosed L Γ U := by
  intro n hn
  have hnU : n ∈ U := IsCodingSupport.natural_mem hn
  have hc (φ : V) (hφ : φ ∈ U) : ⟨n, φ⟩ₖ ∈ U := hU.kpair_closed n hnU φ hφ
  refine ⟨⟨hc _ ?_, hc _ ?_⟩, ?_, ?_, ?_⟩
  · simpa using (CodeExpression.truth : CodeExpression 0).mem_zero (U := U)
  · simpa using (CodeExpression.falsity : CodeExpression 0).mem_zero (U := U)
  · intro r args ha
    obtain ⟨hr, hargs⟩ := atomicArguments_mem_sequenceSupport hL hF hR hΓ hn ha
    constructor
    · apply hc
      simpa [CodeExpression.eval] using (CodeExpression.atom (.var 0) (.var 1)).mem_two hr hargs
    · apply hc
      simpa [CodeExpression.eval] using (CodeExpression.negAtom (.var 0) (.var 1)).mem_two hr hargs
  · intro φ ψ hφ hψ
    have hφU := (kpair_components_mem_transitive hφ).2
    have hψU := (kpair_components_mem_transitive hψ).2
    constructor
    · apply hc
      simpa [CodeExpression.eval] using (CodeExpression.conj (.var 0) (.var 1)).mem_two hφU hψU
    · apply hc
      simpa [CodeExpression.eval] using (CodeExpression.disj (.var 0) (.var 1)).mem_two hφU hψU
  · intro φ hφ
    have hφU := (kpair_components_mem_transitive hφ).2
    constructor
    · apply hc
      simpa [CodeExpression.eval] using (CodeExpression.all (.var 0)).mem_one hφU
    · apply hc
      simpa [CodeExpression.eval] using (CodeExpression.exs (.var 0)).mem_one hφU

theorem formulaFamily_subset_sequenceSupport (hL : IsLanguageCode L)
    (hF : functionSymbols L ⊆ U) (hR : relationSymbols L ⊆ U) (hΓ : Γ ⊆ U) :
    formulaFamily L Γ ⊆ U := formulaFamily_minimal (sequenceSupport_formulaClosed hL hF hR hΓ)

theorem formula_mem_sequenceSupport (hL : IsLanguageCode L)
    (hF : functionSymbols L ⊆ U) (hR : relationSymbols L ⊆ U) (hΓ : Γ ⊆ U)
    {n φ : V} (hφ : φ ∈ formulaSet L Γ n) : φ ∈ U :=
  (kpair_components_mem_transitive (formulaFamily_subset_sequenceSupport hL hF hR hΓ _ ((mem_formulaSet_iff _ _ _ _).mp hφ))).2

end ZFVP
