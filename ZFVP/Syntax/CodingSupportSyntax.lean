import ZFVP.Syntax.BoundedConstructorExpressions
import ZFVP.Syntax.LevyCodes

/-! A coding support contains every pure membership-language syntax code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CodeExpression

theorem mem_zero {U : V} [IsCodingSupport U] (t : CodeExpression 0) : t.eval (V := V) ![] ∈ U :=
  t.eval_mem ![] (Fin.elim0 ·)

theorem mem_one {U x : V} [IsCodingSupport U] (t : CodeExpression 1) (hx : x ∈ U) : t.eval ![x] ∈ U :=
  t.eval_mem ![x] (by simpa using hx)

theorem mem_two {U x y : V} [IsCodingSupport U] (t : CodeExpression 2) (hx : x ∈ U) (hy : y ∈ U) :
    t.eval ![x, y] ∈ U := t.eval_mem ![x, y] (by simpa using And.intro hx hy)

end CodeExpression

theorem membershipAtomicArguments_mem_support {U n r args : V} [hU : IsCodingSupport U]
    (hn : n ∈ (ω : V)) (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) : r ∈ U ∧ args ∈ U := by
  obtain ⟨hr, i, hi, j, hj, rfl⟩ := (membershipAtomicArguments_iff hn).mp ha
  have hnU : n ∈ U := IsCodingSupport.natural_mem hn
  refine ⟨?_, ?_⟩
  · rcases hr with rfl | rfl | rfl
    · exact IsCodingSupport.empty_mem
    · exact hU.kpair_closed _ (IsCodingSupport.numeral_mem 1) _ (IsCodingSupport.numeral_mem 0)
    · exact hU.kpair_closed _ (IsCodingSupport.numeral_mem 1) _ (IsCodingSupport.numeral_mem 1)
  · simpa [CodeExpression.eval] using
      (CodeExpression.boundArgs (.var 0) (.var 1)).mem_two (hU.mem_trans hi hnU) (hU.mem_trans hj hnU)

theorem codingSupport_formulaClosed (U : V) [hU : IsCodingSupport U] :
    IsFormulaClosed membershipLanguageCode ∅ U := by
  intro n hn
  have hnU : n ∈ U := IsCodingSupport.natural_mem hn
  have hc (φ : V) (hφ : φ ∈ U) : ⟨n, φ⟩ₖ ∈ U := hU.kpair_closed n hnU φ hφ
  refine ⟨⟨hc _ ?_, hc _ ?_⟩, ?_, ?_, ?_⟩
  · simpa using (CodeExpression.truth : CodeExpression 0).mem_zero (U := U)
  · simpa using (CodeExpression.falsity : CodeExpression 0).mem_zero (U := U)
  · intro r args ha
    obtain ⟨hr, hargs⟩ := membershipAtomicArguments_mem_support (U := U) hn ha
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

theorem membershipFormulaFamily_subset_support (U : V) [IsCodingSupport U] :
    formulaFamily (membershipLanguageCode : V) ∅ ⊆ U := formulaFamily_minimal (codingSupport_formulaClosed U)

theorem boundedFormulaFamily_subset_support (U : V) [IsCodingSupport U] : (boundedFormulaFamily : V) ⊆ U :=
  subset_trans boundedFormulaFamily_subset (membershipFormulaFamily_subset_support U)

theorem levyFormulaFamily_subset_support (k : ℕ) (p : LevyPolarity) (U : V) [IsCodingSupport U] :
    (levyFormulaFamily k p : V) ⊆ U := subset_trans (levyFormulaFamily_subset k p) (membershipFormulaFamily_subset_support U)

end ZFVP
