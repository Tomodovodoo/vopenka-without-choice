import ZFVP.Syntax.FormulaInduction
import ZFVP.Syntax.TermInduction

/-! Literal symbol-preserving extensions of internal languages. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsInternalLanguageExtension (L K : V) : Prop :=
  IsLanguageCode L ∧ IsLanguageCode K ∧
    functionSymbols L ⊆ functionSymbols K ∧ relationSymbols L ⊆ relationSymbols K ∧
    (∀ f ∈ functionSymbols L, (functionArities K) ‘ f = (functionArities L) ‘ f) ∧
    (∀ r ∈ relationSymbols L, (relationArities K) ‘ r = (relationArities L) ‘ r)

instance isInternalLanguageExtension_definable : ℒₛₑₜ-relation[V] IsInternalLanguageExtension := by
  unfold IsInternalLanguageExtension
  definability

theorem IsInternalLanguageExtension.termSet_subset {L K n : V}
    (h : IsInternalLanguageExtension L K) (hn : n ∈ (ω : V)) (Γ : V) :
    termSet L Γ n ⊆ termSet K Γ n := by
  apply termSet_induction h.1 hn Γ (fun t ↦ t ∈ termSet K Γ n) (by definability)
  · exact (termSet_closed h.2.1 hn Γ).1
  · exact (termSet_closed h.2.1 hn Γ).2.1
  · intro f hf args ha ih
    apply (termSet_closed h.2.1 hn Γ).2.2 f (h.2.2.1 f hf)
    rw [h.2.2.2.2.1 f hf]
    exact mem_function_of_mem_function_of_subset (mem_function_range_of_mem_function ha) ih

theorem IsInternalLanguageExtension.atomicArguments {L K Γ n r args : V}
    (h : IsInternalLanguageExtension L K) (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments L Γ n r args) : IsAtomicArguments K Γ n r args := by
  rcases ha with ⟨hr, ha⟩ | ⟨s, hs, hr, ha⟩
  · exact Or.inl ⟨hr, mem_function_of_mem_function_of_subset ha (h.termSet_subset hn Γ)⟩
  · refine Or.inr ⟨s, h.2.2.2.1 s hs, hr, ?_⟩
    rw [h.2.2.2.2.2 s hs]
    exact mem_function_of_mem_function_of_subset ha (h.termSet_subset hn Γ)

theorem IsInternalLanguageExtension.formulaSet_subset {L K : V}
    (h : IsInternalLanguageExtension L K) (Γ n : V) :
    formulaSet L Γ n ⊆ formulaSet K Γ n := by
  have hh := formulaSet_induction h.1 Γ (fun n φ ↦ φ ∈ formulaSet K Γ n) (by definability)
    (fun n hn ↦ formulaSet_constants h.2.1 hn Γ)
    (fun n hn _ _ ha ↦ formulaSet_atoms h.2.1 hn (h.atomicArguments hn ha))
    (fun n hn _ _ _ _ hφ hψ ↦ formulaSet_binary h.2.1 hn hφ hψ)
    (fun n hn _ _ hφ ↦ formulaSet_quantifiers h.2.1 hn hφ)
  exact hh n

end ZFVP
