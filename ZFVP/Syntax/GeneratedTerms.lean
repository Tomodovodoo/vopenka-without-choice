import ZFVP.Syntax.Subterms

/-! Constructor inversion determines the term set, by internal well-foundedness. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsTermGenerated (L Γ n T : V) : Prop := ∀ t ∈ T,
  (∃ i ∈ n, t = boundVarCode i) ∨ (∃ x ∈ Γ, t = freeVarCode x) ∨
    ∃ f ∈ functionSymbols L, ∃ args ∈ T ^ ((functionArities L) ‘ f), t = functionTermCode f args

theorem termSet_generated {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ : V) :
    IsTermGenerated L Γ n (termSet L Γ n) := fun _ ht ↦ termSet_cases hL hn Γ ht

theorem termGenerated_subset {L Γ n T : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hT : IsTermGenerated L Γ n T) : T ⊆ termSet L Γ n := by
  apply internalWellFounded_induction (subtermRelation_wellFounded T)
    (fun t ↦ t ∈ termSet L Γ n) (by definability)
  intro t ht ih
  rcases hT t ht with ⟨i, hi, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨f, hf, args, ha, rfl⟩
  · exact (termSet_closed hL hn Γ).1 i hi
  · exact (termSet_closed hL hn Γ).2.1 x hx
  · apply (termSet_closed hL hn Γ).2.2 f hf args
    apply mem_function_of_mem_function_of_subset (mem_function_range_of_mem_function ha)
    intro s hs
    have hsT := range_subset_of_mem_function ha s hs
    exact ih s hsT ((kpair_mem_subtermRelation_iff _ _ _).mpr ⟨hsT, ht, f, args, rfl, hs⟩)

end ZFVP
