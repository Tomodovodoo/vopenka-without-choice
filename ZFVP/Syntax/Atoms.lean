import ZFVP.Syntax.TermEvaluation

/-! Logical equality and arbitrary relation symbols in internal atomic syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Equality is a logical token, distinct from every tagged relation symbol. -/
noncomputable def equalityToken : V := ∅
noncomputable def relationToken (r : V) : V := ⟨(1 : V), r⟩ₖ

instance relationToken_definable : ℒₛₑₜ-function₁[V] relationToken := by
  unfold relationToken
  definability

@[simp] theorem relationToken_inj (r s : V) : relationToken r = relationToken s ↔ r = s := by
  simp [relationToken]

@[simp] theorem equalityToken_ne_relationToken (r : V) : equalityToken ≠ relationToken r := by
  intro h
  have hm : ({(1 : V)} : V) ∈ relationToken r := by simp [relationToken, kpair]
  rw [← h] at hm
  exact not_mem_empty hm

def IsAtomicArguments (L Γ n r args : V) : Prop :=
  (r = equalityToken ∧ args ∈ termSet L Γ n ^ (2 : V)) ∨
  ∃ s ∈ relationSymbols L, r = relationToken s ∧
    args ∈ termSet L Γ n ^ ((relationArities L) ‘ s)

instance isAtomicArguments_definable : ℒₛₑₜ-relation₅[V] IsAtomicArguments := by
  unfold IsAtomicArguments equalityToken
  definability

theorem atomicArguments_mem_syntaxUniverse {L Γ n r args : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (ha : IsAtomicArguments L Γ n r args) :
    r ∈ syntaxUniverse L Γ ∧ args ∈ syntaxUniverse L Γ := by
  have hsub := termSet_minimal (syntaxUniverse_termClosed hL hn Γ)
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · exact ⟨codingUniverse_empty_mem _, finiteSequence_mem_codingUniverse _
      ((mem_finiteSequences_iff _ _).mpr ⟨2, by simp,
        mem_function_of_mem_function_of_subset ha hsub⟩)⟩
  · refine ⟨codingUniverse_kpair_closed (codingUniverse_natural_mem _ (by simp))
      ((syntaxUniverse_transitive L Γ).mem_trans hs (relationSymbols_mem_syntaxUniverse hL Γ)), ?_⟩
    exact finiteSequence_mem_codingUniverse _ ((mem_finiteSequences_iff _ _).mpr
      ⟨(relationArities L) ‘ s, hL.relation_arity_natural hs,
        mem_function_of_mem_function_of_subset ha hsub⟩)

end ZFVP

