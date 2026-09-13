import ZFVP.Syntax.Subformulas

/-! A family with constructor inversion contains only internally generated formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsFormulaGenerated (L Γ Q : V) : Prop := ∀ p ∈ Q, ∃ n ∈ (ω : V), ∃ φ, p = ⟨n, φ⟩ₖ ∧
  (φ = truthCode ∨ φ = falsityCode ∨
    (∃ r args, IsAtomicArguments L Γ n r args ∧ (φ = atomCode r args ∨ φ = negAtomCode r args)) ∨
    (∃ ψ χ, ⟨n, ψ⟩ₖ ∈ Q ∧ ⟨n, χ⟩ₖ ∈ Q ∧ (φ = andCode ψ χ ∨ φ = orCode ψ χ)) ∨
    ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ Q ∧ (φ = allCode ψ ∨ φ = existsCode ψ))

theorem formulaFamily_generated {L : V} (hL : IsLanguageCode L) (Γ : V) :
    IsFormulaGenerated L Γ (formulaFamily L Γ) := by
  intro p hp
  obtain ⟨n, hn, φ, rfl⟩ := formulaFamily_context hL Γ hp
  refine ⟨n, hn, φ, rfl, ?_⟩
  have hc := formulaSet_cases hL ((mem_formulaSet_iff _ _ _ _).mpr hp)
  simpa only [IsFormulaConstructor, mem_formulaSet_iff] using hc

theorem formulaGenerated_subset {L Γ Q : V} (hL : IsLanguageCode L) (hQ : IsFormulaGenerated L Γ Q) :
    Q ⊆ formulaFamily L Γ := by
  apply internalWellFounded_induction (subformulaRelation_wellFounded Q)
    (fun p ↦ p ∈ formulaFamily L Γ) (by definability)
  intro p hp ih
  obtain ⟨n, hn, φ, rfl, hc⟩ := hQ p hp
  apply (mem_formulaSet_iff _ _ _ _).mp
  rcases hc with rfl | rfl | ⟨r, args, ha, he⟩ | ⟨ψ, χ, hψ, hχ, he⟩ | ⟨ψ, hψ, he⟩
  · exact (formulaSet_constants hL hn Γ).1
  · exact (formulaSet_constants hL hn Γ).2
  · rcases he with rfl | rfl
    · exact (formulaSet_atoms hL hn ha).1
    · exact (formulaSet_atoms hL hn ha).2
  · have hs : ψ ∈ formulaSet L Γ n := (mem_formulaSet_iff _ _ _ _).mpr
      (ih _ hψ ((kpair_mem_subformulaRelation_iff _ _ _).mpr ⟨hψ, hp,
        Or.inl ⟨n, ψ, χ, he.imp (congrArg (kpair n)) (congrArg (kpair n)), Or.inl rfl⟩⟩))
    have ht : χ ∈ formulaSet L Γ n := (mem_formulaSet_iff _ _ _ _).mpr
      (ih _ hχ ((kpair_mem_subformulaRelation_iff _ _ _).mpr ⟨hχ, hp,
        Or.inl ⟨n, ψ, χ, he.imp (congrArg (kpair n)) (congrArg (kpair n)), Or.inr rfl⟩⟩))
    rcases he with rfl | rfl
    · exact (formulaSet_binary hL hn hs ht).1
    · exact (formulaSet_binary hL hn hs ht).2
  · have hs : ψ ∈ formulaSet L Γ (succ n) := (mem_formulaSet_iff _ _ _ _).mpr
      (ih _ hψ ((kpair_mem_subformulaRelation_iff _ _ _).mpr ⟨hψ, hp,
        Or.inr ⟨n, ψ, he.imp (congrArg (kpair n)) (congrArg (kpair n)), rfl⟩⟩))
    rcases he with rfl | rfl
    · exact (formulaSet_quantifiers hL hn hs).1
    · exact (formulaSet_quantifiers hL hn hs).2

end ZFVP
