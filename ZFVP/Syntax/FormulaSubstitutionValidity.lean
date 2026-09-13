import ZFVP.Syntax.FormulaSubstitutionEquations

/-! Substitution preserves internal formula validity at every binder depth. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicArguments_substituted {L Γ Δ n m B E r args : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hB : B ∈ termSet L Δ m ^ n) (hE : E ∈ termSet L Δ m ^ Γ)
    (ha : IsAtomicArguments L Γ n r args) :
    IsAtomicArguments L Δ m r (compose args (termSubstitution L Γ n B E)) := by
  have hsub := termSubstitution_mem_function hL hn hm hB hE
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · exact Or.inl ⟨rfl, compose_function ha hsub⟩
  · exact Or.inr ⟨s, hs, rfl, compose_function ha hsub⟩

theorem formulaSubstitutionGraph_valid {L Γ Δ G : V} (hL : IsLanguageCode L)
    (hG : ∀ k ∈ (ω : V), IsSubstitutionState L Γ Δ (G ‘ k))
    (hsource : ∀ k ∈ (ω : V), stateSource (G ‘ (succ k)) = succ (stateSource (G ‘ k)))
    (htarget : ∀ k ∈ (ω : V), stateTarget (G ‘ (succ k)) = succ (stateTarget (G ‘ k))) :
    ∀ n φ, φ ∈ formulaSet L Γ n → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ ∈ formulaSet L Δ (stateTarget (G ‘ k)) := by
  apply formulaSet_induction hL Γ (fun n φ ↦ ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ ∈ formulaSet L Δ (stateTarget (G ‘ k))) (by definability)
  · intro n hn
    constructor
    · intro k hk _
      rw [formulaSubstitutionGraph_truth hL hn hk]
      exact (formulaSet_constants hL (hG k hk).2.1 Δ).1
    · intro k hk _
      rw [formulaSubstitutionGraph_falsity hL hn hk]
      exact (formulaSet_constants hL (hG k hk).2.1 Δ).2
  · intro n hn r args ha
    have hv : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        IsAtomicArguments L Δ (stateTarget (G ‘ k)) r
          (compose args (termSubstitution L Γ n (stateBound (G ‘ k)) (stateFree (G ‘ k)))) := by
      intro k hk hctx
      exact atomicArguments_substituted hL hn (hG k hk).2.1
        (hctx.symm ▸ (hG k hk).2.2.1) (hG k hk).2.2.2 ha
    constructor
    · intro k hk hctx
      rw [formulaSubstitutionGraph_atom hL hn hk ha]
      exact (formulaSet_atoms hL (hG k hk).2.1 (hv k hk hctx)).1
    · intro k hk hctx
      rw [formulaSubstitutionGraph_negAtom hL hn hk ha]
      exact (formulaSet_atoms hL (hG k hk).2.1 (hv k hk hctx)).2
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro k hk hctx
      rw [formulaSubstitutionGraph_and hL hn hk hφ hψ]
      exact (formulaSet_binary hL (hG k hk).2.1 (ihφ k hk hctx) (ihψ k hk hctx)).1
    · intro k hk hctx
      rw [formulaSubstitutionGraph_or hL hn hk hφ hψ]
      exact (formulaSet_binary hL (hG k hk).2.1 (ihφ k hk hctx) (ihψ k hk hctx)).2
  · intro n hn φ hφ ih
    have hv : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ ∈
          formulaSet L Δ (succ (stateTarget (G ‘ k))) := by
      intro k hk hctx
      have hc : succ n = stateSource (G ‘ (succ k)) := by rw [hsource k hk, hctx]
      simpa only [htarget k hk] using ih (succ k) (ω_succ_closed hk) hc
    constructor
    · intro k hk hctx
      rw [formulaSubstitutionGraph_all hL hn hk hφ]
      exact (formulaSet_quantifiers hL (hG k hk).2.1 (hv k hk hctx)).1
    · intro k hk hctx
      rw [formulaSubstitutionGraph_exists hL hn hk hφ]
      exact (formulaSet_quantifiers hL (hG k hk).2.1 (hv k hk hctx)).2

theorem substituteFormula_mem {L Γ Δ s φ : V} (hL : IsLanguageCode L)
    (hs : IsSubstitutionState L Γ Δ s) (hφ : φ ∈ formulaSet L Γ (stateSource s)) :
    substituteFormula L Γ Δ s φ ∈ formulaSet L Δ (stateTarget s) := by
  have h := formulaSubstitutionGraph_valid (G := substitutionStates L Δ s) hL
    (fun k hk ↦ substitutionStates_valid hL hs hk)
    (fun k hk ↦ by rw [substitutionStates_succ _ _ _ hk]; simp [liftSubstitutionState])
    (fun k hk ↦ by rw [substitutionStates_succ _ _ _ hk]; simp [liftSubstitutionState])
    (stateSource s) φ hφ (0 : V) (by simp) (by rw [substitutionStates_zero])
  simpa only [substitutionStates_zero, substituteFormula] using h

end ZFVP
