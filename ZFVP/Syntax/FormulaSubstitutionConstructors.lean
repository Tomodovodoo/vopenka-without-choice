import ZFVP.Syntax.FormulaSubstitutionComposition

/-! Constructor equations for substitution, including the binder-lifted state. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem formulaSubstitutionGraph_depthShift {L Γ G H : V} (hL : IsLanguageCode L)
    (hshift : ∀ k ∈ (ω : V), G ‘ (succ k) = H ‘ k) :
    ∀ n φ, φ ∈ formulaSet L Γ n → ∀ k ∈ (ω : V),
      (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, succ k⟩ₖ =
        (formulaSubstitutionGraph L Γ H) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ := by
  apply formulaSet_induction hL Γ (fun n φ ↦ ∀ k ∈ (ω : V),
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, succ k⟩ₖ =
      (formulaSubstitutionGraph L Γ H) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) (by definability)
  · intro n hn
    constructor
    · intro k hk
      rw [formulaSubstitutionGraph_truth hL hn (ω_succ_closed hk), formulaSubstitutionGraph_truth hL hn hk]
    · intro k hk
      rw [formulaSubstitutionGraph_falsity hL hn (ω_succ_closed hk), formulaSubstitutionGraph_falsity hL hn hk]
  · intro n hn r args ha
    constructor
    · intro k hk
      rw [formulaSubstitutionGraph_atom hL hn (ω_succ_closed hk) ha,
        formulaSubstitutionGraph_atom hL hn hk ha, hshift k hk]
    · intro k hk
      rw [formulaSubstitutionGraph_negAtom hL hn (ω_succ_closed hk) ha,
        formulaSubstitutionGraph_negAtom hL hn hk ha, hshift k hk]
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro k hk
      rw [formulaSubstitutionGraph_and hL hn (ω_succ_closed hk) hφ hψ,
        formulaSubstitutionGraph_and hL hn hk hφ hψ, ihφ k hk, ihψ k hk]
    · intro k hk
      rw [formulaSubstitutionGraph_or hL hn (ω_succ_closed hk) hφ hψ,
        formulaSubstitutionGraph_or hL hn hk hφ hψ, ihφ k hk, ihψ k hk]
  · intro n hn φ hφ ih
    constructor
    · intro k hk
      rw [formulaSubstitutionGraph_all hL hn (ω_succ_closed hk) hφ,
        formulaSubstitutionGraph_all hL hn hk hφ, ih (succ k) (ω_succ_closed hk)]
    · intro k hk
      rw [formulaSubstitutionGraph_exists hL hn (ω_succ_closed hk) hφ,
        formulaSubstitutionGraph_exists hL hn hk hφ, ih (succ k) (ω_succ_closed hk)]

theorem substitutionStates_shift (L Δ s : V) {k : V} (hk : k ∈ (ω : V)) :
    (substitutionStates L Δ s) ‘ (succ k) =
      (substitutionStates L Δ (liftSubstitutionState L Δ s)) ‘ k := by
  apply naturalNumber_induction (fun k ↦ (substitutionStates L Δ s) ‘ (succ k) =
    (substitutionStates L Δ (liftSubstitutionState L Δ s)) ‘ k) (by definability) ?_ ?_ k hk
  · rw [substitutionStates_succ _ _ _ (by simp), substitutionStates_zero, substitutionStates_zero]
  · intro k hk ih
    rw [substitutionStates_succ _ _ _ (ω_succ_closed hk), ih, substitutionStates_succ _ _ _ hk]

theorem substituteFormula_and {L Γ Δ s φ ψ : V} (hL : IsLanguageCode L)
    (hφ : φ ∈ formulaSet L Γ (stateSource s)) (hψ : ψ ∈ formulaSet L Γ (stateSource s)) :
    substituteFormula L Γ Δ s (andCode φ ψ) =
      andCode (substituteFormula L Γ Δ s φ) (substituteFormula L Γ Δ s ψ) :=
  formulaSubstitutionGraph_and hL (formulaSet_context hL hφ) (by simp) hφ hψ _

theorem substituteFormula_or {L Γ Δ s φ ψ : V} (hL : IsLanguageCode L)
    (hφ : φ ∈ formulaSet L Γ (stateSource s)) (hψ : ψ ∈ formulaSet L Γ (stateSource s)) :
    substituteFormula L Γ Δ s (orCode φ ψ) =
      orCode (substituteFormula L Γ Δ s φ) (substituteFormula L Γ Δ s ψ) :=
  formulaSubstitutionGraph_or hL (formulaSet_context hL hφ) (by simp) hφ hψ _

theorem substituteFormula_all {L Γ Δ s φ : V} (hL : IsLanguageCode L)
    (hn : stateSource s ∈ (ω : V)) (hφ : φ ∈ formulaSet L Γ (succ (stateSource s))) :
    substituteFormula L Γ Δ s (allCode φ) =
      allCode (substituteFormula L Γ Δ (liftSubstitutionState L Δ s) φ) := by
  have he := formulaSubstitutionGraph_depthShift (Γ := Γ) hL
    (fun k hk ↦ substitutionStates_shift L Δ s hk) _ φ hφ (0 : V) (by simp)
  unfold substituteFormula
  rw [formulaSubstitutionGraph_all hL hn (show (0 : V) ∈ (ω : V) by simp) hφ]
  simpa only [liftSubstitutionState, stateSource_code] using congrArg allCode he

theorem substituteFormula_exists {L Γ Δ s φ : V} (hL : IsLanguageCode L)
    (hn : stateSource s ∈ (ω : V)) (hφ : φ ∈ formulaSet L Γ (succ (stateSource s))) :
    substituteFormula L Γ Δ s (existsCode φ) =
      existsCode (substituteFormula L Γ Δ (liftSubstitutionState L Δ s) φ) := by
  have he := formulaSubstitutionGraph_depthShift (Γ := Γ) hL
    (fun k hk ↦ substitutionStates_shift L Δ s hk) _ φ hφ (0 : V) (by simp)
  unfold substituteFormula
  rw [formulaSubstitutionGraph_exists hL hn (show (0 : V) ∈ (ω : V) by simp) hφ]
  simpa only [liftSubstitutionState, stateSource_code] using congrArg existsCode he

end ZFVP
