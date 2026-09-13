import ZFVP.Syntax.FormulaSubstitutionDefinability
import ZFVP.Syntax.FormulaSubstitutionEquations
import ZFVP.SetTheory.FunctionUnion

/-! Substitution depends only on the variable-table values used by the source context. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem termSubstitution_eq_of_values {L Γ n B E B' E' : V}
    (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hB : ∀ i ∈ n, B ‘ i = B' ‘ i) (hE : ∀ x ∈ Γ, E ‘ x = E' ‘ x) :
    termSubstitution L Γ n B E = termSubstitution L Γ n B' E' := by
  apply functions_eq_of_domain_values (by simp)
  simp only [domain_termSubstitution]
  apply termSet_induction hL hn Γ (fun t ↦
    (termSubstitution L Γ n B E) ‘ t = (termSubstitution L Γ n B' E') ‘ t) (by definability)
  · intro i hi
    rw [termSubstitution_boundVar hL hn _ _ _ hi, termSubstitution_boundVar hL hn _ _ _ hi, hB i hi]
  · intro x hx
    rw [termSubstitution_freeVar hL hn _ _ _ hx, termSubstitution_freeVar hL hn _ _ _ hx, hE x hx]
  · intro f hf args ha ih
    have ht := (termSet_closed hL hn Γ).2.2 f hf args ha
    rw [termSubstitution_function hL hn _ _ _ ht, termSubstitution_function hL hn _ _ _ ht]
    apply congrArg (functionTermCode f)
    have hdom := range_subset_of_mem_function ha
    have he := restrict_eq_of_values (f := termSubstitution L Γ n B E)
      (g := termSubstitution L Γ n B' E') (A := range args)
      (by simpa only [domain_termSubstitution] using hdom)
      (by simpa only [domain_termSubstitution] using hdom) ih
    rw [← compose_restrict_range args (termSubstitution L Γ n B E), he, compose_restrict_range]

theorem formulaSubstitutionGraph_eq_of_tables {L Γ G H : V} (hL : IsLanguageCode L)
    (N : V → V) (hN : ℒₛₑₜ-function₁ N)
    (hstep : ∀ d ∈ (ω : V), N (succ d) = succ (N d))
    (hB : ∀ d ∈ (ω : V), ∀ i ∈ N d, (stateBound (G ‘ d)) ‘ i = (stateBound (H ‘ d)) ‘ i)
    (hE : ∀ d ∈ (ω : V), ∀ x ∈ Γ, (stateFree (G ‘ d)) ‘ x = (stateFree (H ‘ d)) ‘ x) :
    ∀ n φ, φ ∈ formulaSet L Γ n → ∀ d ∈ (ω : V), n = N d →
      (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, d⟩ₖ =
        (formulaSubstitutionGraph L Γ H) ‘ ⟨⟨n, φ⟩ₖ, d⟩ₖ := by
  apply formulaSet_induction hL Γ (fun n φ ↦ ∀ d ∈ (ω : V), n = N d →
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, d⟩ₖ =
      (formulaSubstitutionGraph L Γ H) ‘ ⟨⟨n, φ⟩ₖ, d⟩ₖ) (by definability)
  · intro n hn
    constructor
    · intro d hd _
      rw [formulaSubstitutionGraph_truth hL hn hd, formulaSubstitutionGraph_truth hL hn hd]
    · intro d hd _
      rw [formulaSubstitutionGraph_falsity hL hn hd, formulaSubstitutionGraph_falsity hL hn hd]
  · intro n hn r args ha
    have hterms {d : V} (hd : d ∈ (ω : V)) (he : n = N d) :
        termSubstitution L Γ n (stateBound (G ‘ d)) (stateFree (G ‘ d)) =
          termSubstitution L Γ n (stateBound (H ‘ d)) (stateFree (H ‘ d)) :=
      termSubstitution_eq_of_values hL hn (he.symm ▸ hB d hd) (hE d hd)
    constructor
    · intro d hd he
      rw [formulaSubstitutionGraph_atom hL hn hd ha, formulaSubstitutionGraph_atom hL hn hd ha, hterms hd he]
    · intro d hd he
      rw [formulaSubstitutionGraph_negAtom hL hn hd ha, formulaSubstitutionGraph_negAtom hL hn hd ha, hterms hd he]
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro d hd he
      rw [formulaSubstitutionGraph_and hL hn hd hφ hψ, formulaSubstitutionGraph_and hL hn hd hφ hψ,
        ihφ d hd he, ihψ d hd he]
    · intro d hd he
      rw [formulaSubstitutionGraph_or hL hn hd hφ hψ, formulaSubstitutionGraph_or hL hn hd hφ hψ,
        ihφ d hd he, ihψ d hd he]
  · intro n hn φ hφ ihφ
    have hctx {d : V} (hd : d ∈ (ω : V)) (he : n = N d) : succ n = N (succ d) := by
      rw [hstep d hd, he]
    constructor
    · intro d hd he
      rw [formulaSubstitutionGraph_all hL hn hd hφ, formulaSubstitutionGraph_all hL hn hd hφ,
        ihφ (succ d) (ω_succ_closed hd) (hctx hd he)]
    · intro d hd he
      rw [formulaSubstitutionGraph_exists hL hn hd hφ, formulaSubstitutionGraph_exists hL hn hd hφ,
        ihφ (succ d) (ω_succ_closed hd) (hctx hd he)]

end ZFVP
