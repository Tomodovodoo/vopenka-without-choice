import ZFVP.Syntax.FormulaSubstitutionNegation
import ZFVP.Syntax.SubstitutionExtensionality

/-! Composition and identity for substitution graphs, using the corresponding
identities on the term replacement tables at every binder depth. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem formulaSubstitutionGraph_compose {L Γ Δ G H J : V} (hL : IsLanguageCode L)
    (hG : ∀ k ∈ (ω : V), IsSubstitutionState L Γ Δ (G ‘ k))
    (hsource : ∀ k ∈ (ω : V), stateSource (G ‘ (succ k)) = succ (stateSource (G ‘ k)))
    (htarget : ∀ k ∈ (ω : V), stateTarget (G ‘ (succ k)) = succ (stateTarget (G ‘ k)))
    (hterms : ∀ k ∈ (ω : V),
      compose (termSubstitution L Γ (stateSource (G ‘ k)) (stateBound (G ‘ k)) (stateFree (G ‘ k)))
        (termSubstitution L Δ (stateTarget (G ‘ k)) (stateBound (H ‘ k)) (stateFree (H ‘ k))) =
      termSubstitution L Γ (stateSource (G ‘ k)) (stateBound (J ‘ k)) (stateFree (J ‘ k))) :
    ∀ n φ, φ ∈ formulaSet L Γ n → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      (formulaSubstitutionGraph L Δ H) ‘
        ⟨⟨stateTarget (G ‘ k), (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ⟩ₖ, k⟩ₖ =
      (formulaSubstitutionGraph L Γ J) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ := by
  have hv := formulaSubstitutionGraph_valid hL hG hsource htarget
  apply formulaSet_induction hL Γ (fun n φ ↦ ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
    (formulaSubstitutionGraph L Δ H) ‘
      ⟨⟨stateTarget (G ‘ k), (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ⟩ₖ, k⟩ₖ =
    (formulaSubstitutionGraph L Γ J) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) (by definability)
  · intro n hn
    constructor
    · intro k hk _
      rw [formulaSubstitutionGraph_truth hL hn hk, formulaSubstitutionGraph_truth hL (hG k hk).2.1 hk,
        formulaSubstitutionGraph_truth hL hn hk]
    · intro k hk _
      rw [formulaSubstitutionGraph_falsity hL hn hk, formulaSubstitutionGraph_falsity hL (hG k hk).2.1 hk,
        formulaSubstitutionGraph_falsity hL hn hk]
  · intro n hn r args ha
    have hat : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        IsAtomicArguments L Δ (stateTarget (G ‘ k)) r
          (compose args (termSubstitution L Γ n (stateBound (G ‘ k)) (stateFree (G ‘ k)))) := by
      intro k hk he
      exact atomicArguments_substituted hL hn (hG k hk).2.1
        (he.symm ▸ (hG k hk).2.2.1) (hG k hk).2.2.2 ha
    constructor
    · intro k hk he
      rw [formulaSubstitutionGraph_atom hL hn hk ha,
        formulaSubstitutionGraph_atom hL (hG k hk).2.1 hk (hat k hk he),
        formulaSubstitutionGraph_atom hL hn hk ha, graph_compose_assoc, he, hterms k hk]
    · intro k hk he
      rw [formulaSubstitutionGraph_negAtom hL hn hk ha,
        formulaSubstitutionGraph_negAtom hL (hG k hk).2.1 hk (hat k hk he),
        formulaSubstitutionGraph_negAtom hL hn hk ha, graph_compose_assoc, he, hterms k hk]
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro k hk he
      rw [formulaSubstitutionGraph_and hL hn hk hφ hψ,
        formulaSubstitutionGraph_and hL (hG k hk).2.1 hk (hv _ _ hφ k hk he) (hv _ _ hψ k hk he),
        formulaSubstitutionGraph_and hL hn hk hφ hψ, ihφ k hk he, ihψ k hk he]
    · intro k hk he
      rw [formulaSubstitutionGraph_or hL hn hk hφ hψ,
        formulaSubstitutionGraph_or hL (hG k hk).2.1 hk (hv _ _ hφ k hk he) (hv _ _ hψ k hk he),
        formulaSubstitutionGraph_or hL hn hk hφ hψ, ihφ k hk he, ihψ k hk he]
  · intro n hn φ hφ ih
    have he' : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        succ n = stateSource (G ‘ (succ k)) := by
      intro k hk he
      rw [hsource k hk, he]
    have hv' : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ ∈
          formulaSet L Δ (succ (stateTarget (G ‘ k))) := by
      intro k hk he
      simpa only [htarget k hk] using hv _ _ hφ (succ k) (ω_succ_closed hk) (he' k hk he)
    constructor
    · intro k hk he
      rw [formulaSubstitutionGraph_all hL hn hk hφ,
        formulaSubstitutionGraph_all hL (hG k hk).2.1 hk (hv' k hk he),
        formulaSubstitutionGraph_all hL hn hk hφ, ← htarget k hk,
        ih (succ k) (ω_succ_closed hk) (he' k hk he)]
    · intro k hk he
      rw [formulaSubstitutionGraph_exists hL hn hk hφ,
        formulaSubstitutionGraph_exists hL (hG k hk).2.1 hk (hv' k hk he),
        formulaSubstitutionGraph_exists hL hn hk hφ, ← htarget k hk,
        ih (succ k) (ω_succ_closed hk) (he' k hk he)]

theorem formulaSubstitutionGraph_identity {L Γ G : V} (hL : IsLanguageCode L)
    (hsource : ∀ k ∈ (ω : V), stateSource (G ‘ (succ k)) = succ (stateSource (G ‘ k)))
    (hterms : ∀ k ∈ (ω : V),
      termSubstitution L Γ (stateSource (G ‘ k)) (stateBound (G ‘ k)) (stateFree (G ‘ k)) =
        SetTheory.identity (termSet L Γ (stateSource (G ‘ k)))) :
    ∀ n φ, φ ∈ formulaSet L Γ n → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ = φ := by
  apply formulaSet_induction hL Γ (fun n φ ↦ ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ = φ) (by definability)
  · intro n hn
    exact ⟨fun k hk _ ↦ formulaSubstitutionGraph_truth hL hn hk Γ G,
      fun k hk _ ↦ formulaSubstitutionGraph_falsity hL hn hk Γ G⟩
  · intro n hn r args ha
    have hargs : ∃ a : V, args ∈ (termSet L Γ n) ^ a := by
      rcases ha with ⟨_, ha⟩ | ⟨s, hs, _, ha⟩
      · exact ⟨2, ha⟩
      · exact ⟨_, ha⟩
    obtain ⟨a, hargs⟩ := hargs
    constructor
    · intro k hk he
      rw [formulaSubstitutionGraph_atom hL hn hk ha, he, hterms k hk,
        graph_compose_identity (he ▸ hargs)]
    · intro k hk he
      rw [formulaSubstitutionGraph_negAtom hL hn hk ha, he, hterms k hk,
        graph_compose_identity (he ▸ hargs)]
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro k hk he
      rw [formulaSubstitutionGraph_and hL hn hk hφ hψ, ihφ k hk he, ihψ k hk he]
    · intro k hk he
      rw [formulaSubstitutionGraph_or hL hn hk hφ hψ, ihφ k hk he, ihψ k hk he]
  · intro n hn φ hφ ih
    have he' : ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
        succ n = stateSource (G ‘ (succ k)) := by
      intro k hk he
      rw [hsource k hk, he]
    constructor
    · intro k hk he
      rw [formulaSubstitutionGraph_all hL hn hk hφ, ih (succ k) (ω_succ_closed hk) (he' k hk he)]
    · intro k hk he
      rw [formulaSubstitutionGraph_exists hL hn hk hφ, ih (succ k) (ω_succ_closed hk) (he' k hk he)]

end ZFVP
