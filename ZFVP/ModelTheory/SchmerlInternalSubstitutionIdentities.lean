import ZFVP.ModelTheory.SchmerlInternalSubstitution
import ZFVP.ModelTheory.SchmerlInternalQuantifierAxioms
import ZFVP.Syntax.FormulaSubstitutionComposition

/-! Syntactic substitution identities for internal infinitary codes. The
induction includes every internal binder depth and conjunction index. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem infinitarySubstitutionGraph_identity {L F G : V} (hF : IsFragment L F)
    (hsource : ∀ k ∈ (ω : V), stateSource (G ‘ (succ k)) = succ (stateSource (G ‘ k)))
    (hterms : ∀ k ∈ (ω : V),
      termSubstitution L ∅ (stateSource (G ‘ k)) (stateBound (G ‘ k)) (stateFree (G ‘ k)) =
        SetTheory.identity (termSet L ∅ (stateSource (G ‘ k)))) :
    ∀ n φ, ⟨n, φ⟩ₖ ∈ F → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ = φ := by
  apply fragment_induction hF (fun n φ ↦ ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
    (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ = φ) (by definability)
  · intro n φ ht hφ k hk hc
    rw [infinitarySubstitutionGraph_fo ht hk,
      formulaSubstitutionGraph_identity hF.1 hsource hterms n φ hφ k hk hc]
  · intro n φ ht _ ih k hk hc
    rw [infinitarySubstitutionGraph_neg hF ht hk, ih k hk hc]
  · intro n f ht hf hd _ ih k hk hc
    rw [infinitarySubstitutionGraph_conj hF ht hk]
    apply congrArg conjCode
    let := hf
    apply functions_eq_of_domain_values (by simp only [domain_transformConjunction, hd])
    intro i hi
    rw [domain_transformConjunction] at hi
    rw [value_transformConjunction _ _ _ hi]
    simpa only [substitutionChild, kpair.π₁_kpair, kpair.π₂_kpair] using ih i hi k hk hc
  · intro n φ ht _ ih k hk hc
    rw [infinitarySubstitutionGraph_exs hF ht hk,
      ih (succ k) (ω_succ_closed hk) (by rw [hsource k hk, hc])]
  · intro n φ ht _ ih k hk hc
    rw [infinitarySubstitutionGraph_q hF ht hk,
      ih (succ k) (ω_succ_closed hk) (by rw [hsource k hk, hc])]

theorem infinitarySubstitutionGraph_fragment_eq {L F H G : V}
    (hF : IsFragment L F) (hH : IsFragment L H) :
    ∀ n φ, ⟨n, φ⟩ₖ ∈ F → ⟨n, φ⟩ₖ ∈ H → ∀ k ∈ (ω : V),
      (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ =
        (infinitarySubstitutionGraph L H G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ := by
  apply fragment_induction hF (fun n φ ↦ ⟨n, φ⟩ₖ ∈ H → ∀ k ∈ (ω : V),
    (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ =
      (infinitarySubstitutionGraph L H G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) (by definability)
  · intro n φ ht _ hu k hk
    rw [infinitarySubstitutionGraph_fo ht hk, infinitarySubstitutionGraph_fo hu hk]
  · intro n φ ht _ ih hu k hk
    rw [infinitarySubstitutionGraph_neg hF ht hk, infinitarySubstitutionGraph_neg hH hu hk,
      ih (hH.neg_mem hu) k hk]
  · intro n f ht _ _ _ ih hu k hk
    rw [infinitarySubstitutionGraph_conj hF ht hk, infinitarySubstitutionGraph_conj hH hu hk]
    apply congrArg conjCode
    apply functions_eq_of_domain_values (by simp only [domain_transformConjunction])
    intro i hi
    rw [domain_transformConjunction] at hi
    rw [value_transformConjunction _ _ _ hi, value_transformConjunction _ _ _ hi]
    simpa only [substitutionChild, kpair.π₁_kpair, kpair.π₂_kpair] using
      ih i hi ((hH.conj_data hu).2.2 i hi) k hk
  · intro n φ ht _ ih hu k hk
    rw [infinitarySubstitutionGraph_exs hF ht hk, infinitarySubstitutionGraph_exs hH hu hk,
      ih (hH.exs_mem hu) (succ k) (ω_succ_closed hk)]
  · intro n φ ht _ ih hu k hk
    rw [infinitarySubstitutionGraph_q hF ht hk, infinitarySubstitutionGraph_q hH hu hk,
      ih (hH.q_mem hu) (succ k) (ω_succ_closed hk)]

theorem substituteCode_fragment_eq {L F H s φ : V} (hF : IsFragment L F) (hH : IsFragment L H)
    (hφF : ⟨stateSource s, φ⟩ₖ ∈ F) (hφH : ⟨stateSource s, φ⟩ₖ ∈ H) :
    substituteCode L F s φ = substituteCode L H s φ :=
  infinitarySubstitutionGraph_fragment_eq hF hH _ _ hφF hφH 0 (by simp)

end ZFVP.Infinitary.Internal
