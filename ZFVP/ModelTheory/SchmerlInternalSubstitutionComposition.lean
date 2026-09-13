import ZFVP.ModelTheory.SchmerlInternalSubstitutionIdentities

/-! Composition on actual internal infinitary syntax. The term-table identity
is propagated through all internal conjunction indices and binder depths. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem infinitarySubstitutionGraph_compose {L F G H J : V} (hF : IsFragment L F)
    (hG : ∀ k ∈ (ω : V), IsSubstitutionState L ∅ ∅ (G ‘ k))
    (hsource : ∀ k ∈ (ω : V), stateSource (G ‘ (succ k)) = succ (stateSource (G ‘ k)))
    (htarget : ∀ k ∈ (ω : V), stateTarget (G ‘ (succ k)) = succ (stateTarget (G ‘ k)))
    (hterms : ∀ k ∈ (ω : V),
      compose (termSubstitution L ∅ (stateSource (G ‘ k)) (stateBound (G ‘ k)) (stateFree (G ‘ k)))
        (termSubstitution L ∅ (stateTarget (G ‘ k)) (stateBound (H ‘ k)) (stateFree (H ‘ k))) =
      termSubstitution L ∅ (stateSource (G ‘ k)) (stateBound (J ‘ k)) (stateFree (J ‘ k))) :
    ∀ n φ, ⟨n, φ⟩ₖ ∈ F → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      (infinitarySubstitutionGraph L (substitutedFragment L F G) H) ‘
        ⟨⟨stateTarget (G ‘ k), (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ⟩ₖ, k⟩ₖ =
      (infinitarySubstitutionGraph L F J) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ := by
  have hS := substitutedFragment_valid hF hG hsource htarget
  apply fragment_induction hF (fun n φ ↦ ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      (infinitarySubstitutionGraph L (substitutedFragment L F G) H) ‘
        ⟨⟨stateTarget (G ‘ k), (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ⟩ₖ, k⟩ₖ =
      (infinitarySubstitutionGraph L F J) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) (by definability)
  · intro n φ ht hφ k hk hc
    have hu := substitutedNode_mem (L := L) (G := G) ht hk hc
    rw [infinitarySubstitutionGraph_fo ht hk] at hu
    rw [infinitarySubstitutionGraph_fo (G := G) ht hk,
      infinitarySubstitutionGraph_fo hu hk, infinitarySubstitutionGraph_fo (G := J) ht hk,
      formulaSubstitutionGraph_compose hF.1 hG hsource htarget hterms n φ hφ k hk hc]
  · intro n φ ht _ ih k hk hc
    have hu := substitutedNode_mem (L := L) (G := G) ht hk hc
    rw [infinitarySubstitutionGraph_neg hF ht hk] at hu
    rw [infinitarySubstitutionGraph_neg (G := G) hF ht hk,
      infinitarySubstitutionGraph_neg hS hu hk, infinitarySubstitutionGraph_neg (G := J) hF ht hk,
      ih k hk hc]
  · intro n f ht _ _ _ ih k hk hc
    have hu := substitutedNode_mem (L := L) (G := G) ht hk hc
    rw [infinitarySubstitutionGraph_conj hF ht hk] at hu
    rw [infinitarySubstitutionGraph_conj (G := G) hF ht hk,
      infinitarySubstitutionGraph_conj hS hu hk, infinitarySubstitutionGraph_conj (G := J) hF ht hk]
    apply congrArg conjCode
    apply functions_eq_of_domain_values (by simp only [domain_transformConjunction])
    intro i hi
    rw [domain_transformConjunction] at hi
    rw [value_transformConjunction _ _ _ hi, value_transformConjunction _ _ _ hi,
      value_transformConjunction _ _ _ hi]
    simpa only [substitutionChild, kpair.π₁_kpair, kpair.π₂_kpair] using ih i hi k hk hc
  · intro n φ ht _ ih k hk hc
    have hu := substitutedNode_mem (L := L) (G := G) ht hk hc
    rw [infinitarySubstitutionGraph_exs hF ht hk] at hu
    rw [infinitarySubstitutionGraph_exs (G := G) hF ht hk,
      infinitarySubstitutionGraph_exs hS hu hk, infinitarySubstitutionGraph_exs (G := J) hF ht hk]
    rw [← htarget k hk]
    exact congrArg exsCode (ih (succ k) (ω_succ_closed hk) (by rw [hsource k hk, hc]))
  · intro n φ ht _ ih k hk hc
    have hu := substitutedNode_mem (L := L) (G := G) ht hk hc
    rw [infinitarySubstitutionGraph_q hF ht hk] at hu
    rw [infinitarySubstitutionGraph_q (G := G) hF ht hk,
      infinitarySubstitutionGraph_q hS hu hk, infinitarySubstitutionGraph_q (G := J) hF ht hk]
    rw [← htarget k hk]
    exact congrArg qCode (ih (succ k) (ω_succ_closed hk) (by rw [hsource k hk, hc]))

end ZFVP.Infinitary.Internal
