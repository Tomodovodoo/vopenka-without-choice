import ZFVP.ModelTheory.WoodinStageRule
import ZFVP.ModelTheory.WoodinQuotientClosureInverse
import ZFVP.ModelTheory.WoodinQuotientClosureSuccessor
import ZFVP.ModelTheory.WoodinQuotientClosureDirect

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinStageRule_quotient_closure {δ θ s K : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h : IsWoodinIteration δ θ s K)
    (hc : HasWoodinQuotientClosure θ s K)
    (hinverse : θ ≠ ∅ → (∀ i ∈ θ, succ i ∈ θ) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal K) →
      ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ s) i θ (K ‘ i)) :
    HasWoodinQuotientClosure (succ θ) (kpair.π₁ (woodinStageRule θ s K))
      (kpair.π₂ (woodinStageRule θ s K)) := by
  classical
  by_cases hzero : θ = ∅
  · subst θ
    simpa only [woodinStageRule_initial, kpair.π₁_kpair, kpair.π₂_kpair] using (woodinInitialCode_iteration hδ).code.initial_quotient_closure woodinInitialCardinals
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · have hk : ⋃ˢ θ ∈ θ :=
      (congrArg (fun x : V ↦ (⋃ˢ θ) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ θ))
    let := IsOrdinal.of_mem hk
    have hh : IsWoodinIteration δ (succ (⋃ˢ θ)) s K := hsucc ▸ h
    have he : woodinStageRule θ s K =
        ⟨woodinIterationSuccessor (⋃ˢ θ) s K, woodinIterationCardinalNext (⋃ˢ θ) s K⟩ₖ := by
      simp only [woodinStageRule, ite_eq_right hzero, ite_eq_left hsucc]
    rw [he]
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair, ← hsucc] using (hsucc ▸ hc : HasWoodinQuotientClosure (succ (⋃ˢ θ)) s K).successor hδ hh
  have hlim := ordinal_limit_of_not_successor hsucc
  have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left
    (fun he ↦ hzero he.symm)
  by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal K)
  · simp only [woodinStageRule, ite_eq_right hzero, ite_eq_right hsucc, ite_eq_left hinac,
      kpair.π₁_kpair, kpair.π₂_kpair]
    exact hc.direct h hlim hinac h0
  · simp only [woodinStageRule, ite_eq_right hzero, ite_eq_right hsucc, ite_eq_right hinac,
      kpair.π₁_kpair, kpair.π₂_kpair]
    exact hc.inverse_source_of_raw_closure h hδ hθ h0 hlim hinac (hinverse hzero hlim hinac)

end ZFVP
