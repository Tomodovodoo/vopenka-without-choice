import ZFVP.ModelTheory.NormalizedSelectedUnionInclusion
import ZFVP.ModelTheory.ForcingSemanticConsequence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStep_order_of_tail_inclusion_of_names [Countable V] {P R one Q S t p q σ τ : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one)
    (hQ : IsForcingName P Q) (hSN : IsForcingName P S)
    (hN : ∀ ν ∈ twoStepNames Q t, IsForcingName P ν)
    (hp : ⟨p, σ⟩ₖ ∈ twoStepConditions P R Q t)
    (hq : ⟨q, τ⟩ₖ ∈ twoStepConditions P R Q t) (hpq : ⟨p, q⟩ₖ ∈ R)
    (hval : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      let σ' : ForcingName P := ⟨σ, hN _ ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hp).2.1⟩
      let τ' : ForcingName P := ⟨τ, hN _ ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hq).2.1⟩
      A.ofName ⟨S, hSN⟩ = reverseInclusionOrder (A.ofName ⟨Q, hQ⟩) ∧
        A.ofName τ' ⊆ A.ofName σ') :
    ⟨⟨p, σ⟩ₖ, ⟨q, τ⟩ₖ⟩ₖ ∈ twoStepOrder P R Q S t := by
  obtain ⟨hpP, hσ, hpσ⟩ := (kpair_mem_twoStepConditions _ _ _ _ _ _).mp hp
  obtain ⟨hqP, hτ, hqτ⟩ := (kpair_mem_twoStepConditions _ _ _ _ _ _).mp hq
  refine (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr ⟨hp, hq, ?_, ?_⟩
  · simpa only [kpair.π₁_kpair] using hpq
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  let σ' : ForcingName P := ⟨σ, hN _ hσ⟩
  let τ' : ForcingName P := ⟨τ, hN _ hτ⟩
  apply forcingFormula_of_all_generics hR ho hpP boundedPairMemberFormula ![⟨S, hSN⟩, σ', τ']
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
  have hqG : q ∈ G := hG.1.2.2.1 p hpG q hqP hpq
  have hs : A.ofName σ' ∈ A.ofName ⟨Q, hQ⟩ :=
    (forcingQuotientMk_mem_iff _ _ _ _ _ _ _).mpr ⟨p, hpG, hpσ⟩
  have ht : A.ofName τ' ∈ A.ofName ⟨Q, hQ⟩ :=
    (forcingQuotientMk_mem_iff _ _ _ _ _ _ _).mpr ⟨q, hqG, hqτ⟩
  obtain ⟨hS, hsub⟩ := hval G hG hpG
  have hpair : ⟨A.ofName σ', A.ofName τ'⟩ₖ ∈ A.ofName ⟨S, hSN⟩ := by
    rw [hS]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hs, ht, hsub⟩
  simpa using hpair

theorem twoStep_order_of_tail_inclusion [Countable V] {P R one Q S t p q σ τ : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t)
    (hp : ⟨p, σ⟩ₖ ∈ twoStepConditions P R Q t)
    (hq : ⟨q, τ⟩ₖ ∈ twoStepConditions P R Q t) (hpq : ⟨p, q⟩ₖ ∈ R)
    (hval : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      let σ' : ForcingName P := ⟨σ, h.name ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hp).2.1⟩
      let τ' : ForcingName P := ⟨τ, h.name ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hq).2.1⟩
      A.ofName ⟨S, h.orderName⟩ = reverseInclusionOrder (A.ofName ⟨Q, h.posetName⟩) ∧
        A.ofName τ' ⊆ A.ofName σ') :
    ⟨⟨p, σ⟩ₖ, ⟨q, τ⟩ₖ⟩ₖ ∈ twoStepOrder P R Q S t :=
  twoStep_order_of_tail_inclusion_of_names hR ho h.posetName h.orderName
    (fun _ hν ↦ h.name hν) hp hq hpq hval

end ZFVP
