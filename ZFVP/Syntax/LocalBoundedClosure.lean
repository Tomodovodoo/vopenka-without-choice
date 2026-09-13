import ZFVP.Syntax.BoundedCertificateCases

/-! Bounded formula codes are minimal among families closed inside a coding support. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLocallyBoundedClosed (U Q : V) : Prop := ∀ q ∈ U, BoundedDerivationStep Q q → q ∈ Q

instance isLocallyBoundedClosed_definable : ℒₛₑₜ-relation[V] IsLocallyBoundedClosed := by
  unfold IsLocallyBoundedClosed
  definability

theorem IsBoundedFormulaClosed.locally {Q : V} (hQ : IsBoundedFormulaClosed Q) (U : V) :
    IsLocallyBoundedClosed U Q := fun _ _ h ↦ boundedDerivationStep_closed hQ (fun _ h ↦ h) h

theorem boundedQuantifier_body_mem {U i φ : V} [IsTransitive U]
    (h : boundedAllCode i φ ∈ U ∨ boundedExistsCode i φ ∈ U) : φ ∈ U := by
  rcases h with h | h
  · exact (binaryCode_parameters_mem (kpair_components_mem_transitive h).2).2
  · exact (binaryCode_parameters_mem (kpair_components_mem_transitive h).2).2

theorem boundedFormulaFamily_local_minimal {U Q : V} [hU : IsCodingSupport U]
    (hQ : IsLocallyBoundedClosed U Q) : ∀ q ∈ (boundedFormulaFamily : V), q ∈ U → q ∈ Q := by
  refine boundedFormulaFamily_induction (fun q : V ↦ q ∈ U → q ∈ Q) (by definability) ?_ ?_ ?_ ?_
  · intro n hn
    exact ⟨fun hq ↦ hQ _ hq ⟨n, hn, truthCode, rfl, Or.inl rfl⟩,
      fun hq ↦ hQ _ hq ⟨n, hn, falsityCode, rfl, Or.inr (Or.inl rfl)⟩⟩
  · intro n hn r args ha
    have ha' := (membershipAtomicArguments_iff hn).mp ha
    exact ⟨fun hq ↦ hQ _ hq ⟨n, hn, atomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inl rfl⟩))⟩,
      fun hq ↦ hQ _ hq ⟨n, hn, negAtomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inr rfl⟩))⟩⟩
  · intro n hn φ ψ _ _ ihφ ihψ
    have hm {t : V} (hq : ⟨n, ⟨t, ⟨φ, ψ⟩ₖ⟩ₖ⟩ₖ ∈ U) : ⟨n, φ⟩ₖ ∈ Q ∧ ⟨n, ψ⟩ₖ ∈ Q := by
      obtain ⟨hφ, hψ⟩ := binaryCode_parameters_mem (kpair_components_mem_transitive hq).2
      exact ⟨ihφ (hU.kpair_closed _ (IsCodingSupport.natural_mem hn) _ hφ),
        ihψ (hU.kpair_closed _ (IsCodingSupport.natural_mem hn) _ hψ)⟩
    exact ⟨fun hq ↦ hQ _ hq ⟨n, hn, andCode φ ψ, rfl,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, (hm hq).1, (hm hq).2, Or.inl rfl⟩)))⟩,
      fun hq ↦ hQ _ hq ⟨n, hn, orCode φ ψ, rfl,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, (hm hq).1, (hm hq).2, Or.inr rfl⟩)))⟩⟩
  · intro n hn i hi φ _ ih
    have hm {θ : V} (hq : ⟨n, θ⟩ₖ ∈ U) (hθ : θ = boundedAllCode i φ ∨ θ = boundedExistsCode i φ) :
        ⟨succ n, φ⟩ₖ ∈ Q := by
      have hθU := (kpair_components_mem_transitive hq).2
      have hφ := boundedQuantifier_body_mem (hθ.elim (fun h ↦ Or.inl (h ▸ hθU)) (fun h ↦ Or.inr (h ▸ hθU)))
      exact ih (hU.kpair_closed _ (IsCodingSupport.natural_mem (ω_succ_closed hn)) _ hφ)
    exact ⟨fun hq ↦ hQ _ hq ⟨n, hn, boundedAllCode i φ, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, φ, hm hq (Or.inl rfl), Or.inl rfl⟩)))⟩,
      fun hq ↦ hQ _ hq ⟨n, hn, boundedExistsCode i φ, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, φ, hm hq (Or.inr rfl), Or.inr rfl⟩)))⟩⟩

end ZFVP
