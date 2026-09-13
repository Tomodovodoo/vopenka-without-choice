import ZFVP.SetTheory.ClassForcingBounded
import ZFVP.SetTheory.ForcingPowerName
import ZFVP.SetTheory.BoundedAtomicTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingSubsetConditions_iff_membership {P R σ τ p : V}
    (hR : IsForcingPreorder P R) (hσ : IsForcingName P σ) :
    p ∈ forcingSubsetConditions P R σ τ ↔ p ∈ P ∧
      ∀ u s, ⟨u, s⟩ₖ ∈ σ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R →
        q ∈ atomicMembership P R u τ := by
  have ht : forcingTermValue (.bvar 0) (standardTuple ![σ, τ]) = σ := value_standardTuple ![σ, τ] 0
  have hv (u : V) : (standardTuple ![u, σ, τ]) ‘ (0 : V) = u := value_standardTuple ![u, σ, τ] 0
  have hw (u : V) : (standardTuple ![u, σ, τ]) ‘ (2 : V) = τ := value_standardTuple ![u, σ, τ] 2
  have hh := classForcingFormula_boundedAll_iff hR (IsForcingName P) (by definability)
    (.bvar 0 : SetTheorySemiterm Empty 2)
    (.rel Language.Set.Rel.mem ![.bvar 0, .bvar 2]) ![σ, τ]
    (ht.symm ▸ hσ)
    (by intro u s hs; exact forcingName_subname hσ (ht ▸ hs)) p
  change p ∈ forcingSubsetConditions P R σ τ ↔ _ at hh
  rw [ht] at hh
  have he (u : V) : classForcingFormula P R (IsForcingName P) (by definability)
      (.rel Language.Set.Rel.mem ![.bvar 0, .bvar 2] : SetTheorySemisentence 3) (standardTuple (u :> ![σ, τ])) =
      atomicMembership P R u τ := by
    change atomicMembership P R ((standardTuple ![u, σ, τ]) ‘ (0 : V))
      ((standardTuple ![u, σ, τ]) ‘ (2 : V)) = _
    rw [hv, hw]
  simpa only [he] using hh

def AtomicSubsetTest (P R σ τ p : V) : Prop :=
  ∀ u s, ⟨u, s⟩ₖ ∈ σ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R →
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ∃ v t, ⟨v, t⟩ₖ ∈ τ ∧ ⟨r, t⟩ₖ ∈ R ∧
      r ∈ atomicEquality P R u v

theorem forcingSubsetConditions_iff_atomic {P R σ τ p : V}
    (hR : IsForcingPreorder P R) (hσ : IsForcingName P σ) :
    p ∈ forcingSubsetConditions P R σ τ ↔ p ∈ P ∧ AtomicSubsetTest P R σ τ p := by
  rw [forcingSubsetConditions_iff_membership hR hσ]
  apply and_congr_right
  intro hp
  constructor
  · intro h u s hs q hq hqp hqs
    exact ((mem_atomicMembership_iff _ _ _ _ _).mp (h u s hs q hq hqp hqs)).2 q hq (hR.2.1 q hq)
  · intro h u s hs q hq hqp hqs
    apply (mem_atomicMembership_iff _ _ _ _ _).mpr
    refine ⟨hq, ?_⟩
    intro r hr hrq
    exact h u s hs r hr (hR.2.2 r hr q hq p hp hrq hqp)
      (hR.2.2 r hr q hq s (forcingName_condition hσ hs) hrq hqs)

theorem eval_boundedEqualityLeftFormula_subset {T P R H σ τ p : V} [IsTransitive T]
    (hH : IsAtomicTruthTable P R T H) (hσ : σ ∈ T) (hτ : τ ∈ T) :
    boundedEqualityLeftFormula.Evalb ![T, P, R, H, σ, τ, p] ↔
      AtomicSubsetTest P R σ τ p := by
  simp only [boundedEqualityLeftFormula]
  simp
  constructor
  · intro h u s hs q hq hqp hqs
    obtain ⟨huT, hsT⟩ := subname_pair_components_mem_transitive hσ hs
    obtain ⟨r, hr, hrq, v, hvT, t, _, ht, hrt, he⟩ := h u huT s hsT hs q hq hqp hqs
    exact ⟨r, hr, hrq, v, t, ht, hrt,
      (hH.entry (transitive_subnameClosed inferInstance) huT hvT).mp ⟨hr, he⟩⟩
  · intro h u huT s _ hs q hq hqp hqs
    obtain ⟨r, hr, hrq, v, t, ht, hrt, he⟩ := h u s hs q hq hqp hqs
    obtain ⟨hvT, htT⟩ := subname_pair_components_mem_transitive hτ ht
    exact ⟨r, hr, hrq, v, hvT, t, htT, ht, hrt,
      ((hH.entry (transitive_subnameClosed inferInstance) huT hvT).mpr he).2⟩

theorem forcingSubsetConditions_bounded_iff {T P R H σ τ p : V} [IsTransitive T]
    (hR : IsForcingPreorder P R) (hname : IsForcingName P σ)
    (hH : IsAtomicTruthTable P R T H) (hσ : σ ∈ T) (hτ : τ ∈ T) :
    p ∈ forcingSubsetConditions P R σ τ ↔ p ∈ P ∧
      boundedEqualityLeftFormula.Evalb ![T, P, R, H, σ, τ, p] := by
  rw [forcingSubsetConditions_iff_atomic hR hname,
    eval_boundedEqualityLeftFormula_subset hH hσ hτ]

end ZFVP
