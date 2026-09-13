import ZFVP.SetTheory.BoundedAtomicTruth

/-! Membership forcing is a bounded density test against an atomic equality table. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedAtomicMembershipFormula : SetTheorySemisentence 7 :=
  “T P R H σ τ p. p ∈ P ∧ ∀ q ∈ P, !boundedPairMemberFormula R q p →
    ∃ r ∈ P, !boundedPairMemberFormula R r q ∧ ∃ v ∈ T, ∃ s ∈ T,
      !boundedPairMemberFormula τ v s ∧ !boundedPairMemberFormula R r s ∧
        !boundedTripleMemberFormula H σ v r”

theorem boundedAtomicMembershipFormula_bounded : IsBoundedSetFormula boundedAtomicMembershipFormula := by
  repeat' first
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | exact boundedTripleMemberFormula_bounded.subst _
    | exact IsBoundedSetFormula.rel _ _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedAtomicMembershipFormula {T P R H σ τ : V} [hT : IsTransitive T]
    (hH : IsAtomicTruthTable P R T H) (hσ : σ ∈ T) (hτ : τ ∈ T) (p : V) :
    boundedAtomicMembershipFormula.Evalb ![T, P, R, H, σ, τ, p] ↔ p ∈ atomicMembership P R σ τ := by
  simp [boundedAtomicMembershipFormula, mem_atomicMembership_iff, AtomicMembershipTest]
  intro _
  constructor
  · intro h q hq hqp
    obtain ⟨r, hr, hrq, v, hvT, s, _, hvs, hrs, hentry⟩ := h q hq hqp
    exact ⟨r, hr, hrq, v, s, hvs, hrs,
      (hH.entry (transitive_subnameClosed hT) hσ hvT).mp ⟨hr, hentry⟩⟩
  · intro h q hq hqp
    obtain ⟨r, hr, hrq, v, s, hvs, hrs, he⟩ := h q hq hqp
    obtain ⟨hvT, hsT⟩ := subname_pair_components_mem_transitive hτ hvs
    exact ⟨r, hr, hrq, v, hvT, s, hsT, hvs, hrs,
      ((hH.entry (transitive_subnameClosed hT) hσ hvT).mpr he).2⟩

end ZFVP
