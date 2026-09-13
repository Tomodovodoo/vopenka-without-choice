import ZFVP.SetTheory.AtomicForcingSubstitution
import ZFVP.SetTheory.ForcingNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ForcingHasMemberBelow (P R τ q : V) : Prop :=
  ∃ ν, IsForcingName P ν ∧ ∃ p ∈ P, ⟨p, q⟩ₖ ∈ R ∧ p ∈ atomicMembership P R ν τ

instance forcingHasMemberBelow_definable (P R τ : V) :
    ℒₛₑₜ-predicate (ForcingHasMemberBelow P R τ) := by
  unfold ForcingHasMemberBelow
  definability

def ForcingMinimalMember (P R τ p ν : V) : Prop :=
  IsForcingName P ν ∧ p ∈ atomicMembership P R ν τ ∧
    ∀ μ, IsForcingName P μ → rank μ ∈ rank ν →
      ∀ r ∈ P, ⟨r, p⟩ₖ ∈ R → r ∉ atomicMembership P R μ τ

instance forcingMinimalMember_definable (P R τ : V) :
    ℒₛₑₜ-relation (ForcingMinimalMember P R τ) := by
  unfold ForcingMinimalMember
  definability

noncomputable def forcingFoundationDecisions (P R τ : V) : V :=
  {p ∈ P ; ¬ForcingHasMemberBelow P R τ p ∨ ∃ ν, ForcingMinimalMember P R τ p ν}

theorem mem_forcingFoundationDecisions_iff (P R τ p : V) :
    p ∈ forcingFoundationDecisions P R τ ↔
      p ∈ P ∧ (¬ForcingHasMemberBelow P R τ p ∨ ∃ ν, ForcingMinimalMember P R τ p ν) := mem_sep_iff

theorem forcingFoundationDecisions_dense {P R : V} (hR : IsForcingPreorder P R) (τ : V) :
    ForcingDense P R (forcingFoundationDecisions P R τ) := by
  classical
  refine ⟨fun _ h ↦ (mem_sep_iff.mp h).1, ?_⟩
  intro q hq
  by_cases he : ForcingHasMemberBelow P R τ q
  · obtain ⟨ν, hν, p, hp, hpq, hpM⟩ := he
    obtain ⟨α, hα, _⟩ := leastOrdinal_existsUnique
      (fun α ↦ ∃ ν, IsForcingName P ν ∧ rank ν = α ∧
        ∃ p ∈ P, ⟨p, q⟩ₖ ∈ R ∧ p ∈ atomicMembership P R ν τ)
      (by definability) ⟨rank ν, inferInstance, ν, hν, rfl, p, hp, hpq, hpM⟩
    obtain ⟨ν, hν, hνα, p, hp, hpq, hpM⟩ := hα.2.1
    refine ⟨p, (mem_forcingFoundationDecisions_iff _ _ _ _).mpr
      ⟨hp, Or.inr ⟨ν, hν, hpM, ?_⟩⟩, hpq⟩
    intro μ hμ hμν r hr hrp hrM
    have hle := hα.2.2 (rank μ) inferInstance
      ⟨μ, hμ, rfl, r, hr, hR.2.2 r hr p hp q hq hrp hpq, hrM⟩
    rw [hνα] at hμν
    exact mem_irrefl (rank μ) (hle (rank μ) hμν)
  · exact ⟨q, (mem_forcingFoundationDecisions_iff _ _ _ _).mpr ⟨hq, Or.inl he⟩, hR.2.1 q hq⟩

end ZFVP
