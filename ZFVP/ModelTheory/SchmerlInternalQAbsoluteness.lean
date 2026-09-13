import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.SetTheory.EndExtensionWellOrdering
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.CountableSets
import ZFVP.Syntax.EndExtensionSatisfaction

/-! Actual internal countability is absolute for checked ground sets when
omega-one is preserved. This is the standard-Q step in old-model truth
preservation; it does not invoke a completeness or absoluteness premise. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem hartogs_omega_cardLE_of_uncountable (hAC : InternalChoice V) {A : V}
    (hA : ¬IsInternallyCountable A) : hartogsNumber (ω : V) ≤# A := by
  have hwo := wellOrderable_of_internalChoice hAC A
  let κ := wellOrderedCardinal A
  have hκ : IsOrdinal κ := (wellOrderedCardinal_initial hwo).1
  have he := wellOrderedCardinal_cardEQ hwo
  have hn : ¬κ ≤# (ω : V) := fun h ↦ hA (he.2.trans h)
  exact (cardLE_of_subset (hartogsNumber_minimal hn)).trans he.1

namespace MembershipEndExtension

theorem internallyCountable_iff_of_omegaOne (j : MembershipEndExtension V W)
    (hAC : InternalChoice V)
    (hω₁ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : W)) (A : V) :
    IsInternallyCountable (j A) ↔ IsInternallyCountable A := by
  constructor
  · intro h
    by_contra hnot
    have hle := j.map_cardLE (hartogs_omega_cardLE_of_uncountable hAC hnot)
    rw [hω₁] at hle
    exact hartogs_omega_not_countable (hle.trans h)
  · intro h
    have hh := j.map_cardLE h
    simpa only [j.map_omega, IsInternallyCountable] using hh

theorem uncountable_separation_iff_of_omegaOne (j : MembershipEndExtension V W)
    (hAC : InternalChoice V)
    (hω₁ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : W))
    (A : V) (P : V → Prop) (Q : W → Prop)
    (hP : ℒₛₑₜ-predicate[V] P) (hQ : ℒₛₑₜ-predicate[W] Q)
    (hPQ : ∀ x ∈ A, P x ↔ Q (j x)) :
    (¬IsInternallyCountable (sep (j A) Q hQ)) ↔ ¬IsInternallyCountable (sep A P hP) := by
  rw [← j.map_separation A P Q hP hQ hPQ]
  exact not_congr (j.internallyCountable_iff_of_omegaOne hAC hω₁ (sep A P hP))

end MembershipEndExtension
end ZFVP
