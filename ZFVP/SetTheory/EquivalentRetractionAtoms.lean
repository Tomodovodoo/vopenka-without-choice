import ZFVP.SetTheory.ForcingRetraction
import ZFVP.SetTheory.NameActionEquivalentConditions
import ZFVP.SetTheory.AtomicForcingSubstitution

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRetraction.atomicMembership_nameAction_iff {P R N T m σ τ p : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) (hp : p ∈ P) :
    p ∈ atomicMembership P R σ τ ↔
      m ‘ p ∈ atomicMembership N T (nameAction m σ) (nameAction m τ) := by
  have hm := mem_function_of_mem_function_of_subset hr.maps hr.inclusion
  have hσeq := nameAction_forced_equal_of_equivalent_conditions hR hm he hσ p hp
  have hτeq := nameAction_forced_equal_of_equivalent_conditions hR hm he hτ p hp
  have hs : p ∈ atomicMembership P R σ τ ↔
      p ∈ atomicMembership P R (nameAction m σ) (nameAction m τ) := by
    constructor
    · intro hh
      exact atomicMembership_subst_right hR hτeq (atomicMembership_subst_left hR hσeq hh)
    · intro hh
      exact atomicMembership_subst_right hR (atomicEquality_symm P R τ (nameAction m τ) ▸ hτeq)
        (atomicMembership_subst_left hR (atomicEquality_symm P R σ (nameAction m σ) ▸ hσeq) hh)
  exact hs.trans (hr.atomicMembership_iff (nameAction_isName hr.maps hσ) (nameAction_isName hr.maps hτ) hp)

theorem IsForcingRetraction.atomicEquality_nameAction_iff {P R N T m σ τ p : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) (hp : p ∈ P) :
    p ∈ atomicEquality P R σ τ ↔
      m ‘ p ∈ atomicEquality N T (nameAction m σ) (nameAction m τ) := by
  have hm := mem_function_of_mem_function_of_subset hr.maps hr.inclusion
  have hσeq := nameAction_forced_equal_of_equivalent_conditions hR hm he hσ p hp
  have hτeq := nameAction_forced_equal_of_equivalent_conditions hR hm he hτ p hp
  have hs : p ∈ atomicEquality P R σ τ ↔
      p ∈ atomicEquality P R (nameAction m σ) (nameAction m τ) := by
    constructor
    · intro hh
      exact atomicEquality_trans hR _ σ _ p (atomicEquality_symm P R σ (nameAction m σ) ▸ hσeq)
        (atomicEquality_trans hR σ τ _ p hh hτeq)
    · intro hh
      exact atomicEquality_trans hR σ _ τ p hσeq
        (atomicEquality_trans hR _ _ τ p hh (atomicEquality_symm P R τ (nameAction m τ) ▸ hτeq))
  exact hs.trans (hr.atomicEquality_iff (nameAction_isName hr.maps hσ) (nameAction_isName hr.maps hτ) hp)

end ZFVP
