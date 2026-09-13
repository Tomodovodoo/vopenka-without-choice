import ZFVP.ModelTheory.SchmerlInternalSubstitutionIdentities

/-! Substitution commutes with the derived internal Boolean constructors. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem infinitarySubstitutionGraph_and {L F G n φ ψ k : V} (hF : IsFragment L F)
    (ht : ⟨n, andCode φ ψ⟩ₖ ∈ F) (hk : k ∈ (ω : V)) :
    (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, andCode φ ψ⟩ₖ, k⟩ₖ =
      andCode ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ)
        ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, ψ⟩ₖ, k⟩ₖ) := by
  unfold andCode at ht ⊢
  rw [infinitarySubstitutionGraph_conj hF ht hk]
  apply congrArg conjCode
  apply functions_eq_of_domain_values (by simp only [domain_transformConjunction, domain_binaryCodeSequence])
  intro i hi
  rw [domain_transformConjunction] at hi
  rw [value_transformConjunction _ _ _ hi, value_binaryCodeSequence _ _ hi,
    value_binaryCodeSequence _ _ hi]
  simp only [substitutionChild, kpair.π₁_kpair, kpair.π₂_kpair]
  unfold binaryCodeValue
  split <;> rfl

theorem infinitarySubstitutionGraph_imp {L F G n φ ψ k : V} (hF : IsFragment L F)
    (ht : ⟨n, impCode φ ψ⟩ₖ ∈ F) (hk : k ∈ (ω : V)) :
    (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, impCode φ ψ⟩ₖ, k⟩ₖ =
      impCode ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ)
        ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, ψ⟩ₖ, k⟩ₖ) := by
  have ha := hF.neg_mem ht
  have hl := hF.and_left_mem ha
  have hr := hF.and_right_mem ha
  unfold impCode at ht ⊢
  rw [infinitarySubstitutionGraph_neg hF ht hk, infinitarySubstitutionGraph_and hF ha hk,
    infinitarySubstitutionGraph_neg hF hl hk,
    infinitarySubstitutionGraph_neg hF (hF.neg_mem hl) hk,
    infinitarySubstitutionGraph_neg hF hr hk]

theorem substituteCode_imp {L F s φ ψ : V} (hF : IsFragment L F)
    (ht : ⟨stateSource s, impCode φ ψ⟩ₖ ∈ F) :
    substituteCode L F s (impCode φ ψ) =
      impCode (substituteCode L F s φ) (substituteCode L F s ψ) :=
  infinitarySubstitutionGraph_imp hF ht (by simp)

end ZFVP.Infinitary.Internal
