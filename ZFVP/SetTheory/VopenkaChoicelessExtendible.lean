import ZFVP.SetTheory.VopenkaDefinableClasses
import ZFVP.SetTheory.ChoicelessFailureObstruction

/-! Full Vopenka yields extendibility with any prescribed lower bound on
the critical point. This is the forward construction of Mohammd's Theorem 3.1. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_exists_alphaChoicelessExtendible
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (n : ℕ) (α : V) [IsOrdinal α] : ∃ γ, IsAlphaChoicelessExtendible (n + 1) α γ := by
  classical
  by_contra hn
  have hfail : ∀ γ, ¬IsAlphaChoicelessExtendible (n + 1) α γ := fun γ hγ ↦ hn ⟨γ, hγ⟩
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_definable_class hVP
    (namedMembershipLanguageCode (succ (succ α)))
    (IsChoicelessFailureStructure (n + 1) (n + 2) α) (by definability)
    (choicelessFailureStructure_proper (n + 1) (n + 2) α hfail)
    (fun _ hM ↦ hM.valid)
  exact choicelessFailureStructures_no_embedding hM hN hne hf

theorem vopenka_least_alphaChoicelessExtendible
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (n : ℕ) (α : V) [IsOrdinal α] :
    ∃! γ, IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ :=
  leastAlphaChoicelessExtendible_existsUnique (n + 1) α
    (vopenka_exists_alphaChoicelessExtendible hVP n α)

end ZFVP
