import ZFVP.SetTheory.VopenkaChoicelessExtendible
import ZFVP.SetTheory.ChoicelessEquivalence
import ZFVP.SetTheory.LeastOrdinalChoice
import ZFVP.SetTheory.OrdinalIterationLimit

/-! Full Vopenka gives unbounded choiceless cardinals. The construction
uses least relative witnesses and an internal omega iteration. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_choicelessExtendible_cofinality_omega
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (n : ℕ) (ξ : V) [IsOrdinal ξ] :
    ∃ κ : V, ξ ∈ κ ∧ IsChoicelessExtendible (n + 1) κ ∧ internalCofinality κ = ω := by
  let R := IsAlphaChoicelessExtendible (n + 1) (V := V)
  have hR : ℒₛₑₜ-relation R := by unfold R; definability
  let F := leastOrdinalOrZero R hR
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hspec (α : V) (hα : IsOrdinal α) : IsAlphaChoicelessExtendible (n + 1) α (F α) := by
    let := hα
    obtain ⟨γ, hγ⟩ := vopenka_exists_alphaChoicelessExtendible hVP n α
    exact (leastOrdinalOrZero_spec R hR α ⟨γ, hγ.ordinal, hγ⟩).2.1
  have hstep (α : V) (hα : IsOrdinal α) : IsOrdinal (F α) ∧ α ∈ F α :=
    ⟨(hspec α hα).ordinal, (hspec α hα).2.1⟩
  obtain ⟨κ, hκ, hξκ, hcf, hstage, hcof⟩ := ordinalIteration_limit F hF ξ hstep
  let := hκ
  refine ⟨κ, hξκ, ⟨hκ, ⟨ξ, hξκ⟩, ?_⟩, hcf⟩
  intro α hα
  obtain ⟨m, hm, hαm⟩ := hcof α hα
  have ho : IsOrdinal (naturalIteration F hF ξ m) := IsOrdinal.of_mem (hstage m hm)
  have hrel := (hspec _ ho).lower_bound hαm
  apply hrel.raise_ordinal hκ
  rw [← naturalIteration_succ F hF ξ hm]
  exact hstage (succ m) (ω_succ_closed hm)

theorem vopenka_choicelessSupercompact_cofinality_omega
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (n : ℕ) (ξ : V) [IsOrdinal ξ] :
    ∃ κ : V, ξ ∈ κ ∧ IsChoicelessSupercompact (n + 2) κ ∧
      IsInitialOrdinal κ ∧ (ω : V) ∈ κ ∧ internalCofinality κ = ω := by
  obtain ⟨κ, hξκ, hκ, hcf⟩ := vopenka_choicelessExtendible_cofinality_omega hVP n ξ
  have hs := hκ.supercompact_succ
  exact ⟨κ, hξκ, hs, hs.initial, hs.omega_lt, hcf⟩

end ZFVP
