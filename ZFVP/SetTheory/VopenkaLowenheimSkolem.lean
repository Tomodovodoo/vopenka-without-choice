import ZFVP.SetTheory.VopenkaFullChoiceless
import ZFVP.SetTheory.ChoicelessSupercompactLS

/-! Full VP gives a proper class of LS cardinals. Taking successive least
LS cardinals gives singular LS cardinals of cofinality omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_lsCardinal_unbounded
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (ξ : V) [IsOrdinal ξ] : ∃ κ : V, ξ ∈ κ ∧ IsLSCardinal κ := by
  obtain ⟨κ, hξκ, hκ, _⟩ := vopenka_choicelessSupercompact_cofinality_omega hVP 0 ξ
  exact ⟨κ, hξκ, hκ.lsCardinal⟩

theorem lsCardinal_cofinality_omega_of_unbounded
    (hLS : ∀ ξ : V, IsOrdinal ξ → ∃ κ : V, ξ ∈ κ ∧ IsLSCardinal κ)
    (ξ : V) [IsOrdinal ξ] :
    ∃ κ : V, ξ ∈ κ ∧ IsLSCardinal κ ∧ internalCofinality κ = ω := by
  let R : V → V → Prop := fun α κ ↦ α ∈ κ ∧ IsLSCardinal κ
  have hR : ℒₛₑₜ-relation R := by unfold R; definability
  let F := leastOrdinalOrZero R hR
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hspec (α : V) (hα : IsOrdinal α) : α ∈ F α ∧ IsLSCardinal (F α) := by
    obtain ⟨κ, hακ, hκ⟩ := hLS α hα
    exact (leastOrdinalOrZero_spec R hR α ⟨κ, hκ.1.1, hακ, hκ⟩).2.1
  have hstep (α : V) (hα : IsOrdinal α) : IsOrdinal (F α) ∧ α ∈ F α :=
    ⟨(hspec α hα).2.1.1, (hspec α hα).1⟩
  obtain ⟨κ, hκ, hξκ, hcf, hstage, hcof⟩ := ordinalIteration_limit F hF ξ hstep
  let := hκ
  refine ⟨κ, hξκ, lsCardinal_of_cofinally_ls ⟨ξ, hξκ⟩ ?_, hcf⟩
  intro α hα
  obtain ⟨m, hm, hαm⟩ := hcof α hα
  have ho : IsOrdinal (naturalIteration F hF ξ m) := IsOrdinal.of_mem (hstage m hm)
  have hs := hspec _ ho
  have hnext := hstage (succ m) (ω_succ_closed hm)
  rw [naturalIteration_succ F hF ξ hm] at hnext
  let := hs.2.1.1
  exact ⟨F (naturalIteration F hF ξ m), hnext,
    IsOrdinal.toIsTransitive.mem_trans hαm hs.1, hs.2⟩

theorem vopenka_singular_lsCardinal
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (ξ : V) [IsOrdinal ξ] :
    ∃ κ : V, ξ ∈ κ ∧ IsLSCardinal κ ∧ internalCofinality κ = ω ∧ internalCofinality κ ∈ κ := by
  obtain ⟨κ, hξκ, hκ, hcf⟩ := lsCardinal_cofinality_omega_of_unbounded
    (fun α hα ↦ by let := hα; exact vopenka_lsCardinal_unbounded hVP α) ξ
  exact ⟨κ, hξκ, hκ, hcf, hcf.symm ▸ hκ.2.1⟩

end ZFVP
