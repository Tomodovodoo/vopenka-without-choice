import ZFVP.ModelTheory.SchmerlInternalDiamondTruth
import ZFVP.ModelTheory.SchmerlAcceptedGuessFamily

/-! At a diamond point on the carrier-agreement club, the accepted pair
is the exact trace of the guessed set and its full carrier complement. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_internalDiamondCarrierGuess {A κ C X E : V}
    (hA : IsInternalDiamondSequence A κ) (hX : X ⊆ κ) (hE : IsClubIn E κ)
    (hD : ∀ α ∈ E, structureDomain (C ‘ α) = α) :
    ∃ α ∈ κ, α ∈ E ∧ guessedU A C α = X ∩ α ∧ guessedW A C α = α \ X := by
  obtain ⟨α, hαS, hαE⟩ := (hA.2.2.2 X hX).2 E hE
  obtain ⟨hακ, hguess⟩ := mem_sep_iff.mp hαS
  have hU : guessedU A C α = X ∩ α := by
    apply mem_ext
    intro x
    simp only [guessedU, hguess, hD α hαE, mem_inter_iff, and_assoc, and_self]
  refine ⟨α, hακ, hαE, hU, ?_⟩
  rw [guessedW, hD α hαE, hU]
  apply mem_ext
  intro x
  simp only [mem_sdiff_iff, mem_inter_iff]
  tauto

end ZFVP.Schmerl
