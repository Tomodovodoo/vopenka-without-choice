import ZFVP.SetTheory.HartogsDictionary
import ZFVP.SetTheory.PiOneInitialOrdinal

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def deltaTwoHartogsFormula : SetTheorySemisentence 2 :=
  “α A. !IsOrdinal.dfn α ∧ (∀ f, ¬!boundedInjectionFormula f α A) ∧
    ∀ β ∈ α, ∃ f, !boundedInjectionFormula f β A”

theorem deltaTwoHartogsFormula_levy (pol : LevyPolarity) :
    IsLevyFormula pol 2 deltaTwoHartogsFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.and (.raise (IsLevyFormula.all (.bounded (boundedInjectionFormula_bounded.subst _).neg)))
      (.raise (IsLevyFormula.boundedAll (.bvar 0)
        (IsLevyFormula.exs (.bounded (boundedInjectionFormula_bounded.subst _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eq_hartogsNumber_iff_shorter_inject (α A : V) :
    α = hartogsNumber A ↔ IsOrdinal α ∧ ¬α ≤# A ∧ ∀ β ∈ α, β ≤# A := by
  constructor
  · rintro rfl
    exact ⟨inferInstance, not_hartogsNumber_cardLE A, fun _ ↦ cardLE_of_mem_hartogsNumber⟩
  · rintro ⟨hα, hn, hsmall⟩
    let := hα
    apply subset_antisymm _ (hartogsNumber_minimal hn)
    intro β hβ
    let : IsOrdinal β := IsOrdinal.of_mem hβ
    exact ordinal_cardLE_iff_mem_hartogsNumber.mp (hsmall β hβ)

instance deltaTwoHartogsFormula_defined : ℒₛₑₜ-function₁[V] hartogsNumber via deltaTwoHartogsFormula :=
  ⟨fun v ↦ by
    rw [eq_hartogsNumber_iff_shorter_inject]
    simp [deltaTwoHartogsFormula, CardLE]⟩

end ZFVP
