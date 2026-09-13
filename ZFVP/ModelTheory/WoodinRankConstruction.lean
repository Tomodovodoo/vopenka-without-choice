import ZFVP.ModelTheory.WoodinRankInduction
import ZFVP.ModelTheory.WoodinRecursionUniform
import ZFVP.ModelTheory.CountableZFTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinRankConstructionFormula : SetTheorySemisentence 1 :=
  f“δ. !woodinSupercompactFormula δ → ∀ θ ∈ δ,
    !woodinRankStageFormula θ (!kpair.π₁.dfn (!woodinIterationRecFormula θ))
      (!kpair.π₂.dfn (!woodinIterationRecFormula θ))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinRankConstructionFormula_defined : Defined
    (fun v : Fin 1 → V ↦ IsWoodinSupercompact (v 0) →
      ∀ θ ∈ v 0, WoodinRankStage θ (kpair.π₁ (woodinIterationRec θ))
        (kpair.π₂ (woodinIterationRec θ))) woodinRankConstructionFormula :=
  ⟨fun v ↦ by simp [woodinRankConstructionFormula]⟩

/-- Uniform transfer removes the external countability restriction from the
rank invariant for the actual recursive construction. -/
theorem woodinIteration_rankStages {δ : V} (hδ : IsWoodinSupercompact δ) :
    ∀ θ ∈ δ, WoodinRankStage θ (kpair.π₁ (woodinIterationRec θ))
      (kpair.π₂ (woodinIterationRec θ)) := by
  have hv : woodinRankConstructionFormula.Evalb (![δ] : Fin 1 → V) := by
    apply eval_of_countable_zf woodinRankConstructionFormula
    intro W _ _ _ _ w
    exact (Defined.eval_iff _).mpr (fun hδ ↦ woodinIteration_rankStages_countable hδ)
  exact (Defined.eval_iff _).mp hv hδ

end ZFVP
