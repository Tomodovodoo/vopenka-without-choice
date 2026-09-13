import ZFVP.ModelTheory.WoodinRankConstruction
import ZFVP.ModelTheory.WoodinEndpointDirect

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinEndpointRankFormula : SetTheorySemisentence 1 :=
  f“δ. !woodinSupercompactFormula δ → ¬!choiceFunctionSentence →
    !woodinRankStageFormula δ (!kpair.π₁.dfn (!woodinIterationRecFormula δ))
      (!kpair.π₂.dfn (!woodinIterationRecFormula δ))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinEndpointRankFormula_defined : Defined
    (fun v : Fin 1 → V ↦ IsWoodinSupercompact (v 0) → ¬InternalChoice V →
      WoodinRankStage (v 0) (kpair.π₁ (woodinIterationRec (v 0)))
        (kpair.π₂ (woodinIterationRec (v 0)))) woodinEndpointRankFormula :=
  ⟨fun v ↦ by simp [woodinEndpointRankFormula]⟩

theorem woodinIteration_endpoint_rankStage_countable [Countable V] {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    WoodinRankStage δ (kpair.π₁ (woodinIterationRec δ)) (kpair.π₂ (woodinIterationRec δ)) := by
  let := hδ.inaccessible.1
  have hv := woodinIteration_endpoint_valid hδ hAC
  have hs : ∀ i ∈ δ, IsWoodinIteration (succ δ) (succ i)
      (kpair.π₁ (woodinIterationRec i)) (kpair.π₂ (woodinIterationRec i)) := by
    intro i hi
    exact ((woodinIterationExit hδ hAC).2.1 i hi).1.enlarge_bound
      (fun _ hx ↦ mem_succ_iff.mpr (Or.inr hx))
  apply hv.1.limit_rankEnumerations hv.2
    (fun _ hi ↦ regularCardinal_succ_closed hδ.inaccessible.regular hi)
  intro i hi
  exact (woodinIterationRec_rankStage_previous hs hv.1 hi).mp (woodinIteration_rankStages hδ i hi)

theorem woodinIteration_endpoint_rankStage {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    WoodinRankStage δ (kpair.π₁ (woodinIterationRec δ)) (kpair.π₂ (woodinIterationRec δ)) := by
  have hv : woodinEndpointRankFormula.Evalb (![δ] : Fin 1 → V) := by
    apply eval_of_countable_zf woodinEndpointRankFormula
    intro W _ _ _ _ w
    exact (Defined.eval_iff _).mpr (fun hδ hAC ↦ woodinIteration_endpoint_rankStage_countable hδ hAC)
  exact (Defined.eval_iff _).mp hv hδ hAC

end ZFVP
