module

public import ZFVP.ModelTheory.WoodinInvariantUniform
public import ZFVP.ModelTheory.WoodinConstructionCountable
public import ZFVP.ModelTheory.CountableZFTransfer
public import ZFVP.SetTheory.ChoiceDictionary

@[expose] public section

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def woodinConstructionAtFormula : SetTheorySemisentence 1 :=
  f“δ. !woodinSupercompactFormula δ → ¬!choiceFunctionSentence → !woodinIterationExitFormula δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinConstructionAtFormula_defined : Defined
    (fun v : Fin 1 → V ↦ IsWoodinSupercompact (v 0) → ¬InternalChoice V → WoodinIterationExit (v 0))
    woodinConstructionAtFormula :=
  ⟨fun v ↦ by simp [woodinConstructionAtFormula]⟩

/-- The restored-stage construction in any internal ZF model. The transfer uses
fixed formulas for the actual stage rule, recursion, invariant and endpoint. -/
theorem woodinIterationExit {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) : WoodinIterationExit δ := by
  have hv : woodinConstructionAtFormula.Evalb (![δ] : Fin 1 → V) := by
    apply eval_of_countable_zf woodinConstructionAtFormula
    intro W _ _ _ _ w
    exact (Defined.eval_iff _).mpr (fun hδ hAC ↦ woodinIterationExit_countable hδ hAC)
  exact (Defined.eval_iff _).mp hv hδ hAC

theorem woodinIterationConstruction : WoodinIterationConstruction (V := V) :=
  fun _ hδ hAC ↦ woodinIterationExit hδ hAC

end ZFVP
