import ZFVP.ModelTheory.InfinitaryAdequateOmegaOneConstruction
import ZFVP.ModelTheory.InfinitaryOmegaOneCardinality

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

/-- Every adequate countable weak model embeds elementarily, for its fixed
fragment, into an actual standard-Q model of size at most aleph-one. -/
theorem exists_standard_elementary_extension (hM : M.Adequate S) (hS : S.Countable) :
    ∃ N : Type, ∃ _ : Nonempty N, ∃ s : Structure L N,
      @Structure.Eq L N s _ ∧ Cardinal.mk N ≤ Cardinal.aleph 1 ∧
        ∃ f : M.Domain → N, Function.Injective f ∧
          ∀ {n} (φ : Formula L n),
            ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
              ∀ b : Fin n → M.Domain,
                @Formula.Eval L N s n φ (f ∘ b) ↔ Formula.WeakEval M.Q φ b := by
  obtain ⟨C, e, hg, hf, hc, _, _, _⟩ := M.exists_adequate_omegaOne_chain hM hS
  refine ⟨C.Limit, inferInstance, C.limitStructure, C.limitStructure_eq,
    C.mk_limit_le_alephOne, C.fromStage omegaOneZero ∘ e,
    (C.fromStage_injective omegaOneZero).comp e.injective, ?_⟩
  intro n φ hφ b
  exact (C.standardEval_fromStage_of_successors_and_continuity hg hf hc φ hφ (e ∘ b)).trans
    (e.elementary φ hφ b)

end WeakModel
end ZFVP.Infinitary
