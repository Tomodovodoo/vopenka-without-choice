import ZFVP.ModelTheory.InfinitaryAdequateGrowthSpace
import ZFVP.ModelTheory.InfinitaryWeakOmegaChainSteps

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace DenseRequirementChain
open WeakModel WeakModel.AdequateExtension
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)} {hM : M.Adequate S}
  (C : DenseRequirementChain Refines Meets (AdequateExtension.initial hM))

noncomputable def stepMap (i : ℕ) :
    WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S))
      (C.point i).model (C.point (i + 1)).model := (C.step i).choose

theorem stepMap_freezes (i : ℕ) : (C.stepMap i).FreezesSmallFibers :=
  (C.step i).choose_spec.1

theorem stepMap_compatible (i : ℕ) (x : M.Domain) :
    C.stepMap i ((C.point i).embedding x) = (C.point (i + 1)).embedding x :=
  (C.step i).choose_spec.2 x

noncomputable def omegaChain : WeakOmegaChain.{u,v} (SequenceClosure.carrier S) :=
  WeakOmegaChain.ofSteps (fun i ↦ (C.point i).model) C.stepMap

theorem omegaChain_freezes : ∀ i j (h : i ≤ j), (C.omegaChain.map h).FreezesSmallFibers :=
  WeakOmegaChain.ofSteps_freezes _ _ C.stepMap_freezes

theorem omegaChain_compatible {i j : ℕ} (h : i ≤ j) (x : M.Domain) :
    C.omegaChain.map h ((C.point i).embedding x) = (C.point j).embedding x := by
  induction j, h using Nat.le_induction with
  | base => exact C.omegaChain.identity i _ _
  | succ j h ih =>
    change WeakOmegaChain.stepsMap _ C.stepMap _ _ = _
    rw [WeakOmegaChain.stepsMap_succ_apply _ C.stepMap h]
    change C.stepMap j (C.omegaChain.map h ((C.point i).embedding x)) = _
    rw [ih, C.stepMap_compatible]

noncomputable def limitBaseEmbedding :
    WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M C.omegaChain.limitModel :=
  (C.omegaChain.limitEmbedding 0).comp (C.point 0).embedding

theorem limitBaseEmbedding_coherent (i : ℕ) (x : M.Domain) :
    C.omegaChain.fromStage i ((C.point i).embedding x) = C.limitBaseEmbedding x := by
  rw [← C.omegaChain_compatible (Nat.zero_le i) x]
  exact C.omegaChain.fromStage_coherent (Nat.zero_le i) _

theorem limitBaseEmbedding_freezes : C.limitBaseEmbedding.FreezesSmallFibers :=
  (C.point 0).embedding.comp_freezes (C.omegaChain.limitEmbedding 0) (C.point 0).freezes
    (C.omegaChain.limitEmbedding_freezes C.omegaChain_freezes 0)

theorem limitBaseEmbedding_grows {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → M.Domain) (hq : M.Q {x | Formula.WeakEval M.Q φ (x :> b)}) :
    ∃ a : C.omegaChain.limitModel.Domain, a ∉ Set.range C.limitBaseEmbedding ∧
      Formula.WeakEval C.omegaChain.limitModel.Q φ (a :> C.limitBaseEmbedding ∘ b) := by
  obtain ⟨i, hi⟩ := C.meets (⟨n, ⟨⟨φ, hφ⟩, b⟩⟩ : Requirement M S)
  obtain ⟨a, ha, ht⟩ := hi hq
  refine ⟨C.omegaChain.fromStage i a, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    rw [← C.limitBaseEmbedding_coherent i x] at hx
    exact ha ⟨x, C.omegaChain.fromStage_injective i hx⟩
  · have h := (C.omegaChain.weakEval_fromStage φ hφ (a :> (C.point i).embedding ∘ b)).mpr ht
    change Formula.WeakEval C.omegaChain.limitQuantifier φ _
    have hb : C.omegaChain.fromStage i ∘ (a :> (C.point i).embedding ∘ b) =
        C.omegaChain.fromStage i a :> C.limitBaseEmbedding ∘ b := by
      funext j
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact C.limitBaseEmbedding_coherent i (b j)
    exact hb ▸ h

end DenseRequirementChain

namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

/-- One countable block grows every positive base fiber and freezes every
negative base fiber, retaining adequacy for the next block. -/
theorem exists_adequate_growth_block (hM : M.Adequate S) (hS : S.Countable) :
    ∃ N : WeakModel.{u,v} L,
      ∃ e : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M N,
        N.Adequate S ∧ e.FreezesSmallFibers ∧
          ∀ {n} (φ : Formula L (n + 1)),
            ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
              ∀ b : Fin n → M.Domain, M.Q {x | Formula.WeakEval M.Q φ (x :> b)} →
                ∃ a : N.Domain, a ∉ Set.range e ∧ Formula.WeakEval N.Q φ (a :> e ∘ b) := by
  obtain ⟨C⟩ := AdequateExtension.exists_growth_chain hM hS
  exact ⟨C.omegaChain.limitModel, C.limitBaseEmbedding,
    C.omegaChain.limit_adequate (fun i ↦ (C.point i).adequate),
    C.limitBaseEmbedding_freezes, C.limitBaseEmbedding_grows⟩

end WeakModel
end ZFVP.Infinitary
