import ZFVP.ModelTheory.InfinitaryAdequateLimits
import ZFVP.ModelTheory.InfinitaryCountablyDirectedWeakLimit

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v w
namespace WeakDirectedChain
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {I : Type v} [Preorder I] [Nonempty I] {S : Set (TaggedFormula L)}
  (C : WeakDirectedChain.{u,v,w} I S)

/-- A source small fiber is preserved exactly in the constructed directed limit.
This equality does not require the index type itself to be countable. -/
theorem small_fiber_eq_stageImage
    (hf : ∀ i j (h : i ≤ j), (C.map h).FreezesSmallFibers)
    {n} (φ : Formula L (n + 1)) (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S)
    {i} (b : Fin n → (C.model i).Domain)
    (hs : ¬(C.model i).Q {x | Formula.WeakEval (C.model i).Q φ (x :> b)}) :
    {z : C.Limit | Formula.WeakEval C.limitQuantifier φ (z :> C.fromStage i ∘ b)} =
      C.fromStage i '' {x | Formula.WeakEval (C.model i).Q φ (x :> b)} := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, y, rfl⟩ := C.stage_cover z
    change Formula.WeakEval C.limitQuantifier φ (C.fromStage j y :> C.fromStage i ∘ b) at hz
    let k := C.upper i j
    have hi : i ≤ k := C.le_upper_left i j
    have hj : j ≤ k := C.le_upper_right i j
    have hy : Formula.WeakEval (C.model k).Q φ (C.map hj y :> C.map hi ∘ b) := by
      apply (C.weakEval_fromStage φ hφ _).mp
      simpa only [C.fromStage_cons, ← Function.comp_assoc, C.fromStage_comp,
        C.fromStage_coherent] using hz
    have hmem : C.map hj y ∈ C.map hi ''
        {x | Formula.WeakEval (C.model i).Q φ (x :> b)} :=
      (hf i k hi φ hφ b hs) ▸ hy
    obtain ⟨x, hx, he⟩ := hmem
    exact ⟨x, hx, (C.fromStage_eq_iff x y hi hj).mpr he⟩
  · rintro ⟨x, hx, rfl⟩
    change Formula.WeakEval C.limitQuantifier φ (C.fromStage i x :> C.fromStage i ∘ b)
    have ht := (C.weakEval_fromStage φ hφ (x :> b)).mpr hx
    simpa only [C.fromStage_cons] using ht

/-- For a countable index type, the actual directed limit has the countability
field needed by `WeakModel`. Its underlying structure and Q are unchanged. -/
noncomputable def countableLimitModel [Countable I] : WeakModel.{u,max v w} L where
  Domain := C.Limit
  str := C.limitStructure
  eq := C.limitStructure_eq
  nonempty := C.limit_nonempty
  countable := C.limit_countable
  Q := C.limitQuantifier
  mono := C.limitQuantifier_mono

noncomputable def countableLimitEmbedding [Countable I] (i : I) :
    WeakElementaryMap (FragmentClosure.carrier S) (C.model i) C.countableLimitModel where
  toFun := C.fromStage i
  injective := C.fromStage_injective i
  func := fun f b ↦ (C.func_fromStage f b).symm
  rel := C.rel_fromStage
  elementary := C.weakEval_fromStage

theorem countableLimitEmbedding_freezes [Countable I]
    (hf : ∀ i j (h : i ≤ j), (C.map h).FreezesSmallFibers) (i : I) :
    (C.countableLimitEmbedding i).FreezesSmallFibers := by
  intro n φ hφ b hs
  exact C.small_fiber_eq_stageImage hf φ hφ b hs

variable (D : WeakDirectedChain.{u,v,w} I (SequenceClosure.carrier S))

theorem countableLimit_adequate_of_stage [Countable I] (i : I)
    (hi : (D.model i).Adequate S) : D.countableLimitModel.Adequate S :=
  hi.of_elementary (D.countableLimitEmbedding i)

theorem countableLimit_adequate [Countable I] (hm : ∀ i, (D.model i).Adequate S) :
    D.countableLimitModel.Adequate S := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact D.countableLimit_adequate_of_stage i (hm i)

end WeakDirectedChain
end ZFVP.Infinitary
