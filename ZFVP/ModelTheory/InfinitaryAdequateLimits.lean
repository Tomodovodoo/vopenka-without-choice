import ZFVP.ModelTheory.InfinitaryAdequateModel
import ZFVP.ModelTheory.InfinitaryWeakChainSemantics

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v w

namespace WeakElementaryMap
variable {L : Language.{u}} [L.Eq] {T : Set (TaggedFormula L)}
  {M : WeakModel.{u,v} L} {N : WeakModel.{u,w} L}

/-- An embedding preserves each old negative fragment fiber exactly, with every
finite tuple of old parameters. -/
def FreezesSmallFibers (e : WeakElementaryMap T M N) : Prop :=
  ∀ {n} (φ : Formula L (n + 1)), ⟨n + 1, φ⟩ ∈ T →
    ∀ b : Fin n → M.Domain,
      ¬M.Q {x | Formula.WeakEval M.Q φ (x :> b)} →
        {y : N.Domain | Formula.WeakEval N.Q φ (y :> e ∘ b)} =
          e '' {x : M.Domain | Formula.WeakEval M.Q φ (x :> b)}

end WeakElementaryMap

namespace WeakOmegaChain
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  (C : WeakOmegaChain.{u,v} S)

/-- A limit fiber is already the image of its old source fiber when every stage
map freezes old small fibers. Only one point and its finite parameter tuple are
placed in a common stage. -/
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
    let k := max i j
    have hi : i ≤ k := Nat.le_max_left _ _
    have hj : j ≤ k := Nat.le_max_right _ _
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

theorem limitEmbedding_freezes
    (hf : ∀ i j (h : i ≤ j), (C.map h).FreezesSmallFibers) (i : ℕ) :
    (C.limitEmbedding i).FreezesSmallFibers := by
  intro n φ hφ b hs
  exact C.small_fiber_eq_stageImage hf φ hφ b hs

variable (D : WeakOmegaChain.{u,v} (SequenceClosure.carrier S))

/-- Full fragment elementarity transfers universally closed adequacy schemas to
every parameter tuple in the actual countable weak limit. -/
theorem limit_adequate_of_stage (i : ℕ) (hi : (D.model i).Adequate S) :
    D.limitModel.Adequate S := hi.of_elementary (D.limitEmbedding i)

theorem limit_adequate (hm : ∀ i, (D.model i).Adequate S) : D.limitModel.Adequate S :=
  D.limit_adequate_of_stage 0 (hm 0)

end WeakOmegaChain
end ZFVP.Infinitary
