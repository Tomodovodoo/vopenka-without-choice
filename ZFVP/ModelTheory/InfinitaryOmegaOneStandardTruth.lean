import ZFVP.ModelTheory.InfinitaryOmegaOneStandardFibers

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakDirectedChain
open FragmentClosure
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  (C : WeakDirectedChain.{u,0,v} OmegaOne S)

/-- Local successor growth and small-fiber preservation identify the constructed
weak semantics with standard uncountability semantics throughout the fragment. -/
theorem standardEval_iff_weakEval (hgrowth : C.LargeFiberSuccessorGrowth)
    (hsmall : C.PreservesSmallFibers) {n} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → C.Limit) :
    Formula.Eval φ b ↔ Formula.WeakEval C.limitQuantifier φ b := by
  induction φ with
  | fo φ => rfl
  | neg φ ih =>
    have hc := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    exact not_congr (ih hc b)
  | conj f ih =>
    have hc (m : ℕ) : ⟨_, f m⟩ ∈ FragmentClosure.carrier S :=
      subformulas_closed hφ (Or.inr (Set.mem_iUnion.mpr ⟨m, Formula.self_mem_subformulas (f m)⟩))
    exact forall_congr' fun m ↦ ih m (hc m) b
  | exs φ ih =>
    have hc := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    exact exists_congr fun x ↦ ih hc (x :> b)
  | q φ ih =>
    have hc := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    have he : {x : C.Limit | Formula.Eval φ (x :> b)} =
        {x : C.Limit | Formula.WeakEval C.limitQuantifier φ (x :> b)} := by
      ext x
      exact ih hc (x :> b)
    have hf : {x : C.Limit | Formula.WeakEval C.limitQuantifier φ (x :> b)} =
        C.LimitFiber φ b := by
      ext x
      exact C.limit_weak_truth φ hc (x :> b)
    change (¬Set.Countable _) ↔ C.limitQuantifier _
    rw [he, hf]
    exact (C.limitQuantifier_fiber_iff_uncountable hgrowth hsmall hc b).symm

theorem standardEval_iff_stageEval (hgrowth : C.LargeFiberSuccessorGrowth)
    (hsmall : C.PreservesSmallFibers) {n} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → C.Limit) :
    Formula.Eval φ b ↔ C.StageEval φ b :=
  (C.standardEval_iff_weakEval hgrowth hsmall φ hφ b).trans (C.limit_weak_truth φ hφ b)

theorem standardEval_fromStage (hgrowth : C.LargeFiberSuccessorGrowth)
    (hsmall : C.PreservesSmallFibers) {n i} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → (C.model i).Domain) :
    Formula.Eval φ (C.fromStage i ∘ b) ↔ Formula.WeakEval (C.model i).Q φ b :=
  (C.standardEval_iff_weakEval hgrowth hsmall φ hφ _).trans (C.weakEval_fromStage φ hφ b)

theorem standard_sentence_fromStage (hgrowth : C.LargeFiberSuccessorGrowth)
    (hsmall : C.PreservesSmallFibers) (φ : Sentence L)
    (hφ : ⟨0, φ⟩ ∈ FragmentClosure.carrier S) (i : OmegaOne) :
    Formula.Eval φ (Fin.elim0 : Fin 0 → C.Limit) ↔
      Formula.WeakEval (C.model i).Q φ Fin.elim0 := by
  have h := C.standardEval_fromStage hgrowth hsmall φ hφ
    (Fin.elim0 : Fin 0 → (C.model i).Domain)
  have he : C.fromStage i ∘ (Fin.elim0 : Fin 0 → (C.model i).Domain) =
      (Fin.elim0 : Fin 0 → C.Limit) := Subsingleton.elim _ _
  rwa [he] at h

/-- A stage's weak theory becomes a true theory in the actual standard limit. -/
theorem standard_models_of_stage (hgrowth : C.LargeFiberSuccessorGrowth)
    (hsmall : C.PreservesSmallFibers) (Δ : Set (Sentence L))
    (hΔ : ∀ φ ∈ Δ, ⟨0, φ⟩ ∈ FragmentClosure.carrier S) (i : OmegaOne)
    (ht : ∀ φ ∈ Δ, Formula.WeakEval (C.model i).Q φ Fin.elim0) :
    ∀ φ ∈ Δ, Formula.Eval φ (Fin.elim0 : Fin 0 → C.Limit) :=
  fun φ hφ ↦ (C.standard_sentence_fromStage hgrowth hsmall φ (hΔ φ hφ) i).mpr (ht φ hφ)

end WeakDirectedChain
end ZFVP.Infinitary
