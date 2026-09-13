import ZFVP.ModelTheory.InfinitaryAdequateFirstOrderTruth
import ZFVP.ModelTheory.InfinitaryAdequateQuantifier

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel.AdequateGenericChain
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}
  {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

theorem eval_ofFormula_neg {n} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) (ts : Fin n → ℕ) :
    C.Eval (ParameterInstance.ofFormula (.neg φ) (FragmentClosure.neg_closed hφ)) ts ↔
      ¬C.Eval (ParameterInstance.ofFormula φ hφ) ts := C.eval_neg (ParameterInstance.ofFormula φ hφ) ts

theorem eval_ofFormula_conj {n} (f : ℕ → Formula L n)
    (hf : ⟨n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) (ts : Fin n → ℕ) :
    C.Eval (ParameterInstance.ofFormula (.conj f) hf) ts ↔
      ∀ i, C.Eval (ParameterInstance.ofFormula (f i)
        (FragmentClosure.subformulas_closed (φ := .conj f) hf (Or.inr (Set.mem_iUnion.mpr ⟨i, Formula.self_mem_subformulas (f i)⟩)))) ts :=
  C.eval_conj (⟨0, ⟨⟨f, hf⟩, Fin.elim0⟩⟩ : ParameterSequence M S n) ts

theorem eval_ofFormula_exs {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) (ts : Fin n → ℕ) :
    C.Eval (ParameterInstance.ofFormula (.exs φ) (FragmentClosure.exs_closed hφ)) ts ↔
      ∃ t, C.Eval (ParameterInstance.ofFormula φ hφ) (t :> ts) := by
  have he : C.Eval (ParameterInstance.ofFormula (.exs φ) (FragmentClosure.exs_closed hφ)) ts ↔
      C.Eval (ParameterInstance.ofFormula φ hφ).exs ts := by
    apply C.eval_congr
    intro b
    simp only [ParameterInstance.eval_ofFormula, ParameterInstance.eval_exs, Formula.weakEval_exs]
  exact he.trans (C.eval_exs _ ts)

theorem eval_ofFormula_q {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) (ts : Fin n → ℕ) :
    C.Eval (ParameterInstance.ofFormula (.q φ) (FragmentClosure.q_closed hφ)) ts ↔
      C.Eval (ParameterInstance.ofFormula φ hφ).q ts := by
  apply C.eval_congr
  intro b
  simp only [ParameterInstance.eval_ofFormula, ParameterInstance.eval_q, Formula.weakEval_q]


/-- Full weak fragment truth on the actual coordinate quotient with its actual Q. -/
theorem extension_truth {n} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) (ts : Fin n → ℕ) :
    Formula.WeakEval C.extensionQuantifier φ (C.classOf ∘ ts) ↔
      C.Eval (ParameterInstance.ofFormula φ hφ) ts := by
  induction φ with
  | fo φ => exact C.firstOrder_truth φ ts
  | neg φ ih =>
    have hbody := FragmentClosure.subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    rw [Formula.weakEval_neg, C.eval_ofFormula_neg φ hbody]
    exact not_congr (ih hbody ts)
  | conj f ih =>
    rw [Formula.weakEval_conj, C.eval_ofFormula_conj f hφ]
    exact forall_congr' fun i ↦ ih i _ ts
  | exs φ ih =>
    have hbody := FragmentClosure.subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    rw [Formula.weakEval_exs, C.eval_ofFormula_exs φ hbody]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨t, rfl⟩ := C.classOf_surjective x
      exact ⟨t, (ih hbody (t :> ts)).mp ((C.classOf_cons t ts).symm ▸ hx)⟩
    · rintro ⟨t, ht⟩
      exact ⟨C.classOf t, C.classOf_cons t ts ▸ (ih hbody (t :> ts)).mpr ht⟩
  | q φ ih =>
    have hbody := FragmentClosure.subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    have hf : {x : C.Domain | Formula.WeakEval C.extensionQuantifier φ (x :> C.classOf ∘ ts)} =
        C.genericFiber (ParameterInstance.ofFormula φ hbody) ts := by
      ext x
      obtain ⟨t, rfl⟩ := C.classOf_surjective x
      change Formula.WeakEval C.extensionQuantifier φ (C.classOf t :> C.classOf ∘ ts) ↔ _
      rw [← C.classOf_cons]
      exact (ih hbody (t :> ts)).trans (C.classOf_mem_genericFiber _ _ _).symm
    rw [Formula.weakEval_q, hf, C.extensionQuantifier_fiber, C.eval_ofFormula_q φ hbody]

theorem extension_elementary {n} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) (b : Fin n → M.Domain) :
    Formula.WeakEval C.extensionQuantifier φ (C.oldEmbedding ∘ b) ↔ Formula.WeakEval M.Q φ b := by
  change Formula.WeakEval C.extensionQuantifier φ (C.classOf ∘ (C.oldCoordinate ∘ b)) ↔ _
  rw [C.extension_truth φ hφ]
  exact (C.eval_named_tuple _ _ b (fun i ↦ C.oldCoordinate_names (b i))).trans
    (ParameterInstance.eval_ofFormula φ hφ b)

end WeakModel.AdequateGenericChain
end ZFVP.Infinitary

