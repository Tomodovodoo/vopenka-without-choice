import ZFVP.ModelTheory.InfinitaryAdequateTruth
import ZFVP.ModelTheory.InfinitaryAdequateSmallFibers

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

namespace ParameterInstance

def unaryInstance {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → M.Domain) : ParameterInstance M S 1 :=
  ⟨n, ⟨⟨φ.rename (Fin.cast (Nat.add_comm n 1)), FragmentClosure.rename_closed hφ _⟩, b⟩⟩

@[simp] theorem eval_unaryInstance {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → M.Domain) (a : Fin 1 → M.Domain) :
    (unaryInstance φ hφ b).Eval a ↔ Formula.WeakEval M.Q φ (a 0 :> b) := by
  simp [Eval, unaryInstance, Formula.weakEval_rename, Fin.append_left_eq_cons, Function.comp_def]
  apply Iff.of_eq
  congr 1

end ParameterInstance
namespace AdequateGenericChain
variable {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

theorem eval_ofFormula_rename {n m} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ρ : Fin n → Fin m) (ts : Fin m → ℕ) :
    C.Eval (ParameterInstance.ofFormula (φ.rename ρ) (FragmentClosure.rename_closed hφ ρ)) ts ↔
      C.Eval (ParameterInstance.ofFormula φ hφ) (ts ∘ ρ) := by
  have he : C.Eval (ParameterInstance.ofFormula (φ.rename ρ) (FragmentClosure.rename_closed hφ ρ)) ts ↔
      C.Eval ((ParameterInstance.ofFormula φ hφ).rename ρ) ts := by
    apply C.eval_congr
    intro a
    simp only [ParameterInstance.eval_ofFormula, ParameterInstance.eval_rename, Formula.weakEval_rename]
  exact he.trans (C.eval_rename _ _ _)

theorem eval_unaryInstance {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → M.Domain) (t : ℕ) :
    C.Eval (ParameterInstance.unaryInstance φ hφ b) (t :> Fin.elim0) ↔
      C.Eval (ParameterInstance.ofFormula φ hφ) (t :> C.oldCoordinate ∘ b) := by
  rw [C.eval_parameterInstance]
  change C.Eval (ParameterInstance.ofFormula (φ.rename (Fin.cast (Nat.add_comm n 1))) _)
    (Fin.append (t :> Fin.elim0) (C.oldCoordinate ∘ b)) ↔ _
  rw [C.eval_ofFormula_rename φ hφ]
  simp [Fin.append_left_eq_cons, Function.comp_def]
  apply Iff.of_eq
  congr 1

theorem named_semantic_fiber {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → M.Domain) :
    {x : C.Domain | Formula.WeakEval C.extensionQuantifier φ (x :> C.oldEmbedding ∘ b)} =
      C.genericFiber (ParameterInstance.unaryInstance φ hφ b) Fin.elim0 := by
  ext x
  obtain ⟨t, rfl⟩ := C.classOf_surjective x
  change Formula.WeakEval C.extensionQuantifier φ (C.classOf t :> C.classOf ∘ (C.oldCoordinate ∘ b)) ↔ _
  rw [← C.classOf_cons, C.extension_truth φ hφ, C.classOf_mem_genericFiber]
  exact (C.eval_unaryInstance φ hφ b t).symm

/-- Every old negative definable fiber with arbitrary finite old parameters is frozen exactly. -/
theorem parameterized_small_fiber_eq_oldImage {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → M.Domain) (hs : ¬M.Q {x | Formula.WeakEval M.Q φ (x :> b)}) :
    {x : C.Domain | Formula.WeakEval C.extensionQuantifier φ (x :> C.oldEmbedding ∘ b)} =
      C.oldEmbedding '' {x | Formula.WeakEval M.Q φ (x :> b)} := by
  rw [C.named_semantic_fiber φ hφ b]
  have hsmall : ¬M.Q {x | (ParameterInstance.unaryInstance φ hφ b).Eval (x :> Fin.elim0)} := by
    simpa only [ParameterInstance.eval_unaryInstance, Matrix.cons_val_zero] using hs
  rw [C.small_fiber_eq_oldImage _ hsmall]
  congr 1
  ext x
  exact ParameterInstance.eval_unaryInstance φ hφ b (x :> Fin.elim0)

end AdequateGenericChain
end WeakModel
end ZFVP.Infinitary



