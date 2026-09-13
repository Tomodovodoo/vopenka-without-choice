import ZFVP.SetTheory.ElementaryMap
import ZFVP.SetTheory.OrdinalDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]

theorem ElementaryMap.evalb (j : ElementaryMap V W) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : Fin n → V) : φ.Evalb b ↔ φ.Evalb (j ∘ b) := by
  have hf : j ∘ (Empty.elim : Empty → V) = (Empty.elim : Empty → W) :=
    funext (fun x ↦ nomatch x)
  have h := j.elementary φ b Empty.elim
  rw [hf] at h
  exact h

variable [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ElementaryMap.dependentChoiceAt (j : ElementaryMap V W) {γ : V}
    (h : InternalDependentChoiceAt γ) : InternalDependentChoiceAt (j γ) := by
  have ht : dependentChoiceAtFormula.Evalb ![γ] := (Defined.eval_iff _).mpr h
  have ht' := (j.evalb dependentChoiceAtFormula ![γ]).mp ht
  have hv : (j ∘ ![γ]) = ![j γ] := funext (fun i ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) i)
  have ht'' : dependentChoiceAtFormula.Evalb ![j γ] :=
    (congrArg (fun b ↦ dependentChoiceAtFormula.Evalb b) hv) ▸ ht'
  exact (Defined.eval_iff _).mp ht''

end ZFVP
