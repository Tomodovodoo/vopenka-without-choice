import ZFVP.SetTheory.RankZermelo

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A class definable over an internal set domain is represented by an ambient
set. No truth predicate internal to that domain is assumed. -/
theorem setDomain_definable_set (U : V) (D : SetDomain U → Prop) (hD : ℒₛₑₜ-predicate D) :
    ∃ d : V, d ⊆ U ∧ ∀ x : SetDomain U, x.val ∈ d ↔ D x := by
  obtain ⟨φ, hφ⟩ := hD.definable
  let Q : V → Prop := fun x ↦ (relativize φ).Eval ![x]
    (fun i ↦ i.elim U (fun j : SetDomain U ↦ j.val))
  have hQ : ℒₛₑₜ-predicate Q := by
    apply Language.Definable.of_iff (relativizedEvaluation_definable U φ id)
    intro v
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change (relativize φ).Eval ![v 0] _ ↔ (relativize φ).Eval v _
    rw [hv]
    rfl
  refine ⟨{x ∈ U ; Q x}, fun _ h ↦ (mem_sep_iff.mp h).1, ?_⟩
  intro x
  simp only [mem_sep_iff, x.property, true_and]
  have he := eval_relativize U φ ![x] id
  have hv : (fun i ↦ ((![x] : Fin 1 → SetDomain U) i).val) = ![x.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at he
  exact he.trans (hφ ![x])

end ZFVP
