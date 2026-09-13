import ZFVP.SetTheory.FunctionComposition
import ZFVP.SetTheory.WellFoundedRecursion

/-! Shared formulas for composition and predecessors, with a total recursion interface. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def composeFormula : SetTheorySemisentence 3 :=
  f“C R S. ∀ p, p ∈ C ↔ ∃ x y z, !kpair.dfn x y ∈ R ∧ !kpair.dfn y z ∈ S ∧ p = !kpair.dfn x z”

def predecessorsFormula : SetTheorySemisentence 4 :=
  f“P R D x. ∀ y, y ∈ P ↔ y ∈ D ∧ !kpair.dfn y x ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance composeFormula_defined : ℒₛₑₜ-function₂[V] compose via composeFormula :=
  ⟨fun v ↦ by
    change composeFormula.Evalb v ↔ v 0 = compose (v 1) (v 2)
    rw [mem_ext_iff]
    simp [composeFormula, mem_compose_iff]⟩

instance predecessorsFormula_defined : ℒₛₑₜ-function₃[V] predecessors via predecessorsFormula :=
  ⟨fun v ↦ by
    change predecessorsFormula.Evalb v ↔ v 0 = predecessors (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [predecessorsFormula]⟩

theorem totalRecursionAttempt_iff (R D : V) (F : V → V → V) (g : V) :
    (IsRecursionAttempt R D F g ∧ domain g = D) ↔
      IsFunction g ∧ domain g = D ∧ ∀ x ∈ D, g ‘ x = F x (g ↾ (predecessors R D x)) := by
  constructor
  · rintro ⟨hg, hd⟩
    exact ⟨hg.1, hd, fun x hx ↦ hg.2.2 x (hd.symm ▸ hx)⟩
  · rintro ⟨hg, hd, hrec⟩
    refine ⟨⟨hg, ⟨?_, ?_⟩, ?_⟩, hd⟩
    · rw [hd]
    · intro x hx y hy
      rw [hd]
      exact (mem_predecessors_iff _ _ _ _).mp hy |>.1
    · intro x hx
      exact hrec x (hd ▸ hx)

end ZFVP
