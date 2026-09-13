import ZFVP.SetTheory.Rank
import ZFVP.SetTheory.UniformRecursion
import ZFVP.SetTheory.ElementaryMap

/-! Uniform rank definition and its preservation by elementary maps. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankFormula : SetTheorySemisentence 2 :=
  f“α x. !IsOrdinal.dfn α ∧ x ⊆ !hierarchyFormula α ∧
    ∀ β, !IsOrdinal.dfn β → x ⊆ !hierarchyFormula β → α ⊆ β”

variable {V W : Type*} [SetStructure V] [SetStructure W]

instance rankFormula_defined [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    ℒₛₑₜ-function₁[V] rank via rankFormula := ⟨fun v ↦ by
  change rankFormula.Evalb v ↔ v 0 = rank (v 1)
  rw [eq_comm, rank_eq_iff]
  simp [rankFormula, IsRank, IsLeastOrdinal]⟩

namespace ElementaryMap

theorem map_defined {k : ℕ} (j : ElementaryMap V W) (φ : SetTheorySemisentence k)
    (P : (Fin k → V) → Prop) (Q : (Fin k → W) → Prop)
    [Defined P φ] [Defined Q φ] (b : Fin k → V) : P b ↔ Q (j ∘ b) := by
  have h := j.elementary φ b (Empty.elim : Empty → V)
  have hf : j ∘ (Empty.elim : Empty → V) = (Empty.elim : Empty → W) := by
    funext x
    exact Empty.elim x
  change φ.Evalb b ↔ φ.Eval (j ∘ b) (j ∘ Empty.elim) at h
  rw [hf] at h
  exact (Defined.eval_iff b).symm.trans (h.trans (Defined.eval_iff (j ∘ b)))

theorem map_definedFunction₁ (j : ElementaryMap V W) (φ : SetTheorySemisentence 2)
    (F : V → V) (G : W → W)
    [ℒₛₑₜ-function₁ F via φ] [ℒₛₑₜ-function₁ G via φ] (x : V) :
    j (F x) = G (j x) := by
  have h := j.map_defined φ (fun v ↦ v 0 = F (v 1))
    (fun v ↦ v 0 = G (v 1)) ![F x, x]
  exact h.mp rfl

variable [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_hierarchy (j : ElementaryMap V W) (α : V) :
    j (hierarchy α) = hierarchy (j α) :=
  j.map_definedFunction₁ hierarchyFormula hierarchy hierarchy α

theorem map_rank (j : ElementaryMap V W) (x : V) : j (rank x) = rank (j x) :=
  j.map_definedFunction₁ rankFormula rank rank x

omit [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem map_ordinal_iff (j : ElementaryMap V W) (α : V) :
    IsOrdinal (j α) ↔ IsOrdinal α :=
  (j.map_defined IsOrdinal.dfn (fun v ↦ IsOrdinal (v 0))
    (fun v ↦ IsOrdinal (v 0)) ![α]).symm

end ElementaryMap
end ZFVP
