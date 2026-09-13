import Foundation.FirstOrder.SetTheory.ZF
import Foundation.FirstOrder.SetTheory.Function

/-!
Internal graphs of definable functions, for dependency B03.

The ambient function is not assumed to be an element of the model. Replacement
constructs its graph over an internal set. The explicit definability hypothesis
is the hypothesis required by the ZF Replacement scheme.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The internal graph of a definable function restricted to an internal set. -/
noncomputable def definableGraph (X : V) (F : V → V)
    (hF : ℒₛₑₜ-function₁ F) : V :=
  repl (fun x ↦ ⟨x, F x⟩ₖ) (by definability) X

theorem mem_definableGraph_iff (X : V) (F : V → V)
    (hF : ℒₛₑₜ-function₁ F) (p : V) :
    p ∈ definableGraph X F hF ↔ ∃ x ∈ X, p = ⟨x, F x⟩ₖ := by
  exact repl_spec (by definability)

theorem pair_mem_definableGraph_iff (X : V) (F : V → V)
    (hF : ℒₛₑₜ-function₁ F) (x y : V) :
    ⟨x, y⟩ₖ ∈ definableGraph X F hF ↔ x ∈ X ∧ y = F x := by
  simp only [mem_definableGraph_iff, kpair_iff]
  constructor
  · rintro ⟨z, hz, hx, hy⟩
    subst z
    exact ⟨hz, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, rfl, hy⟩

theorem domain_definableGraph (X : V) (F : V → V)
    (hF : ℒₛₑₜ-function₁ F) : domain (definableGraph X F hF) = X := by
  ext x
  simp only [mem_domain_iff, pair_mem_definableGraph_iff]
  exact ⟨fun ⟨_, hx, _⟩ ↦ hx, fun hx ↦ ⟨F x, hx, rfl⟩⟩

theorem range_definableGraph (X : V) (F : V → V)
    (hF : ℒₛₑₜ-function₁ F) : range (definableGraph X F hF) = repl F hF X := by
  ext y
  simp only [mem_range_iff, pair_mem_definableGraph_iff, repl_spec]

end ZFVP
