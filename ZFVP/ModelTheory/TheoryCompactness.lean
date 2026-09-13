import Foundation.FirstOrder.Basic.Soundness

/-!
# Compactness for first-order theories

The step of the paper's Theorem B that turns satisfiability of every finite subset of a theory
into consistency of the whole theory.

Nothing here is specific to the language of set theory, so both results are stated for an
arbitrary language `L` and an arbitrary theory `T : Theory L`.

The proof is syntactic. A derivation of an inconsistency from `T` mentions only finitely many
axioms (`LO.FirstOrder.Theory.Proof.inconsistent_iff`), so the finite subset of `T` collecting
those axioms is already inconsistent; soundness then makes it unsatisfiable, contradicting the
hypothesis.
-/

namespace ZFVP

open LO LO.FirstOrder Entailment

universe v w

variable {L : Language.{w}}

/-- If every finite subset of `T` has a model, then `T` is consistent. -/
theorem consistent_of_finite_subsets_satisfiable {T : Theory L}
    (h : ∀ u : Finset (Sentence L), ↑u ⊆ T →
      Semantics.Satisfiable (Struc.{v, w} L) (u : Theory L)) :
    Entailment.Consistent T := by
  classical
  by_contra hcon
  have hinc : Entailment.Inconsistent T := Entailment.not_consistent_iff_inconsistent.mp hcon
  obtain ⟨Γ, hΓ, hd⟩ := Theory.Proof.inconsistent_iff.mp hinc
  set u : Finset (Sentence L) := Γ.toFinset with hu
  have hsub : (u : Theory L) ⊆ T := by
    intro ψ hψ
    exact hΓ ψ (by simpa [hu] using hψ)
  have hincu : Entailment.Inconsistent (u : Theory L) :=
    Theory.Proof.inconsistent_iff.mpr ⟨Γ, fun ψ hψ => by simpa [hu] using hψ, hd⟩
  exact (Theory.consistent_of_satisfiable (h u hsub)).not_inconsistent hincu

/-- Packaged form of `consistent_of_finite_subsets_satisfiable`: a model for every finite subset,
given as an explicit type with a structure on it, makes `T` consistent. -/
theorem consistent_of_finite_subsets_models {T : Theory L}
    (h : ∀ u : Finset (Sentence L), ↑u ⊆ T →
      ∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M), M↓[L] ⊧* (u : Theory L)) :
    Entailment.Consistent T :=
  consistent_of_finite_subsets_satisfiable.{v} fun u hu => satisfiable_iff.mpr (h u hu)

end ZFVP
