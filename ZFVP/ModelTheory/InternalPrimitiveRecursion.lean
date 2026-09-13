import ZFVP.ModelTheory.InternalNaturalUnpairing
import Mathlib.Computability.Primrec.Basic

/-! Primitive recursion with a carried parameter on every internal natural number. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def naturalPrimitiveStepFormula (φ ψ : SetTheorySemisentence 2) : SetTheorySemisentence 3 :=
  f“r z g. (!domain.dfn g = !isEmpty ∧ r = !φ z) ∨
    (!domain.dfn g ≠ !isEmpty ∧ r = !ψ (!naturalSquarePairFormula z
      (!naturalSquarePairFormula (!sUnion.dfn (!domain.dfn g))
        (!value.dfn g (!sUnion.dfn (!domain.dfn g))))))”

def naturalPrimitiveFormula (φ ψ : SetTheorySemisentence 2) : SetTheorySemisentence 3 :=
  parameterRecursionFormula (naturalPrimitiveStepFormula φ ψ)

def naturalPrecFormula (φ ψ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“y p. y = !(naturalPrimitiveFormula φ ψ) (!naturalSquareLeftFormula p) (!naturalSquareRightFormula p)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def naturalPrimitiveStep (F G : V → V) (z g : V) : V := by
  classical
  exact if domain g = 0 then F z else
    G (naturalSquarePair z (naturalSquarePair (⋃ˢ domain g) (g ‘ (⋃ˢ domain g))))

instance naturalPrimitiveStep_defined (F G : V → V) (φ ψ : SetTheorySemisentence 2)
    [ℒₛₑₜ-function₁ F via φ] [ℒₛₑₜ-function₁ G via ψ] :
    ℒₛₑₜ-function₂ (naturalPrimitiveStep F G) via naturalPrimitiveStepFormula φ ψ :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = 0
    · simp_all [naturalPrimitiveStepFormula, naturalPrimitiveStep, zero_def]
    · simp_all [naturalPrimitiveStepFormula, naturalPrimitiveStep, zero_def, -ne_empty_iff_isNonempty]⟩

theorem naturalPrimitiveStep_definable (F G : V → V)
    (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G) : ℒₛₑₜ-function₂ (naturalPrimitiveStep F G) := by
  have h : ℒₛₑₜ-relation₃ (fun r z g : V ↦
      (domain g = 0 ∧ r = F z) ∨
      (domain g ≠ 0 ∧ r = G (naturalSquarePair z (naturalSquarePair (⋃ˢ domain g) (g ‘ (⋃ˢ domain g)))))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = naturalPrimitiveStep F G (v 1) (v 2) ↔ _
  unfold naturalPrimitiveStep
  split <;> simp_all

noncomputable def naturalPrimitive (F G : V → V)
    (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G) (z n : V) : V :=
  parameterRecursion (naturalPrimitiveStep F G) (naturalPrimitiveStep_definable F G hF hG) z n

instance naturalPrimitive_defined (F G : V → V) (φ ψ : SetTheorySemisentence 2)
    [hF : ℒₛₑₜ-function₁ F via φ] [hG : ℒₛₑₜ-function₁ G via ψ] :
    ℒₛₑₜ-function₂ (naturalPrimitive F G hF.to_definable hG.to_definable) via naturalPrimitiveFormula φ ψ :=
  parameterRecursionFormula_defined (naturalPrimitiveStep F G) (naturalPrimitiveStepFormula φ ψ)

theorem naturalPrimitive_definable (F G : V → V)
    (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G) (z : V) :
    ℒₛₑₜ-function₁ (naturalPrimitive F G hF hG z) :=
  Replacement.transfiniteRec_definable
    (by have := naturalPrimitiveStep_definable F G hF hG; definability)

theorem naturalPrimitive_zero (F G : V → V) (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G) (z : V) :
    naturalPrimitive F G hF hG z 0 = F z := by
  have hr := Replacement.transfiniteRec_spec (naturalPrimitiveStep F G z)
    (by have := naturalPrimitiveStep_definable F G hF hG; definability) (IsOrdinal.toOrdinal (0 : V))
  change naturalPrimitive F G hF hG z 0 = naturalPrimitiveStep F G z
    (definableGraph 0 (naturalPrimitive F G hF hG z) (naturalPrimitive_definable F G hF hG z)) at hr
  simpa [naturalPrimitiveStep, domain_definableGraph] using hr

theorem naturalPrimitive_succ (F G : V → V) (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G)
    (z : V) {n : V} (hn : n ∈ (ω : V)) :
    naturalPrimitive F G hF hG z (succ n) =
      G (naturalSquarePair z (naturalSquarePair n (naturalPrimitive F G hF hG z n))) := by
  let := IsOrdinal.of_mem hn
  have hr := Replacement.transfiniteRec_spec (naturalPrimitiveStep F G z)
    (by have := naturalPrimitiveStep_definable F G hF hG; definability) (IsOrdinal.toOrdinal (succ n))
  change naturalPrimitive F G hF hG z (succ n) = naturalPrimitiveStep F G z
    (definableGraph (succ n) (naturalPrimitive F G hF hG z) (naturalPrimitive_definable F G hF hG z)) at hr
  have hne : succ n ≠ (0 : V) := by
    intro h
    have hm : n ∈ succ n := by simp
    rw [h] at hm
    exact not_mem_empty hm
  simpa [naturalPrimitiveStep, domain_definableGraph, hne, sUnion_succ_of_transitive,
    value_definableGraph _ _ _ (show n ∈ succ n by simp)] using hr

theorem naturalPrimitive_natural (F G : V → V) (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G)
    (hFω : ∀ x ∈ (ω : V), F x ∈ (ω : V)) (hGω : ∀ x ∈ (ω : V), G x ∈ (ω : V))
    {z n : V} (hz : z ∈ (ω : V)) (hn : n ∈ (ω : V)) : naturalPrimitive F G hF hG z n ∈ (ω : V) := by
  have := naturalPrimitive_definable F G hF hG z
  apply naturalNumber_induction (fun n ↦ naturalPrimitive F G hF hG z n ∈ (ω : V)) (by definability) ?_ ?_ n hn
  · rw [naturalPrimitive_zero]
    exact hFω z hz
  · intro n hn ih
    rw [naturalPrimitive_succ _ _ _ _ _ hn]
    exact hGω _ (naturalSquarePair_natural hz (naturalSquarePair_natural hn ih))

theorem naturalPrimitive_natCast (F G : V → V) (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G)
    (f g : ℕ → ℕ) (hFs : ∀ n : ℕ, F (n : V) = (f n : V)) (hGs : ∀ n : ℕ, G (n : V) = (g n : V))
    (z n : ℕ) : naturalPrimitive F G hF hG (z : V) (n : V) =
      ((Nat.rec (f z) (fun y r ↦ g (Nat.pair z (Nat.pair y r))) n : ℕ) : V) := by
  induction n with
  | zero =>
    change naturalPrimitive F G hF hG (z : V) 0 = (f z : V)
    rw [naturalPrimitive_zero]
    exact hFs z
  | succ n ih =>
    rw [num_succ_def, naturalPrimitive_succ _ _ _ _ _ (by simp), ih,
      naturalSquarePair_natCast, naturalSquarePair_natCast, hGs]

noncomputable def naturalPrec (F G : V → V) (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G) (p : V) : V :=
  naturalPrimitive F G hF hG (naturalSquareLeft p) (naturalSquareRight p)

instance naturalPrec_defined (F G : V → V) (φ ψ : SetTheorySemisentence 2)
    [hF : ℒₛₑₜ-function₁ F via φ] [hG : ℒₛₑₜ-function₁ G via ψ] :
    ℒₛₑₜ-function₁ (naturalPrec F G hF.to_definable hG.to_definable) via naturalPrecFormula φ ψ :=
  ⟨fun v ↦ by simp [naturalPrecFormula, naturalPrec]⟩

theorem naturalPrec_natural (F G : V → V) (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G)
    (hFω : ∀ x ∈ (ω : V), F x ∈ (ω : V)) (hGω : ∀ x ∈ (ω : V), G x ∈ (ω : V)) (p : V) :
    naturalPrec F G hF hG p ∈ (ω : V) :=
  naturalPrimitive_natural F G hF hG hFω hGω (naturalSquareLeft_natural p) (naturalSquareRight_natural p)

theorem naturalPrec_natCast (F G : V → V) (hF : ℒₛₑₜ-function₁ F) (hG : ℒₛₑₜ-function₁ G)
    (f g : ℕ → ℕ) (hFs : ∀ n : ℕ, F (n : V) = (f n : V)) (hGs : ∀ n : ℕ, G (n : V) = (g n : V))
    (p : ℕ) : naturalPrec F G hF hG (p : V) =
      ((Nat.unpaired (fun z n ↦ Nat.rec (f z) (fun y r ↦ g (Nat.pair z (Nat.pair y r))) n) p : ℕ) : V) := by
  unfold naturalPrec naturalSquareLeft naturalSquareRight
  rw [naturalSquareUnpair_natCast]
  exact naturalPrimitive_natCast F G hF hG f g hFs hGs _ _

end ZFVP
