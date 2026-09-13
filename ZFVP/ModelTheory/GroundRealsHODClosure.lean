import ZFVP.ModelTheory.GroundRealsHOD

/-! Closure of ordinal definability from ground sets and reals: a set definable from a definable
set is definable. The composite formula `∃ w (∀ y (y ∈ w ↔ φ(y, v)) ∧ ψ(b, w))` substitutes the
definition of the parameter. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The membership atom `x ∈ y`. -/
def memAtom : SetTheorySemisentence 2 := “x y. x ∈ y”

/-- `∃ w, (∀ y, y ∈ w ↔ φ(y, v)) ∧ ψ(b, w)`, with free variables `b, v`. -/
def definedFrom {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (ψ : SetTheorySemisentence 2) :
    SetTheorySemisentence (n + 1) :=
  ∃¹ ((∀¹ (((∼(memAtom.subst ![#0, #1])) ⋎
        (φ.subst (#0 :> fun i ↦ #i.succ.succ.succ))) ⋏
      ((∼(φ.subst (#0 :> fun i ↦ #i.succ.succ.succ))) ⋎
        (memAtom.subst ![#0, #1])))) ⋏
    (ψ.subst ![#1, #0]))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_definedFrom {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (ψ : SetTheorySemisentence 2)
    (b : V) (v : Fin n → V) :
    (definedFrom φ ψ).Evalb (b :> v) ↔
      ∃ w : V, (∀ y, y ∈ w ↔ φ.Evalb (y :> v)) ∧ ψ.Evalb ![b, w] := by
  simp [definedFrom, memAtom, Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton]
  constructor
  · rintro ⟨w, hw, hψ⟩
    exact ⟨w, fun y ↦ ⟨fun hy ↦ (hw y).1.resolve_left (not_not.mpr hy),
      fun hφ ↦ (hw y).2.resolve_left (not_not.mpr hφ)⟩, hψ⟩
  · rintro ⟨w, hw, hψ⟩
    refine ⟨w, fun y ↦ ⟨?_, ?_⟩, hψ⟩
    · by_cases hy : y ∈ w
      · exact Or.inr ((hw y).mp hy)
      · exact Or.inl hy
    · by_cases hφ : φ.Evalb (y :> v)
      · exact Or.inr ((hw y).mpr hφ)
      · exact Or.inl hφ

namespace ForcingContext

variable {A : ForcingContext V}

/-- A set definable from a definable set is definable. -/
theorem groundRealDefinable_of_definable_from {x C : A.Model} (hx : A.IsGroundRealDefinable x)
    (ψ : SetTheorySemisentence 2) (hC : ∀ b, b ∈ C ↔ ψ.Evalb ![b, x]) :
    A.IsGroundRealDefinable C := by
  obtain ⟨n, φ, v, hv, hdef⟩ := hx
  refine ⟨n, definedFrom φ ψ, v, hv, fun b ↦ ?_⟩
  rw [eval_definedFrom, hC]
  constructor
  · intro h
    exact ⟨x, fun y ↦ hdef y, h⟩
  · rintro ⟨w, hw, hψ⟩
    have hwx : w = x := by
      apply mem_ext
      intro y
      rw [hw y, hdef y]
    rw [hwx] at hψ
    exact hψ

end ForcingContext

end ZFVP
