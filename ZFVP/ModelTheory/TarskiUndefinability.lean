import ZFVP.ModelTheory.SatisfactionClass
import ZFVP.Syntax.PackFiniteParameters

/-! Undefinability of a full satisfaction class, with set parameters allowed.

This is Enayat, "Models of set theory: extensions and dead ends", Theorem 2.8(b). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A ternary relation defined with parameters is defined by a formula with one free parameter,
after coding the three arguments as a single Kuratowski triple. -/
theorem definable_relation₃_one_parameter (S : V → V → V → Prop) (hS : ℒₛₑₜ-relation₃[V] S) :
    ∃ φ : SetTheorySemisentence 2, ∃ p : V,
      ∀ x y z : V, φ.Evalb ![⟨x, ⟨y, z⟩ₖ⟩ₖ, p] ↔ S x y z := by
  haveI := hS
  have hP : ℒₛₑₜ-predicate[V] (fun w : V ↦ ∃ x y z, w = ⟨x, ⟨y, z⟩ₖ⟩ₖ ∧ S x y z) := by
    definability
  obtain ⟨φ, p, hφ⟩ := definable_predicate_one_parameter _ hP
  refine ⟨φ, p, fun x y z ↦ ?_⟩
  rw [hφ]
  constructor
  · rintro ⟨x', y', z', h, hS'⟩
    obtain ⟨rfl, h'⟩ := kpair_inj h
    obtain ⟨rfl, rfl⟩ := kpair_inj h'
    exact hS'
  · exact fun h ↦ ⟨x, y, z, rfl, h⟩

/-- The two element assignment sending `0` to `x` and `1` to `y` is characterised by its
elements. -/
theorem eq_standardTuple_two (x y t : V) :
    (∀ q : V, q ∈ t ↔ (q = ⟨((0 : ℕ) : V), x⟩ₖ ∨ q = ⟨((1 : ℕ) : V), y⟩ₖ)) ↔
      t = standardTuple ![x, y] := by
  constructor
  · intro h
    apply mem_ext
    intro q
    rw [h q, mem_standardTuple_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) i
      · exact Or.inl rfl
      · exact Or.inr rfl
  · rintro rfl q
    rw [mem_standardTuple_iff]
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩

/-- Reads "the coded formula with two free variables whose number is `x`, evaluated at the
assignment sending `0` to `x` and `1` to `y`, is not in the class defined by `φ` with parameter
`y`". The formula has no parameters of its own. -/
def diagonalLiar (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“x y. ¬∃ t,
    (∀ q, q ∈ t ↔ (q = !kpair.dfn (!(numeralFormula 0)) x ∨ q = !kpair.dfn (!(numeralFormula 1)) y))
      ∧ !φ (!kpair.dfn (!(numeralFormula 2)) (!kpair.dfn x t)) y”

theorem eval_diagonalLiar (φ : SetTheorySemisentence 2) (x y : V) :
    (diagonalLiar φ).Evalb ![x, y] ↔
      ¬ φ.Evalb ![⟨((2 : ℕ) : V), ⟨x, standardTuple ![x, y]⟩ₖ⟩ₖ, y] := by
  classical
  have h : (diagonalLiar φ).Evalb ![x, y] ↔
      ∀ t : V, (∃ q : V, ¬(q ∈ t ↔ (q = ⟨((0 : ℕ) : V), x⟩ₖ ∨ q = ⟨((1 : ℕ) : V), y⟩ₖ)))
        ∨ ¬ φ.Evalb ![⟨((2 : ℕ) : V), ⟨x, t⟩ₖ⟩ₖ, y] := by
    simp [diagonalLiar]
  rw [h]
  constructor
  · intro H hev
    rcases H (standardTuple ![x, y]) with ⟨q, hq⟩ | hn
    · exact hq (((eq_standardTuple_two x y _).mpr rfl) q)
    · exact hn hev
  · intro hn t
    by_cases hc : ∀ q : V, q ∈ t ↔ (q = ⟨((0 : ℕ) : V), x⟩ₖ ∨ q = ⟨((1 : ℕ) : V), y⟩ₖ)
    · refine Or.inr ?_
      rw [(eq_standardTuple_two x y t).mp hc]
      exact hn
    · exact Or.inl (not_forall.mp hc)

/-- Enayat, Theorem 2.8(b): a full satisfaction class for a model of ZF is not definable in that
model, even allowing set parameters. -/
theorem no_definable_fullSatisfactionClass (S : V → V → V → Prop)
    (hS : IsFullSatisfactionClass V S) : ¬ (ℒₛₑₜ-relation₃[V] S) := by
  intro hdef
  obtain ⟨φ, p, hφ⟩ := definable_relation₃_one_parameter S hdef
  set θ : SetTheorySemisentence 2 := diagonalLiar φ with hθ
  set g : V := encodeMembershipFormula θ with hg
  have key : S ((2 : ℕ) : V) g (standardTuple ![g, p]) ↔ θ.Evalb ![g, p] :=
    hS.evalb_iff θ ![g, p]
  rw [hθ, eval_diagonalLiar φ g p, hφ] at key
  exact iff_not_self key

end ZFVP
