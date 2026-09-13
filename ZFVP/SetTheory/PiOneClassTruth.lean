import ZFVP.SetTheory.LevelOneTruth
import ZFVP.SetTheory.TransfiniteIteration

/-! Downward absoluteness of a Π₁ formula in two free variables to a transitive set, in the raw
evaluation form and in the internally coded form built on `MembershipSatisfies`, together with a
rank stage of limit height at which the coded form and real truth agree. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Both entries of `![B, a]` lie in `M` once `B` and `a` do. -/
theorem pair_mem_of_mem {M B a : V} (hB : B ∈ M) (ha : a ∈ M) :
    ∀ i, (![B, a] : Fin 2 → V) i ∈ M :=
  fun i ↦ Fin.cases hB (fun j ↦ Fin.cases ha (fun k ↦ Fin.elim0 k) j) i

/-- The tuple of members of `M` built entrywise from `![B, a]` is the pair of the two members. -/
theorem setDomain_pair_eq {M B a : V} (hB : B ∈ M) (ha : a ∈ M) :
    (fun i ↦ (⟨(![B, a] : Fin 2 → V) i, pair_mem_of_mem hB ha i⟩ : SetDomain M))
      = ![⟨B, hB⟩, ⟨a, ha⟩] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i

/-- A Π₁ formula true in `V` of two parameters from a transitive set `M` is true of the same two
parameters read inside `M`. -/
theorem piOne_class_downward (M : V) [IsTransitive M] {φ : SetTheorySemisentence 2}
    (hφ : IsPiFormula 1 φ) {B a : V} (hB : B ∈ M) (ha : a ∈ M) (h : φ.Evalb ![B, a]) :
    φ.Evalb (![⟨B, hB⟩, ⟨a, ha⟩] : Fin 2 → SetDomain M) := by
  have key := pi_one_downward M hφ
    (fun i ↦ (⟨(![B, a] : Fin 2 → V) i, pair_mem_of_mem hB ha i⟩ : SetDomain M)) h
  exact cast (congrArg (fun v : Fin 2 → SetDomain M ↦ φ.Evalb v) (setDomain_pair_eq hB ha)) key

/-- The same statement through the internal satisfaction predicate: if a Π₁ formula holds in `V`
of two parameters lying in a nonempty transitive set `M`, then `M` records it. -/
theorem piOne_class_satisfies_downward (M : V) [IsTransitive M] (hM : IsNonempty M)
    {φ : SetTheorySemisentence 2} (hφ : IsPiFormula 1 φ) {B a : V}
    (hB : B ∈ M) (ha : a ∈ M) (h : φ.Evalb ![B, a]) :
    MembershipSatisfies M ((2 : ℕ) : V) (encodeMembershipFormula φ)
      (standardTuple ![B, a]) := by
  have hcode := membershipSatisfies_encode hM φ
    (fun i ↦ (⟨(![B, a] : Fin 2 → V) i, pair_mem_of_mem hB ha i⟩ : SetDomain M))
  exact hcode.mpr (pi_one_downward M hφ _ h)

/-- An ordinal that is closed under successors and has `ω` below it is a limit ordinal. -/
theorem isLimitOrdinal_of_succ_closed {δ : V} (hδ : IsOrdinal δ) (hω : (ω : V) ∈ δ)
    (hsucc : ∀ ξ ∈ δ, succ ξ ∈ δ) : IsLimitOrdinal δ := by
  refine ⟨hδ, ?_, ?_⟩
  · rintro rfl
    exact not_mem_empty hω
  · rintro ⟨ξ, rfl⟩
    exact mem_irrefl _ (hsucc ξ (mem_succ_self ξ))

/-- A rank stage containing a set is nonempty. -/
theorem isNonempty_hierarchy_of_mem {δ X : V} (hX : X ∈ hierarchy δ) :
    IsNonempty (hierarchy δ) := ⟨⟨X, hX⟩⟩

/-- For any formula in two free variables and any set `X` there is a limit rank stage above `ω`
containing `X` at which the internal satisfaction predicate agrees with real truth on all pairs of
parameters from that stage. No complexity hypothesis on `φ` is needed. -/
theorem piOne_class_reflecting_stage (φ : SetTheorySemisentence 2) (X : V) :
    ∃ δ : V, IsOrdinal δ ∧ IsLimitOrdinal δ ∧ (ω : V) ∈ δ ∧ X ∈ hierarchy δ ∧
      ∀ B a : V, B ∈ hierarchy δ → a ∈ hierarchy δ →
        (MembershipSatisfies (hierarchy δ) ((2 : ℕ) : V) (encodeMembershipFormula φ)
           (standardTuple ![B, a]) ↔ φ.Evalb ![B, a]) := by
  obtain ⟨δ, hδ, hX, hω, hsucc, habs⟩ := finite_formula_reflection_containing [⟨2, φ⟩] X
  have : IsOrdinal δ := hδ
  refine ⟨δ, hδ, isLimitOrdinal_of_succ_closed hδ hω hsucc, hω, hX, ?_⟩
  have hne : IsNonempty (hierarchy δ) := isNonempty_hierarchy_of_mem hX
  intro B a hB ha
  have hcode := membershipSatisfies_encode hne φ
    (fun i ↦ (⟨(![B, a] : Fin 2 → V) i, pair_mem_of_mem hB ha i⟩ : SetDomain (hierarchy δ)))
  have hrefl := habs ⟨2, φ⟩ (by simp)
    (fun i ↦ (⟨(![B, a] : Fin 2 → V) i, pair_mem_of_mem hB ha i⟩ : SetDomain (hierarchy δ)))
  exact hcode.trans hrefl

end ZFVP
