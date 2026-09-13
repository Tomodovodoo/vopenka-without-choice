import ZFVP.ModelTheory.InfinitaryAdequateRequirements
import ZFVP.ModelTheory.InfinitaryDenseRequirementChain

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
open AdequateFiniteCondition
variable {L : Language.{u}} [L.Eq] [L.Encodable]

/-- An actual refining chain meeting the semantic requirements over any adequate model. -/
structure AdequateGenericChain (M : WeakModel.{u,v} L) (S : Set (TaggedFormula L))
    (p₀ : AdequateFiniteCondition M S) where
  adequate : M.Adequate S
  point : ℕ → AdequateFiniteCondition M S
  initial : point 0 = p₀
  refines : ∀ {k m}, k ≤ m → Refines (point k) (point m)
  arity_unbounded : ∀ N, ∃ k, ∀ m, k ≤ m → N ≤ (point m).1
  decides : ∀ {n} (φ : ParameterInstance M S n),
    ∃ k, ∀ m, k ≤ m → Forces (point m) φ ∨ Forces (point m) φ.neg
  conjunction : ∀ {n} (s : ParameterSequence M S n),
    ∃ k, ∀ m, k ≤ m → Forces (point m) s.conj ∨ ∃ i, Forces (point m) (s.component i).neg
  existential : ∀ {n} (φ : ParameterInstance M S (n + 1)),
    ∃ k, ∀ m, k ≤ m → Forces (point m) φ.exs.neg ∨ HasWitness (point m) φ
  freezes : ∀ {n} (i : Fin n) (ψ : ParameterInstance M S 1),
    ¬M.Q {x | ψ.Eval (x :> Fin.elim0)} →
      ∃ k, ∀ m, k ≤ m → Freezes (point m) i ψ
  avoids : ∀ a : M.Domain, ∃ k, ∀ m, k ≤ m → Avoids (point m) a

namespace AdequateGenericChain
variable {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

private abbrev Requirement (M : WeakModel.{u,v} L) (S : Set (TaggedFormula L)) :=
  (Σ n, ParameterInstance M S n) ⊕ (Σ n, ParameterSequence M S n) ⊕
    (Σ n, ParameterInstance M S (n + 1)) ⊕
    ((Σ n, Fin n) × ParameterInstance M S 1) ⊕ M.Domain ⊕ ℕ

private def Meets : Requirement M S → AdequateFiniteCondition M S → Prop
  | .inl a, p => Forces p a.2 ∨ Forces p a.2.neg
  | .inr (.inl a), p => Forces p a.2.conj ∨ ∃ i, Forces p (a.2.component i).neg
  | .inr (.inr (.inl a)), p => Forces p a.2.exs.neg ∨ HasWitness p a.2
  | .inr (.inr (.inr (.inl a))), p => ¬M.Q {x | a.2.Eval (x :> Fin.elim0)} → Freezes p a.1.2 a.2
  | .inr (.inr (.inr (.inr (.inl a)))), p => Avoids p a
  | .inr (.inr (.inr (.inr (.inr N)))), p => N ≤ p.1

private theorem meets_persistent (i : Requirement M S) {p q : AdequateFiniteCondition M S}
    (hpq : Refines p q) (hp : Meets i p) : Meets i q := by
  rcases i with a | a | a | a | u | N
  · exact hp.imp (forces_persistent hpq) (forces_persistent hpq)
  · exact hp.imp (forces_persistent hpq) (fun ⟨i, hi⟩ ↦ ⟨i, forces_persistent hpq hi⟩)
  · exact hp.imp (forces_persistent hpq) (hasWitness_persistent hpq)
  · exact fun hs ↦ freezes_persistent hpq (hp hs)
  · exact avoids_persistent hpq hp
  · exact hp.trans hpq.choose

private theorem meets_dense (hM : M.Adequate S) (i : Requirement M S) (p : AdequateFiniteCondition M S) :
    ∃ q, Refines p q ∧ Meets i q := by
  classical
  rcases i with a | a | a | a | u | N
  · exact decide_dense hM p a.2
  · exact conjunction_dense hM p a.2
  · exact existential_dense hM p a.2
  · by_cases hs : ¬M.Q {x | a.2.Eval (x :> Fin.elim0)}
    · obtain ⟨q, hpq, hq⟩ := freezing_dense hM p a.1.2 a.2 hs
      exact ⟨q, hpq, fun _ ↦ hq⟩
    · exact ⟨p, refines_refl p, fun h ↦ (hs h).elim⟩
  · exact avoidance_dense hM p u
  · exact exists_raise p N

theorem exists_chain (hM : M.Adequate S) (hS : S.Countable) (p₀ : AdequateFiniteCondition M S) :
    Nonempty (AdequateGenericChain M S p₀) := by
  classical
  have (n : ℕ) : Countable (ParameterInstance M S n) := ParameterInstance.countable hS n
  have (n : ℕ) : Countable (ParameterSequence M S n) := ParameterSequence.countable hS n
  obtain ⟨C⟩ := exists_denseRequirementChain (I := Requirement M S) Refines Meets
    refines_refl (fun hpq hqr ↦ refines_trans hpq hqr) meets_persistent (meets_dense hM) p₀
  refine ⟨{
    adequate := hM
    point := C.point
    initial := C.initial
    refines := C.refines
    arity_unbounded := ?_
    decides := ?_
    conjunction := ?_
    existential := ?_
    freezes := ?_
    avoids := ?_ }⟩
  · intro N
    exact C.eventually_meets (.inr (.inr (.inr (.inr (.inr N)))))
  · intro n φ
    exact C.eventually_meets (.inl ⟨n, φ⟩)
  · intro n s
    exact C.eventually_meets (.inr (.inl ⟨n, s⟩))
  · intro n φ
    exact C.eventually_meets (.inr (.inr (.inl ⟨n, φ⟩)))
  · intro n i ψ hs
    obtain ⟨k, hk⟩ := C.eventually_meets (.inr (.inr (.inr (.inl (⟨n, i⟩, ψ)))))
    exact ⟨k, fun m hm ↦ hk m hm hs⟩
  · intro a
    exact C.eventually_meets (.inr (.inr (.inr (.inr (.inl a)))))

end AdequateGenericChain
end WeakModel
end ZFVP.Infinitary
