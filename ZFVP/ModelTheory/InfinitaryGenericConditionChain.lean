import ZFVP.ModelTheory.InfinitaryConditionFreezing
import ZFVP.ModelTheory.InfinitaryConditionWitness
import ZFVP.ModelTheory.InfinitaryDenseRequirementChain

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}

/-- A refining sequence that eventually meets every finite-condition requirement. -/
structure GenericConditionChain
    (H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S)))
    (p₀ : H.FiniteCondition) where
  point : ℕ → H.FiniteCondition
  initial : point 0 = p₀
  refines : ∀ {k m}, k ≤ m → Refines (point k) (point m)
  arity_unbounded : ∀ N, ∃ k, ∀ m, k ≤ m → N ≤ (point m).1
  decides : ∀ {n} (φ : Formula (limit L) n),
    ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
      ∃ k, ∀ m, k ≤ m → Forces (point m) φ ∨ Forces (point m) (.neg φ)
  conjunction : ∀ {n} (f : ℕ → Formula (limit L) n),
    ⟨n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
      ∃ k, ∀ m, k ≤ m → Forces (point m) (.conj f) ∨ ∃ i, Forces (point m) (.neg (f i))
  existential : ∀ {n} (φ : Formula (limit L) (n + 1)),
    ⟨n, .exs φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
      ∃ k, ∀ m, k ≤ m → Forces (point m) (.neg (.exs φ)) ∨ HasWitness (point m) φ
  freezes : ∀ {n} (t : Semiterm (limit L) Empty n) (ψ : Formula (limit L) 1),
    ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) → .q ψ ∉ H.carrier →
      ∃ k, ∀ m, k ≤ m → Freezes (point m) t ψ
  avoids : ∀ u : Semiterm (limit L) Empty 0,
    ∃ k, ∀ m, k ≤ m → Avoids (point m) u

namespace GenericConditionChain
variable {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

private def ConjunctionMeets {n} (φ : Formula (limit L) n) (p : H.FiniteCondition) : Prop :=
  match φ with
  | .conj f => Forces p (.conj f) ∨ ∃ i, Forces p (.neg (f i))
  | _ => True

private def ExistentialMeets {n} (φ : Formula (limit L) n) (p : H.FiniteCondition) : Prop :=
  match φ with
  | .exs ψ => Forces p (.neg (.exs ψ)) ∨ HasWitness p ψ
  | _ => True

private theorem conjunctionMeets_persistent {n} (φ : Formula (limit L) n)
    {p q : H.FiniteCondition} (hpq : Refines p q) (hp : ConjunctionMeets φ p) :
    ConjunctionMeets φ q := by
  cases φ with
  | conj f =>
    rcases hp with hp | ⟨i, hp⟩
    · exact Or.inl (forces_persistent hpq hp)
    · exact Or.inr ⟨i, forces_persistent hpq hp⟩
  | _ => trivial

private theorem existentialMeets_persistent {n} (φ : Formula (limit L) n)
    {p q : H.FiniteCondition} (hpq : Refines p q) (hp : ExistentialMeets φ p) :
    ExistentialMeets φ q := by
  cases φ with
  | exs ψ => exact hp.imp (forces_persistent hpq) (hasWitness_persistent hpq)
  | _ => trivial

private theorem conjunctionMeets_dense {n} (φ : Formula (limit L) n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (p : H.FiniteCondition) : ∃ q, Refines p q ∧ ConjunctionMeets φ q := by
  cases φ with
  | conj f => exact conjunction_dense p hφ
  | _ => exact ⟨p, refines_refl p, trivial⟩

private theorem existentialMeets_dense {n} (φ : Formula (limit L) n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (p : H.FiniteCondition) : ∃ q, Refines p q ∧ ExistentialMeets φ q := by
  cases φ with
  | exs ψ =>
    exact existential_dense p (subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas ψ)))
  | _ => exact ⟨p, refines_refl p, trivial⟩

private abbrev FragmentFormula (S : Set (TaggedFormula (limit L))) :=
  {a : TaggedFormula (limit L) // a ∈ FragmentClosure.carrier (SequenceClosure.carrier S)}

private abbrev UnaryFormula (S : Set (TaggedFormula (limit L))) :=
  {ψ : Formula (limit L) 1 // ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)}

private abbrev Requirement (S : Set (TaggedFormula (limit L))) :=
  FragmentFormula S ⊕ FragmentFormula S ⊕ FragmentFormula S ⊕
    ((Σ n, Semiterm (limit L) Empty n) × UnaryFormula S) ⊕ Semiterm (limit L) Empty 0 ⊕ ℕ

private def Meets : Requirement S → H.FiniteCondition → Prop
  | .inl a, p => Forces p a.1.2 ∨ Forces p (.neg a.1.2)
  | .inr (.inl a), p => ConjunctionMeets a.1.2 p
  | .inr (.inr (.inl a)), p => ExistentialMeets a.1.2 p
  | .inr (.inr (.inr (.inl a))), p => .q a.2.1 ∉ H.carrier → Freezes p a.1.2 a.2.1
  | .inr (.inr (.inr (.inr (.inl u)))), p => Avoids p u
  | .inr (.inr (.inr (.inr (.inr N)))), p => N ≤ p.1

private theorem meets_persistent (i : Requirement S) {p q : H.FiniteCondition}
    (hpq : Refines p q) (hp : Meets i p) : Meets i q := by
  rcases i with a | a | a | a | u | N
  · exact hp.imp (forces_persistent hpq) (forces_persistent hpq)
  · exact conjunctionMeets_persistent _ hpq hp
  · exact existentialMeets_persistent _ hpq hp
  · exact fun hs ↦ freezes_persistent hpq (hp hs)
  · exact avoids_persistent hpq hp
  · exact hp.trans hpq.choose

private theorem meets_dense (i : Requirement S) (p : H.FiniteCondition) :
    ∃ q, Refines p q ∧ Meets i q := by
  classical
  rcases i with a | a | a | a | u | N
  · exact decide_dense p a.2
  · exact conjunctionMeets_dense _ a.2 p
  · exact existentialMeets_dense _ a.2 p
  · by_cases hs : .q a.2.1 ∉ H.carrier
    · obtain ⟨q, hpq, hq⟩ := freezes_dense p a.1.2 a.2.2 hs
      exact ⟨q, hpq, fun _ ↦ hq⟩
    · exact ⟨p, refines_refl p, fun h ↦ (hs h).elim⟩
  · exact avoids_dense p u
  · exact exists_raise p N

/-- The countable fragment and the encoded terms supply all scheduling indices. -/
theorem exists_genericConditionChain (hS : S.Countable) (p₀ : H.FiniteCondition) :
    Nonempty (GenericConditionChain H p₀) := by
  classical
  have hT := FragmentClosure.carrier_countable (SequenceClosure.carrier_countable hS)
  let : Countable (FragmentFormula S) := hT.to_subtype
  let : Countable (UnaryFormula S) := Function.Injective.countable
    (f := fun ψ : UnaryFormula S ↦ (⟨⟨1, ψ.1⟩, ψ.2⟩ : FragmentFormula S)) (by
      intro a b h
      apply Subtype.ext
      simpa using congrArg Subtype.val h)
  obtain ⟨C⟩ := exists_denseRequirementChain (I := Requirement S) Refines Meets
    refines_refl (fun hpq hqr ↦ refines_trans hpq hqr) meets_persistent meets_dense p₀
  refine ⟨{
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
  · intro n φ hφ
    exact C.eventually_meets (.inl ⟨⟨n, φ⟩, hφ⟩)
  · intro n f hf
    exact C.eventually_meets (.inr (.inl ⟨⟨n, .conj f⟩, hf⟩))
  · intro n φ hφ
    exact C.eventually_meets (.inr (.inr (.inl ⟨⟨n, .exs φ⟩, hφ⟩)))
  · intro n t ψ hψ hs
    obtain ⟨k, hk⟩ := C.eventually_meets (.inr (.inr (.inr (.inl (⟨n, t⟩, ⟨ψ, hψ⟩)))))
    exact ⟨k, fun m hm ↦ hk m hm hs⟩
  · intro u
    exact C.eventually_meets (.inr (.inr (.inr (.inr (.inl u)))))

end GenericConditionChain
end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary
