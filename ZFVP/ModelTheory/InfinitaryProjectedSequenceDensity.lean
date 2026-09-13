import ZFVP.ModelTheory.InfinitaryFiniteProjection

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  (H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S)))

theorem sequence_conj_exsN_closed (k : ℕ) {n} {f : ℕ → Formula (limit L) (n + k)}
    (hf : ⟨n + k, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ⟨n, .conj fun i ↦ Formula.exsN k (f i)⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) := by
  rw [SequenceClosure.base_carrier_eq] at hf ⊢
  exact SequenceClosure.conj_exsN_closed k hf

/-- Finite existential projection preserves the countable-conjunction density
needed when a condition already contains auxiliary witness variables. -/
theorem q_mem_projected_conjunction_split (k : ℕ) {φ : Formula (limit L) (1 + k)}
    {f : ℕ → Formula (limit L) (1 + k)}
    (hφ : ⟨1 + k, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hf : ⟨1 + k, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hq : .q (Formula.exsN k φ) ∈ H.carrier) :
    .q (Formula.exsN k (φ.and (.conj f))) ∈ H.carrier ∨
      ∃ i, .q (Formula.exsN k (φ.and (.neg (f i)))) ∈ H.carrier := by
  rcases H.q_mem_projected_split k hφ hf hq with h | h
  · exact Or.inl h
  right
  let g : ℕ → Formula (limit L) (1 + k) := fun i ↦ φ.and (.neg (f i))
  have hg : ⟨1 + k, .conj g⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) :=
    sequence_conj_and_closed (sequence_conj_neg_closed hf) hφ
  have hdg := sequence_disj_closed hg
  have hp := sequence_conj_exsN_closed k hg
  have hd := sequence_disj_closed hp
  have hpi (i : ℕ) := sequence_member_closed hp i
  have he : H.fiber (Formula.exsN k (φ.and (.neg (.conj f)))) =
      H.fiber (Formula.disj fun i ↦ Formula.exsN k (g i)) := by
    ext x
    rw [H.fiber_weakEval (exsN_closed k (and_closed hφ (neg_closed hf))), H.fiber_weakEval hd]
    refine (Formula.weakEval_exsN_congr H.weakQuantifier k
      (ψ := Formula.disj g) (fun b ↦ ?_) _).trans ?_
    · simp only [Formula.weakEval_and, Formula.weakEval_neg, Formula.weakEval_conj,
        Formula.weakEval_disj, g, not_forall, exists_and_left]
    · rw [Formula.weakEval_exsN_disj, Formula.weakEval_disj]
  exact (H.q_mem_disj_iff _ hd hpi (sequence_q_disj_closed hp)).mp
    ((H.q_mem_extensional (exsN_closed k (and_closed hφ (neg_closed hf))) hd he).mp h)

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary
