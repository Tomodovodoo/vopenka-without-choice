import ZFVP.ModelTheory.InfinitarySequenceClosure
import ZFVP.ModelTheory.InfinitaryHenkinQDensity

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction
open HenkinLanguage
variable {L : Language} [L.Eq] [L.Encodable]

theorem exists_sequenceFragmentExtension (Γ : Set (Sentence L))
    (hc : KeislerDerivation.Consistent Γ) (hΓ : Γ.Countable)
    (S : Set (TaggedFormula (limit L))) (hS : S.Countable)
    (hfinite : ∀ a ∈ S, FiniteSupport a.2) :
    Nonempty (FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))) :=
  exists_closedFragmentExtension Γ hc hΓ _ (SequenceClosure.carrier_countable hS)
    (fun _ ha ↦ SequenceClosure.carrier_supported hfinite ha)

namespace FragmentExtension
open FragmentClosure
variable {Γ : Set (Sentence L)} {S : Set (TaggedFormula (limit L))}
  (H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S)))

theorem sequence_conj_neg_closed {n} {f : ℕ → Formula (limit L) n}
    (hf : ⟨n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ⟨n, .conj fun i ↦ .neg (f i)⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) := by
  rw [SequenceClosure.base_carrier_eq] at hf ⊢
  exact SequenceClosure.conj_neg_closed hf

theorem sequence_disj_closed {n} {f : ℕ → Formula (limit L) n}
    (hf : ⟨n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ⟨n, Formula.disj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) := by
  rw [SequenceClosure.base_carrier_eq] at hf ⊢
  exact SequenceClosure.conj_disj_closed hf

theorem sequence_q_disj_closed {n} {f : ℕ → Formula (limit L) (n + 1)}
    (hf : ⟨n + 1, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ⟨n, Formula.disj fun i ↦ .q (f i)⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) := by
  rw [SequenceClosure.base_carrier_eq] at hf ⊢
  exact SequenceClosure.conj_disj_closed (SequenceClosure.conj_q_closed hf)

theorem sequence_conj_and_closed {n} {f : ℕ → Formula (limit L) n} {ψ : Formula (limit L) n}
    (hf : ⟨n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hψ : ⟨n, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ⟨n, .conj fun i ↦ ψ.and (f i)⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) := by
  rw [SequenceClosure.base_carrier_eq] at hf hψ ⊢
  exact SequenceClosure.conj_and_closed hf hψ

theorem sequence_member_closed {n} {f : ℕ → Formula (limit L) n}
    (hf : ⟨n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) (i : ℕ) :
    ⟨n, f i⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) :=
  subformulas_closed hf (Or.inr (Set.mem_iUnion.mpr ⟨i, Formula.self_mem_subformulas _⟩))

/-- The countable conjunction requirement is dense among Q-large conditions. -/
theorem q_mem_conjunction_split {φ : Formula (limit L) 1} {f : ℕ → Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hf : ⟨1, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hq : .q φ ∈ H.carrier) :
    .q (φ.and (.conj f)) ∈ H.carrier ∨ ∃ i, .q (φ.and (.neg (f i))) ∈ H.carrier := by
  rcases H.q_mem_split hφ hf hq with h | h
  · exact Or.inl h
  right
  let g : ℕ → Formula (limit L) 1 := fun i ↦ φ.and (.neg (f i))
  have hg : ⟨1, .conj g⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) :=
    sequence_conj_and_closed (sequence_conj_neg_closed hf) hφ
  have hgi (i : ℕ) : ⟨1, g i⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) :=
    sequence_member_closed hg i
  have hd := sequence_disj_closed hg
  have he : H.fiber (φ.and (.neg (.conj f))) = H.fiber (Formula.disj g) := by
    rw [H.fiber_and hφ (neg_closed hf), H.fiber_neg hf, H.fiber_disj g hd hgi]
    ext x
    have hfc : x ∈ H.fiber (.conj f) ↔ ∀ i, x ∈ H.fiber (f i) := by
      change Formula.conj (fun i ↦ (f i).substFirst x.out) ∈ H.carrier ↔ _
      exact H.conj_mem_iff _ (subst_closed hf _)
        (fun i ↦ subst_closed (sequence_member_closed hf i) _)
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, hfc, Set.mem_iUnion]
    have hgc (i : ℕ) : x ∈ H.fiber (g i) ↔ x ∈ H.fiber φ ∧ x ∉ H.fiber (f i) := by
      rw [H.fiber_and hφ (neg_closed (sequence_member_closed hf i)),
        H.fiber_neg (sequence_member_closed hf i)]
      rfl
    simp only [hgc, not_forall, exists_and_left]
  exact (H.q_mem_disj_iff g hd hgi (sequence_q_disj_closed hg)).mp
    ((H.q_mem_extensional (and_closed hφ (neg_closed hf)) hd he).mp h)

end FragmentExtension
end HenkinConstruction
end ZFVP.Infinitary
