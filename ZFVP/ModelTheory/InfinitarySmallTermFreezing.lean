import ZFVP.ModelTheory.InfinitaryWitnessMatrix

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language} {M : Type*} [Structure L M] (Q : Set M → Prop)

@[simp] theorem weakEval_swapFirstTwo {n} (φ : Formula L (n + 2))
    (b : Fin n → M) (x y : M) :
    WeakEval Q φ.swapFirstTwo (x :> y :> b) ↔ WeakEval Q φ (y :> x :> b) := by
  rw [swapFirstTwo, weakEval_rename]
  have he : (x :> y :> b) ∘ Fin.cases 1 (Fin.cases 0 (fun i ↦ i.succ.succ)) = y :> x :> b := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases <;> rfl
  rw [he]

def liftClosedTerm {n} (u : Semiterm L Empty 0) : Semiterm L Empty n :=
  Rew.subst (Fin.elim0 : Fin 0 → Semiterm L Empty n) u

@[simp] theorem val_liftClosedTerm {n} (u : Semiterm L Empty 0) (b : Fin n → M) :
    (liftClosedTerm u).val b Empty.elim = u.val Fin.elim0 Empty.elim := by
  rw [liftClosedTerm, Semiterm.val_substs]
  congr 1
  exact Subsingleton.elim _ _

end Formula
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  (H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S)))

theorem witnessMatrix_projection (k : ℕ) {φ : Formula (limit L) (1 + k)}
    (hφ : ⟨1 + k, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (t : Semiterm (limit L) Empty (1 + k)) :
    H.fiber (.exs (Formula.witnessMatrix k φ t)) = H.fiber (Formula.exsN k φ) := by
  ext x
  rw [H.fiber_weakEval (exs_closed (witnessMatrix_closed k hφ t)), H.fiber_weakEval (exsN_closed k hφ)]
  simp only [Formula.weakEval_exs, Formula.weakEval_witnessMatrix, Formula.weakEval_exsN_one_iff]
  constructor
  · rintro ⟨y, e, he, hp, _⟩
    exact ⟨e, he, hp⟩
  · rintro ⟨e, he, hp⟩
    exact ⟨t.val e Empty.elim, e, he, hp, rfl⟩

/-- If a term is forced into an old small fiber, it can be fixed to an old
closed term while retaining a large projection. -/
theorem q_mem_fix_small_term (k : ℕ) {φ : Formula (limit L) (1 + k)}
    (hφ : ⟨1 + k, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (t : Semiterm (limit L) Empty (1 + k)) {ψ : Formula (limit L) 1}
    (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hq : .q (Formula.exsN k φ) ∈ H.carrier) (hs : .q ψ ∉ H.carrier)
    (hbound : ∀ e : Fin (1 + k) → H.Domain, Formula.WeakEval H.weakQuantifier φ e →
      Formula.WeakEval H.weakQuantifier ψ (t.val e Empty.elim :> Fin.elim0)) :
    ∃ u : Semiterm (limit L) Empty 0,
      .q (Formula.exsN k (φ.and (Formula.termEqual t (Formula.liftClosedTerm u)))) ∈ H.carrier := by
  let θ := Formula.witnessMatrix k φ t
  have hθ := witnessMatrix_closed k hφ t
  have hp : .q (.exs θ) ∈ H.carrier :=
    (H.q_mem_extensional (exs_closed hθ) (exsN_closed k hφ) (H.witnessMatrix_projection k hφ t)).mpr hq
  have hb : H.fiber (.exs θ.swapFirstTwo) ⊆ H.fiber ψ := by
    intro y hy
    rw [H.fiber_weakEval (exs_closed (swapFirstTwo_closed hθ))] at hy
    obtain ⟨x, hx⟩ := hy
    rw [Formula.weakEval_swapFirstTwo] at hx
    obtain ⟨e, he, hf, ht⟩ := (Formula.weakEval_witnessMatrix _ k φ t y x).mp hx
    apply (H.fiber_weakEval hψ y).mpr
    rw [ht]
    exact hbound e hf
  obtain ⟨u, hu⟩ := H.q_large_witness_in_small_bound hθ hψ hp hs hb
  refine ⟨u, ?_⟩
  have hu' := (H.weak_sentence_truth _ (subst_closed (q_closed (swapFirstTwo_closed hθ)) _)).mpr hu
  change Formula.WeakEval H.weakQuantifier ((Formula.q θ.swapFirstTwo).substFirst u) Fin.elim0 at hu'
  rw [Formula.weakEval_substFirst, Formula.weakEval_q] at hu'
  have hf : ⟨1, Formula.exsN k (φ.and (Formula.termEqual t (Formula.liftClosedTerm u)))⟩ ∈
      FragmentClosure.carrier (SequenceClosure.carrier S) :=
    exsN_closed k (and_closed hφ (fo_in_fragment _))
  apply (H.weakQuantifier_fiber hf).mp
  have he : {x : H.Domain | Formula.WeakEval H.weakQuantifier θ.swapFirstTwo
      (x :> u.val Fin.elim0 Empty.elim :> Fin.elim0)} =
      H.fiber (Formula.exsN k (φ.and (Formula.termEqual t (Formula.liftClosedTerm u)))) := by
    ext x
    rw [H.fiber_weakEval hf]
    simp only [Formula.weakEval_swapFirstTwo, θ, Formula.weakEval_witnessMatrix,
      Formula.weakEval_exsN_one_iff, Formula.weakEval_and, Formula.weakEval_termEqual,
      Formula.val_liftClosedTerm]
    apply exists_congr
    intro e
    simp only [eq_comm]
  rwa [he] at hu'

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary


