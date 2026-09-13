import ZFVP.ModelTheory.InfinitaryWitnessCoordinates
import ZFVP.ModelTheory.InfinitaryLargeConditions

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language} [L.Eq]

def witnessMatrix (k : ℕ) (φ : Formula L (1 + k)) (t : Semiterm L Empty (1 + k)) : Formula L 2 :=
  exsN k ((φ.rename (WitnessCoordinates.embed k)).and
    (termEqual (.bvar (WitnessCoordinates.witness k))
      ((Rew.subst fun i ↦ Semiterm.bvar (WitnessCoordinates.embed k i)) t)))

variable {M : Type*} [Structure L M] [Structure.Eq L M] (Q : Set M → Prop)

@[simp] theorem weakEval_termEqual {n} (s t : Semiterm L Empty n) (b : Fin n → M) :
    WeakEval Q (termEqual s t) b ↔ s.val b Empty.elim = t.val b Empty.elim :=
  eval_termEqual s t b

theorem weakEval_witnessMatrix (k : ℕ) (φ : Formula L (1 + k)) (t : Semiterm L Empty (1 + k))
    (y x : M) : WeakEval Q (witnessMatrix k φ t) (y :> x :> Fin.elim0) ↔
      ∃ e : Fin (1 + k) → M,
        e (lastCoordinate k) = x ∧ WeakEval Q φ e ∧ y = t.val e Empty.elim := by
  rw [witnessMatrix, weakEval_exsN_iff]
  constructor
  · rintro ⟨e, he, h⟩
    have hz := congrFun he 0
    have ho := congrFun he 1
    rw [dropFirst_apply, WitnessCoordinates.tail_zero] at hz
    rw [dropFirst_apply, WitnessCoordinates.tail_one] at ho
    obtain ⟨hp, ht⟩ := (weakEval_and _ _ _ _).mp h
    rw [weakEval_rename] at hp
    rw [weakEval_termEqual, Semiterm.val_substs] at ht
    refine ⟨e ∘ WitnessCoordinates.embed k, ho, hp, ?_⟩
    change e (WitnessCoordinates.witness k) = t.val (e ∘ WitnessCoordinates.embed k) Empty.elim at ht
    exact hz.symm.trans ht
  · rintro ⟨e, he, hp, ht⟩
    refine ⟨WitnessCoordinates.insert k e y, ?_, ?_⟩
    · rw [WitnessCoordinates.drop_insert, he]
    · rw [weakEval_and, weakEval_rename, WitnessCoordinates.insert_comp_embed]
      refine ⟨hp, ?_⟩
      rw [weakEval_termEqual, Semiterm.val_substs]
      change WitnessCoordinates.insert k e y (WitnessCoordinates.witness k) =
        t.val (WitnessCoordinates.insert k e y ∘ WitnessCoordinates.embed k) Empty.elim
      rw [WitnessCoordinates.insert_witness, WitnessCoordinates.insert_comp_embed]
      exact ht

end Formula
namespace FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable]

theorem witnessMatrix_closed {S : Set (TaggedFormula L)} (k : ℕ) {φ : Formula L (1 + k)}
    (hφ : ⟨1 + k, φ⟩ ∈ carrier S) (t : Semiterm L Empty (1 + k)) :
    ⟨2, Formula.witnessMatrix k φ t⟩ ∈ carrier S :=
  exsN_closed k (and_closed (rename_closed hφ _) (firstOrder_subset_carrier _ (Or.inl ⟨⟨_, _⟩, rfl⟩)))

end FragmentClosure
end ZFVP.Infinitary

