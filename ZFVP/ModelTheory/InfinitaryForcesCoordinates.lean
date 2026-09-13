import ZFVP.ModelTheory.InfinitaryForcesTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language}

def liftRightTerm {n m} (h : n ≤ m) (t : Semiterm L Empty n) : Semiterm L Empty m :=
  (Rew.subst fun i ↦ Semiterm.bvar (rightEmbed h i)) t

@[simp] theorem val_liftRightTerm {M : Type*} [Structure L M] {n m} (h : n ≤ m)
    (t : Semiterm L Empty n) (b : Fin m → M) :
    (liftRightTerm h t).val b Empty.elim = t.val (b ∘ rightEmbed h) Empty.elim := by
  rw [liftRightTerm, Semiterm.val_substs]
  rfl

end Formula
namespace HenkinConstruction.FragmentExtension.FiniteCondition
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

theorem forces_of_rightRename {p : H.FiniteCondition} {n m} (h : n ≤ m)
    {φ : Formula (limit L) n} (hp : Forces p (φ.rename (Formula.rightEmbed h))) :
    Forces p φ := by
  obtain ⟨g, hg⟩ := hp
  refine ⟨h.trans g, ?_⟩
  intro b hb
  have := (Formula.weakEval_rename _ _ _ _).mp (hg b hb)
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using this

theorem forces_rightRename {p : H.FiniteCondition} {n m} (h : n ≤ m)
    (hm : m ≤ 1 + p.1) {φ : Formula (limit L) n} (hp : Forces p φ) :
    Forces p (φ.rename (Formula.rightEmbed h)) := by
  obtain ⟨g, hg⟩ := hp
  refine ⟨hm, ?_⟩
  intro b hb
  rw [Formula.weakEval_rename]
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using hg b hb

theorem forces_termEqual_refl {p : H.FiniteCondition} {n} (hn : n ≤ 1 + p.1)
    (t : Semiterm (limit L) Empty n) : Forces p (Formula.termEqual t t) := by
  refine ⟨hn, ?_⟩
  intro b _
  exact (Formula.weakEval_termEqual _ _ _ _).mpr rfl

theorem forces_termEqual_symm {p : H.FiniteCondition} {n} {s t : Semiterm (limit L) Empty n}
    (hp : Forces p (Formula.termEqual s t)) : Forces p (Formula.termEqual t s) := by
  obtain ⟨h, hh⟩ := hp
  refine ⟨h, ?_⟩
  intro b hb
  exact (Formula.weakEval_termEqual _ _ _ _).mpr ((Formula.weakEval_termEqual _ _ _ _).mp (hh b hb)).symm

theorem forces_termEqual_trans {p : H.FiniteCondition} {n} {s t u : Semiterm (limit L) Empty n}
    (hs : Forces p (Formula.termEqual s t)) (ht : Forces p (Formula.termEqual t u)) :
    Forces p (Formula.termEqual s u) := by
  obtain ⟨h, hh⟩ := hs
  obtain ⟨g, hg⟩ := ht
  refine ⟨h, ?_⟩
  intro b hb
  exact (Formula.weakEval_termEqual _ _ _ _).mpr
    (((Formula.weakEval_termEqual _ _ _ _).mp (hh b hb)).trans
      ((Formula.weakEval_termEqual _ _ _ _).mp (hg b hb)))

end HenkinConstruction.FragmentExtension.FiniteCondition
end ZFVP.Infinitary
