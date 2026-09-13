import ZFVP.ModelTheory.InfinitaryGenericConditionChain
import ZFVP.ModelTheory.InfinitaryCoordinateTermRelation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

def Contains {n} (φ : Formula (limit L) n) : Prop := ∃ i, Forces (C.point i) φ

theorem contains_eventually {n} {φ : Formula (limit L) n} (h : C.Contains φ) :
    ∃ i, ∀ j, i ≤ j → Forces (C.point j) φ := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, fun j hj ↦ forces_persistent (C.refines hj) hi⟩

theorem not_both {n} {φ : Formula (limit L) n}
    (hp : C.Contains φ) (hn : C.Contains (.neg φ)) : False := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hn
  exact not_forces_both (C.point (max i j))
    (forces_persistent (C.refines (Nat.le_max_left _ _)) hi)
    (forces_persistent (C.refines (Nat.le_max_right _ _)) hj)

theorem neg_iff {n} {φ : Formula (limit L) n}
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    C.Contains (.neg φ) ↔ ¬C.Contains φ := by
  constructor
  · exact fun hn hp ↦ C.not_both hp hn
  · intro hn
    obtain ⟨i, hi⟩ := C.decides φ hφ
    rcases hi i (le_refl _) with hp | hp
    · exact (hn ⟨i, hp⟩).elim
    · exact ⟨i, hp⟩

theorem and_iff {n} {φ ψ : Formula (limit L) n} :
    C.Contains (φ.and ψ) ↔ C.Contains φ ∧ C.Contains ψ := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨hφ, hψ⟩ := forces_and_iff.mp hi
    exact ⟨⟨i, hφ⟩, ⟨i, hψ⟩⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨max i j, forces_and_iff.mpr
      ⟨forces_persistent (C.refines (Nat.le_max_left _ _)) hi,
        forces_persistent (C.refines (Nat.le_max_right _ _)) hj⟩⟩

theorem conjunction_iff {n} {f : ℕ → Formula (limit L) n}
    (hf : ⟨n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    C.Contains (.conj f) ↔ ∀ i, C.Contains (f i) := by
  constructor
  · rintro ⟨k, hk⟩ i
    exact ⟨k, forces_conj_member hk i⟩
  · intro hh
    obtain ⟨k, hk⟩ := C.conjunction f hf
    rcases hk k (le_refl _) with hp | ⟨i, hi⟩
    · exact ⟨k, hp⟩
    · exact (C.not_both (hh i) ⟨k, hi⟩).elim

theorem existential_iff {n} {φ : Formula (limit L) (n + 1)}
    (hφ : ⟨n, .exs φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    C.Contains (.exs φ) ↔ ∃ i, HasWitness (C.point i) φ := by
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := C.existential φ hφ
    rcases hi i (le_refl _) with hn | hw
    · exact (C.not_both hp ⟨i, hn⟩).elim
    · exact ⟨i, hw⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, forces_exs_of_witness hi⟩

theorem closed_iff (φ : Sentence (limit L)) :
    C.Contains φ ↔ Formula.WeakEval H.weakQuantifier φ Fin.elim0 := by
  constructor
  · rintro ⟨i, hi⟩
    exact (forces_closed_iff _ _).mp hi
  · intro hi
    exact ⟨0, (forces_closed_iff _ _).mpr hi⟩

theorem coordinate_cofinal (n : ℕ) : ∃ i, n ≤ 1 + (C.point i).1 := by
  obtain ⟨i, hi⟩ := C.arity_unbounded n
  exact ⟨i, by have := hi i (le_refl _); omega⟩

theorem rightRename_iff {n m} (h : n ≤ m) {φ : Formula (limit L) n} :
    C.Contains (φ.rename (Formula.rightEmbed h)) ↔ C.Contains φ := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, forces_of_rightRename h hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := C.coordinate_cofinal m
    have hbound := (C.refines (Nat.le_max_right i j)).choose
    refine ⟨max i j, forces_rightRename h ?_
      (forces_persistent (C.refines (Nat.le_max_left _ _)) hi)⟩
    omega

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary
