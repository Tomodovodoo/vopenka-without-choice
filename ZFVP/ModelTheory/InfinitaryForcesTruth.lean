import ZFVP.ModelTheory.InfinitaryConditionRealization
import ZFVP.ModelTheory.InfinitaryConditionWitness

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.FiniteCondition
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

theorem forces_closed_iff (p : H.FiniteCondition) (φ : Sentence (limit L)) :
    Forces p φ ↔ Formula.WeakEval H.weakQuantifier φ Fin.elim0 := by
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨b, hb⟩ := p.realizable
    have he : b ∘ Formula.rightEmbed h = Fin.elim0 := Subsingleton.elim _ _
    simpa only [he] using hh b hb
  · intro hh
    refine ⟨Nat.zero_le _, ?_⟩
    intro b _
    convert hh using 1

theorem forces_congr {p : H.FiniteCondition} {n} {φ ψ : Formula (limit L) n}
    (he : ∀ b : Fin n → H.Domain,
      Formula.WeakEval H.weakQuantifier φ b ↔ Formula.WeakEval H.weakQuantifier ψ b) :
    Forces p φ ↔ Forces p ψ := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, fun b hb ↦ (he _).mp (hh b hb)⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, fun b hb ↦ (he _).mpr (hh b hb)⟩

theorem forces_and_iff {p : H.FiniteCondition} {n} {φ ψ : Formula (limit L) n} :
    Forces p (φ.and ψ) ↔ Forces p φ ∧ Forces p ψ := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨⟨h, fun b hb ↦ (Formula.weakEval_and _ _ _ _).mp (hh b hb) |>.1⟩,
      ⟨h, fun b hb ↦ (Formula.weakEval_and _ _ _ _).mp (hh b hb) |>.2⟩⟩
  · rintro ⟨⟨h, hh⟩, ⟨g, hg⟩⟩
    exact ⟨h, fun b hb ↦ (Formula.weakEval_and _ _ _ _).mpr ⟨hh b hb, hg b hb⟩⟩

theorem forces_conj_member {p : H.FiniteCondition} {n} {f : ℕ → Formula (limit L) n}
    (hp : Forces p (.conj f)) (i : ℕ) : Forces p (f i) := by
  obtain ⟨h, hh⟩ := hp
  exact ⟨h, fun b hb ↦ hh b hb i⟩

theorem forces_exs_of_witness {p : H.FiniteCondition} {n} {φ : Formula (limit L) (n + 1)}
    (hp : HasWitness p φ) : Forces p (.exs φ) := by
  obtain ⟨h, i, hh⟩ := hp
  exact ⟨h, fun b hb ↦ ⟨b i, hh b hb⟩⟩

theorem forces_double_neg_iff {p : H.FiniteCondition} {n} {φ : Formula (limit L) n} :
    Forces p (.neg (.neg φ)) ↔ Forces p φ := by
  classical
  exact forces_congr (fun _ ↦ not_not)

end HenkinConstruction.FragmentExtension.FiniteCondition
end ZFVP.Infinitary

