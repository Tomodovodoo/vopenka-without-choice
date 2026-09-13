import ZFVP.ModelTheory.InfinitaryConditionForcing

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.FiniteCondition
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

/-- One of the condition's coordinates witnesses the formula for its final
parameter coordinates. -/
def HasWitness (p : H.FiniteCondition) {n} (φ : Formula (limit L) (n + 1)) : Prop :=
  ∃ h : n ≤ 1 + p.1, ∃ i : Fin (1 + p.1), ∀ b : Fin (1 + p.1) → H.Domain,
    Formula.WeakEval H.weakQuantifier p.2.formula b →
      Formula.WeakEval H.weakQuantifier φ (b i :> b ∘ Formula.rightEmbed h)

theorem hasWitness_persistent {p q : H.FiniteCondition} (hpq : Refines p q) {n}
    {φ : Formula (limit L) (n + 1)} (hp : HasWitness p φ) : HasWitness q φ := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨h, i, hi⟩ := hp
  refine ⟨h.trans (Nat.add_le_add_left g 1), Formula.rightEmbed (Nat.add_le_add_left g 1) i, ?_⟩
  intro b hb
  have ht := hi _ (hg b hb)
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using ht

theorem existential_dense (p : H.FiniteCondition) {n} {φ : Formula (limit L) (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) :
    ∃ q : H.FiniteCondition, Refines p q ∧ (Forces q (.neg (.exs φ)) ∨ HasWitness q φ) := by
  obtain ⟨r, hpr, hn⟩ := exists_raise p n
  have h : n ≤ 1 + r.1 := by omega
  let ψ := φ.rename (liftRenaming (Formula.rightEmbed h))
  have hψ : ⟨1 + (r.1 + 1), ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) :=
    rename_closed hφ _
  rcases r.2.existential hψ with ⟨s, hrs, hs⟩ | ⟨s, hrs, hs⟩
  · refine ⟨⟨r.1, s⟩, refines_trans hpr (refines_same hrs), Or.inl ?_⟩
    refine ⟨h, ?_⟩
    intro b hb
    rw [hs, Formula.weakEval_and] at hb
    have he : Formula.WeakEval H.weakQuantifier (.exs ψ) b ↔
        Formula.WeakEval H.weakQuantifier (.exs φ) (b ∘ Formula.rightEmbed h) :=
      Formula.weakEval_rename H.weakQuantifier (Formula.rightEmbed h) (.exs φ) b
    exact fun hx ↦ hb.2 (he.mpr hx)
  · refine ⟨⟨r.1 + 1, s⟩, refines_trans hpr (refines_next hrs), Or.inr ?_⟩
    let hnew : n ≤ 1 + (r.1 + 1) := h.trans (Nat.le_succ (1 + r.1))
    refine ⟨hnew, 0, ?_⟩
    intro b hb
    rw [hs, Formula.weakEval_and] at hb
    have ht := (Formula.weakEval_rename H.weakQuantifier
      (liftRenaming (Formula.rightEmbed h)) φ b).mp hb.2
    have he : b ∘ liftRenaming (Formula.rightEmbed h) = b 0 :> b ∘ Formula.rightEmbed hnew := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        change b (Formula.rightEmbed h i).succ = b (Formula.rightEmbed hnew i)
        congr 1
        simpa only [Formula.rightEmbed_succ] using
          (Formula.rightEmbed_trans h (Nat.le_succ (1 + r.1)) i)
    rwa [he] at ht

end HenkinConstruction.FragmentExtension.FiniteCondition
end ZFVP.Infinitary
