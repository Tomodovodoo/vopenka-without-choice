import ZFVP.ModelTheory.InfinitaryForcesCoordinates

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

abbrev CoordinateTerm (L : Language) := Σ n, Semiterm L Empty n

namespace CoordinateTerm

def EqualAt (p : H.FiniteCondition) (s t : CoordinateTerm (limit L)) : Prop :=
  ∃ hs : s.1 ≤ 1 + p.1, ∃ ht : t.1 ≤ 1 + p.1,
    ∀ b, Formula.WeakEval H.weakQuantifier p.2.formula b →
      s.2.val (b ∘ Formula.rightEmbed hs) Empty.elim =
        t.2.val (b ∘ Formula.rightEmbed ht) Empty.elim

theorem equalAt_persistent {p q : H.FiniteCondition} (hpq : Refines p q)
    {s t : CoordinateTerm (limit L)} (he : EqualAt p s t) : EqualAt q s t := by
  obtain ⟨h, hh⟩ := hpq
  obtain ⟨hs, ht, he⟩ := he
  refine ⟨hs.trans (Nat.add_le_add_left h 1), ht.trans (Nat.add_le_add_left h 1), ?_⟩
  intro b hb
  have := he _ (hh b hb)
  simpa only [Function.comp_def, Formula.rightEmbed_trans] using this

theorem equalAt_refl (p : H.FiniteCondition) (s : CoordinateTerm (limit L))
    (h : s.1 ≤ 1 + p.1) : EqualAt p s s := ⟨h, h, fun _ _ ↦ rfl⟩

theorem equalAt_symm {p : H.FiniteCondition} {s t : CoordinateTerm (limit L)}
    (he : EqualAt p s t) : EqualAt p t s := by
  obtain ⟨hs, ht, he⟩ := he
  exact ⟨ht, hs, fun b hb ↦ (he b hb).symm⟩

theorem equalAt_trans {p : H.FiniteCondition} {s t u : CoordinateTerm (limit L)}
    (hst : EqualAt p s t) (htu : EqualAt p t u) : EqualAt p s u := by
  obtain ⟨hs, ht, he⟩ := hst
  obtain ⟨ht', hu, hf⟩ := htu
  exact ⟨hs, hu, fun b hb ↦ (he b hb).trans (hf b hb)⟩

def Rel (c : ℕ → H.FiniteCondition) (s t : CoordinateTerm (limit L)) : Prop :=
  ∃ i, EqualAt (c i) s t

variable (c : ℕ → H.FiniteCondition)
  (hc : ∀ {i j}, i ≤ j → Refines (c i) (c j))
  (ha : ∀ n, ∃ i, n ≤ 1 + (c i).1)

include ha in
theorem rel_refl (s : CoordinateTerm (limit L)) : Rel c s s := by
  obtain ⟨i, hi⟩ := ha s.1
  exact ⟨i, equalAt_refl (c i) s hi⟩

theorem rel_symm {s t : CoordinateTerm (limit L)} (he : Rel c s t) : Rel c t s := by
  obtain ⟨i, hi⟩ := he
  exact ⟨i, equalAt_symm hi⟩

include hc in
theorem rel_trans {s t u : CoordinateTerm (limit L)}
    (hst : Rel c s t) (htu : Rel c t u) : Rel c s u := by
  obtain ⟨i, hi⟩ := hst
  obtain ⟨j, hj⟩ := htu
  exact ⟨max i j, equalAt_trans (equalAt_persistent (hc (Nat.le_max_left _ _)) hi)
    (equalAt_persistent (hc (Nat.le_max_right _ _)) hj)⟩

def setoid : Setoid (CoordinateTerm (limit L)) where
  r := Rel c
  iseqv := ⟨rel_refl c ha, rel_symm c, rel_trans c hc⟩

end CoordinateTerm
end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary

