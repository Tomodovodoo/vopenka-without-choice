import ZFVP.ModelTheory.InfinitaryConditionForcing

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.FiniteCondition
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

def Freezes (p : H.FiniteCondition) {n} (t : Semiterm (limit L) Empty n)
    (ψ : Formula (limit L) 1) : Prop :=
  ∃ h : n ≤ 1 + p.1,
    (∀ b, Formula.WeakEval H.weakQuantifier p.2.formula b →
      ¬Formula.WeakEval H.weakQuantifier ψ
        (t.val (b ∘ Formula.rightEmbed h) Empty.elim :> Fin.elim0)) ∨
    ∃ u : Semiterm (limit L) Empty 0, ∀ b,
      Formula.WeakEval H.weakQuantifier p.2.formula b →
        t.val (b ∘ Formula.rightEmbed h) Empty.elim = u.val Fin.elim0 Empty.elim

theorem freezes_persistent {p q : H.FiniteCondition} (hpq : Refines p q) {n}
    {t : Semiterm (limit L) Empty n} {ψ : Formula (limit L) 1}
    (hp : Freezes p t ψ) : Freezes q t ψ := by
  obtain ⟨g, hg⟩ := hpq
  obtain ⟨h, hh⟩ := hp
  refine ⟨h.trans (Nat.add_le_add_left g 1), ?_⟩
  rcases hh with hh | ⟨u, hh⟩
  · left
    intro b hb
    have := hh _ (hg b hb)
    simpa only [Function.comp_def, Formula.rightEmbed_trans] using this
  · right
    refine ⟨u, ?_⟩
    intro b hb
    have := hh _ (hg b hb)
    simpa only [Function.comp_def, Formula.rightEmbed_trans] using this

theorem freezes_dense (p : H.FiniteCondition) {n} (t : Semiterm (limit L) Empty n)
    {ψ : Formula (limit L) 1}
    (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hs : .q ψ ∉ H.carrier) :
    ∃ q : H.FiniteCondition, Refines p q ∧ Freezes q t ψ := by
  obtain ⟨r, hpr, hn⟩ := exists_raise p n
  have h : n ≤ 1 + r.1 := by omega
  let t' := (Rew.subst fun i ↦ Semiterm.bvar (Formula.rightEmbed h i)) t
  have ht (b : Fin (1 + r.1) → H.Domain) :
      t'.val b Empty.elim = t.val (b ∘ Formula.rightEmbed h) Empty.elim := by
    rw [Semiterm.val_substs]
    rfl
  obtain ⟨s, hrs, hh⟩ := r.2.freeze_small_term t' hψ hs
  refine ⟨⟨r.1, s⟩, refines_trans hpr (refines_same hrs), h, ?_⟩
  rcases hh with hh | ⟨u, hh⟩
  · left
    intro b hb
    simpa only [ht] using hh b hb
  · right
    exact ⟨u, fun b hb ↦ (ht b).symm.trans (hh b hb)⟩

def Avoids (p : H.FiniteCondition) (u : Semiterm (limit L) Empty 0) : Prop :=
  ∀ b, Formula.WeakEval H.weakQuantifier p.2.formula b →
    b (Formula.lastCoordinate p.1) ≠ u.val Fin.elim0 Empty.elim

theorem avoids_persistent {p q : H.FiniteCondition} (hpq : Refines p q)
    {u : Semiterm (limit L) Empty 0} (hp : Avoids p u) : Avoids q u := by
  obtain ⟨h, hh⟩ := hpq
  intro b hb
  have := hp _ (hh b hb)
  simpa only [Function.comp_apply, Formula.rightEmbed_last] using this

theorem avoids_dense (p : H.FiniteCondition) (u : Semiterm (limit L) Empty 0) :
    ∃ q : H.FiniteCondition, Refines p q ∧ Avoids q u := by
  obtain ⟨q, hq, hu⟩ := p.2.avoid_old_value u
  exact ⟨⟨p.1, q⟩, refines_same hq, hu⟩

end HenkinConstruction.FragmentExtension.FiniteCondition
end ZFVP.Infinitary
