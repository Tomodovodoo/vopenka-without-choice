import ZFVP.SetTheory.ClassForcingAlgebra

/-! Generic truth laws for definable classes of conditions. No set of all
conditions and no ZF hypothesis on the class extension is used. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

def ClassMeets (_T : DefinableForcingTower V) (G : Set V) (A : V → Prop) : Prop := ∃ p ∈ G, A p

theorem classDecision_dense (A : V → Prop) (hA : ∀ p, A p → T.Condition p) :
    ClassForcingDense T.Condition T.LE (fun p ↦ A p ∨ T.ClassNegation A p) := by
  classical
  refine ⟨fun p hp ↦ hp.elim (hA p) And.left, ?_⟩
  intro p hp
  by_cases he : ∃ q, A q ∧ T.LE q p
  · obtain ⟨q, hq, hqp⟩ := he
    exact ⟨q, Or.inl hq, hqp⟩
  · exact ⟨p, Or.inr ⟨hp, fun q _ hqp hq ↦ he ⟨q, hq, hqp⟩⟩, T.le_refl hp⟩

variable {G : Set V} (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
include hG

theorem classMeets_decision (A : V → Prop) (hd : ℒₛₑₜ-predicate A)
    (hA : ∀ p, A p → T.Condition p) :
    T.ClassMeets G A ∨ T.ClassMeets G (T.ClassNegation A) := by
  obtain ⟨p, hp, h⟩ := hG.2 (fun p ↦ A p ∨ T.ClassNegation A p)
    (by unfold ClassNegation; definability) (T.classDecision_dense A hA)
  exact h.elim (fun h ↦ Or.inl ⟨p, hp, h⟩) (fun h ↦ Or.inr ⟨p, hp, h⟩)

theorem classMeets_negation (A : V → Prop) (hd : ℒₛₑₜ-predicate A)
    (hA : ∀ p, A p → T.Condition p) (hdown : T.ClassDownward A) :
    T.ClassMeets G (T.ClassNegation A) ↔ ¬T.ClassMeets G A := by
  constructor
  · rintro ⟨p, hp, hn⟩ ⟨q, hq, hqA⟩
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
    exact hn.2 r (hG.1.1 r hr) hrp (hdown q hqA r (hG.1.1 r hr) hrq)
  · intro hn
    exact (T.classMeets_decision hG A hd hA).elim (fun h ↦ (hn h).elim) id

theorem classMeets_closure (A : V → Prop) (hd : ℒₛₑₜ-predicate A)
    (hA : ∀ p, A p → T.Condition p) (hdown : T.ClassDownward A) :
    T.ClassMeets G (T.ClassClosure A) ↔ T.ClassMeets G A := by
  constructor
  · rintro ⟨p, hp, hc⟩
    rcases T.classMeets_decision hG A hd hA with h | ⟨q, hq, hn⟩
    · exact h
    · obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
      obtain ⟨s, hs, hsr⟩ := hc.2 r (hG.1.1 r hr) hrp
      exact (hn.2 s (hA s hs) (T.le_trans hsr hrq) hs).elim
  · rintro ⟨p, hp, hAp⟩
    exact ⟨p, hp, hA p hAp, fun q hq hqp ↦
      ⟨q, hdown p hAp q hq hqp, T.le_refl hq⟩⟩

theorem classMeets_and {A B : V → Prop} (hA : T.ClassDownward A) (hB : T.ClassDownward B) :
    T.ClassMeets G (fun p ↦ A p ∧ B p) ↔ T.ClassMeets G A ∧ T.ClassMeets G B := by
  constructor
  · rintro ⟨p, hp, hAp, hBp⟩
    exact ⟨⟨p, hp, hAp⟩, ⟨p, hp, hBp⟩⟩
  · rintro ⟨⟨p, hp, hAp⟩, ⟨q, hq, hBq⟩⟩
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
    exact ⟨r, hr, hA p hAp r (hG.1.1 r hr) hrp, hB q hBq r (hG.1.1 r hr) hrq⟩

theorem classMeets_or (A B : V → Prop) (hA : ℒₛₑₜ-predicate A) (hB : ℒₛₑₜ-predicate B)
    (hrA : T.ClassRegular A) (hrB : T.ClassRegular B) :
    T.ClassMeets G (T.ClassClosure (fun p ↦ A p ∨ B p)) ↔
      T.ClassMeets G A ∨ T.ClassMeets G B := by
  rw [T.classMeets_closure hG _ (by definability)
    (fun p hp ↦ hp.elim (hrA.1 p) (hrB.1 p))
    (fun p hp q hq hqp ↦ hp.elim (fun h ↦ Or.inl (hrA.2.1 p h q hq hqp))
      (fun h ↦ Or.inr (hrB.2.1 p h q hq hqp)))]
  constructor
  · rintro ⟨p, hp, h⟩
    exact h.elim (fun h ↦ Or.inl ⟨p, hp, h⟩) (fun h ↦ Or.inr ⟨p, hp, h⟩)
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, hp, Or.inl h⟩
    · exact ⟨p, hp, Or.inr h⟩

theorem classMeets_all (N : V → Prop) (F : V → V → Prop)
    (hN : ℒₛₑₜ-predicate N) (hF : ℒₛₑₜ-relation F)
    (hr : ∀ x, N x → T.ClassRegular (F x)) :
    T.ClassMeets G (fun p ↦ T.Condition p ∧ ∀ x, N x → F x p) ↔
      ∀ x, N x → T.ClassMeets G (F x) := by
  classical
  constructor
  · rintro ⟨p, hp, _, hall⟩ x hx
    exact ⟨p, hp, hall x hx⟩
  · intro hall
    let D := fun p ↦ (T.Condition p ∧ ∀ x, N x → F x p) ∨
      ∃ x, N x ∧ T.ClassNegation (F x) p
    have hd : ClassForcingDense T.Condition T.LE D := by
      refine ⟨?_, ?_⟩
      · intro p hp
        rcases hp with hp | ⟨x, _, hx⟩
        · exact hp.1
        · exact hx.1
      · intro p hp
        by_cases hf : ∀ x, N x → F x p
        · exact ⟨p, Or.inl ⟨hp, hf⟩, T.le_refl hp⟩
        · push Not at hf
          obtain ⟨x, hx, hfx⟩ := hf
          obtain ⟨q, hq, hqp⟩ := T.classNegation_exists_of_not (hr x hx) hp hfx
          exact ⟨q, Or.inr ⟨x, hx, hq⟩, hqp⟩
    obtain ⟨p, hp, hDp⟩ := hG.2 D (by unfold D ClassNegation; definability) hd
    rcases hDp with h | ⟨x, hx, hn⟩
    · exact ⟨p, hp, h⟩
    · exact ((T.classMeets_negation hG (F x) (by definability) (hr x hx).1
        (hr x hx).2.1).mp ⟨p, hp, hn⟩ (hall x hx)).elim

theorem classMeets_exists (N : V → Prop) (F : V → V → Prop)
    (hN : ℒₛₑₜ-predicate N) (hF : ℒₛₑₜ-relation F)
    (hr : ∀ x, N x → T.ClassRegular (F x)) :
    T.ClassMeets G (T.ClassClosure (fun p ↦ ∃ x, N x ∧ F x p)) ↔
      ∃ x, N x ∧ T.ClassMeets G (F x) := by
  rw [T.classMeets_closure hG _ (by definability)
    (fun p ⟨x, hx, hxp⟩ ↦ (hr x hx).1 p hxp)
    (fun p ⟨x, hx, hxp⟩ q hq hqp ↦ ⟨x, hx, (hr x hx).2.1 p hxp q hq hqp⟩)]
  constructor
  · rintro ⟨p, hp, x, hx, hxp⟩
    exact ⟨x, hx, p, hp, hxp⟩
  · rintro ⟨x, hx, p, hp, hxp⟩
    exact ⟨p, hp, x, hx, hxp⟩

end DefinableForcingTower
end ZFVP
