import ZFVP.ModelTheory.DefinableClassGeneric
import ZFVP.SetTheory.ClassForcingTowerOrder

/-! Regular definable classes of conditions and the logical forcing operations
for the actual ordinal tower. These are classes, not purported internal sets. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

def ClassDownward (A : V → Prop) : Prop :=
  ∀ p, A p → ∀ q, T.Condition q → T.LE q p → A q

def ClassClosure (A : V → Prop) (p : V) : Prop :=
  T.Condition p ∧ ∀ q, T.Condition q → T.LE q p → ∃ r, A r ∧ T.LE r q

def ClassNegation (A : V → Prop) (p : V) : Prop :=
  T.Condition p ∧ ∀ q, T.Condition q → T.LE q p → ¬A q

def ClassRegular (A : V → Prop) : Prop :=
  (∀ p, A p → T.Condition p) ∧ T.ClassDownward A ∧ ∀ p, T.ClassClosure A p → A p

theorem classClosure_definable (A : V → Prop) (hA : ℒₛₑₜ-predicate A) :
    ℒₛₑₜ-predicate (T.ClassClosure A) := by
  unfold ClassClosure
  definability

theorem classNegation_definable (A : V → Prop) (hA : ℒₛₑₜ-predicate A) :
    ℒₛₑₜ-predicate (T.ClassNegation A) := by
  unfold ClassNegation
  definability

theorem classClosure_downward (A : V → Prop) : T.ClassDownward (T.ClassClosure A) := by
  intro p hp q hq hqp
  refine ⟨hq, ?_⟩
  intro r hr hrq
  exact hp.2 r hr (T.le_trans hrq hqp)

theorem classClosure_regular (A : V → Prop) :
    T.ClassRegular (T.ClassClosure A) := by
  refine ⟨fun _ h ↦ h.1, T.classClosure_downward A, ?_⟩
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro q hq hqp
  obtain ⟨r, hr, hrq⟩ := hp.2 q hq hqp
  obtain ⟨s, hs, hsr⟩ := hr.2 r hr.1 (T.le_refl hr.1)
  exact ⟨s, hs, T.le_trans hsr hrq⟩

theorem classNegation_downward (A : V → Prop) : T.ClassDownward (T.ClassNegation A) := by
  intro p hp q hq hqp
  exact ⟨hq, fun r hr hrq ↦ hp.2 r hr (T.le_trans hrq hqp)⟩

theorem classNegation_regular (A : V → Prop) (hd : T.ClassDownward A) :
    T.ClassRegular (T.ClassNegation A) := by
  refine ⟨fun _ h ↦ h.1, T.classNegation_downward A, ?_⟩
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro q hq hqp hAq
  obtain ⟨r, hr, hrq⟩ := hp.2 q hq hqp
  exact hr.2 r hr.1 (T.le_refl hr.1) (hd q hAq r hr.1 hrq)

theorem classRegular_top : T.ClassRegular T.Condition := by
  exact ⟨fun _ h ↦ h, fun _ _ _ hq _ ↦ hq, fun _ h ↦ h.1⟩

theorem classRegular_empty : T.ClassRegular (fun _ ↦ False) := by
  refine ⟨fun _ h ↦ h.elim, fun _ h ↦ h.elim, ?_⟩
  intro p hp
  obtain ⟨_, h, _⟩ := hp.2 p hp.1 (T.le_refl hp.1)
  exact h

theorem classRegular_and {A B : V → Prop} (hA : T.ClassRegular A) (hB : T.ClassRegular B) :
    T.ClassRegular (fun p ↦ A p ∧ B p) := by
  refine ⟨fun p hp ↦ hA.1 p hp.1, ?_, ?_⟩
  · intro p hp q hq hqp
    exact ⟨hA.2.1 p hp.1 q hq hqp, hB.2.1 p hp.2 q hq hqp⟩
  · intro p hp
    constructor
    · apply hA.2.2 p
      refine ⟨hp.1, ?_⟩
      intro q hq hqp
      obtain ⟨r, hr, hrq⟩ := hp.2 q hq hqp
      exact ⟨r, hr.1, hrq⟩
    · apply hB.2.2 p
      refine ⟨hp.1, ?_⟩
      intro q hq hqp
      obtain ⟨r, hr, hrq⟩ := hp.2 q hq hqp
      exact ⟨r, hr.2, hrq⟩

theorem classRegular_all (N : V → Prop) (F : V → V → Prop)
    (hF : ∀ x, N x → T.ClassRegular (F x)) :
    T.ClassRegular (fun p ↦ T.Condition p ∧ ∀ x, N x → F x p) := by
  refine ⟨fun _ h ↦ h.1, ?_, ?_⟩
  · intro p hp q hq hqp
    exact ⟨hq, fun x hx ↦ (hF x hx).2.1 p (hp.2 x hx) q hq hqp⟩
  · intro p hp
    refine ⟨hp.1, ?_⟩
    intro x hx
    apply (hF x hx).2.2 p
    refine ⟨hp.1, ?_⟩
    intro q hq hqp
    obtain ⟨r, hr, hrq⟩ := hp.2 q hq hqp
    exact ⟨r, hr.2 x hx, hrq⟩

theorem classNegation_exists_of_not {A : V → Prop} (hA : T.ClassRegular A)
    {p : V} (hp : T.Condition p) (hn : ¬A p) :
    ∃ q, T.ClassNegation A q ∧ T.LE q p := by
  classical
  have hd : ¬∀ q, T.Condition q → T.LE q p → ∃ r, A r ∧ T.LE r q :=
    fun h ↦ hn (hA.2.2 p ⟨hp, h⟩)
  push Not at hd
  obtain ⟨q, hq, hqp, hnone⟩ := hd
  refine ⟨q, ⟨hq, ?_⟩, hqp⟩
  intro r _ hrq hAr
  exact hnone r hAr hrq

end DefinableForcingTower
end ZFVP
