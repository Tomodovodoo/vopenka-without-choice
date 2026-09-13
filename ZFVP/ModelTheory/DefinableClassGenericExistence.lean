import ZFVP.ModelTheory.DefinableClassGeneric
import ZFVP.ModelTheory.ClassForcingTowerGeneric
import Foundation.FirstOrder.Basic.Coding

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Countable V]

/-- Rasiowa--Sikorski for definable dense classes, enumerated by formulas
with parameters from the countable ground model. -/
theorem exists_genericForDefinableDenseClasses (P : V → Prop) (R : V → V → Prop)
    (hrefl : ∀ p, P p → R p p)
    (htrans : ∀ p, P p → ∀ q, P q → ∀ r, P r → R p q → R q r → R p r)
    {p : V} (hp : P p) :
    ∃ G : Set V, IsGenericForDefinableDenseClasses P R G ∧ p ∈ G := by
  classical
  let Q := {q : V // P q}
  let : Preorder Q :=
    { le := fun q r ↦ R r.val q.val
      le_refl := fun q ↦ hrefl q.val q.property
      le_trans := fun q r s hqr hrs ↦
        htrans s.val s.property r.val r.property q.val q.property hrs hqr }
  let I := {φ : Semiformula ℒₛₑₜ V 1 //
    ClassForcingDense P R (fun q ↦ φ.Eval ![q] id)}
  let : Encodable I := Encodable.ofCountable I
  let ds : I → Order.Cofinal Q := fun D ↦
    { carrier := {q | D.val.Eval ![q.val] id}
      isCofinal := by
        intro q
        obtain ⟨r, hr, hrq⟩ := D.property.2 q.val q.property
        exact ⟨⟨r, D.property.1 r hr⟩, hr, hrq⟩ }
  let J := Order.idealOfCofinals (⟨p, hp⟩ : Q) ds
  let G : Set V := {q | ∃ hq : P q, (⟨q, hq⟩ : Q) ∈ J}
  have hpG : p ∈ G := ⟨hp, Order.mem_idealOfCofinals _ _⟩
  refine ⟨G, ⟨?_, ?_⟩, hpG⟩
  · refine ⟨fun q hq ↦ hq.choose, ⟨p, hpG⟩, ?_, ?_⟩
    · intro q hq r hr hqr
      obtain ⟨hqP, hqJ⟩ := hq
      exact ⟨hr, J.lower (show (⟨r, hr⟩ : Q) ≤ ⟨q, hqP⟩ from hqr) hqJ⟩
    · intro q hq r hr
      obtain ⟨hqP, hqJ⟩ := hq
      obtain ⟨hrP, hrJ⟩ := hr
      obtain ⟨s, hs, hsq, hsr⟩ := J.directed (⟨q, hqP⟩ : Q) hqJ (⟨r, hrP⟩ : Q) hrJ
      exact ⟨s.val, ⟨s.property, hs⟩, hsq, hsr⟩
  · intro D hD hd
    obtain ⟨φ, hφ⟩ := hD.definable
    have hφD (q : V) : φ.Eval ![q] id ↔ D q := hφ ![q]
    have hdφ : ClassForcingDense P R (fun q ↦ φ.Eval ![q] id) := by
      refine ⟨fun q hq ↦ hd.1 q ((hφD q).mp hq), ?_⟩
      intro q hq
      obtain ⟨r, hr, hrq⟩ := hd.2 q hq
      exact ⟨r, (hφD r).mpr hr, hrq⟩
    obtain ⟨q, hqD, hqJ⟩ :=
      Order.cofinal_meets_idealOfCofinals (⟨p, hp⟩ : Q) ds (⟨φ, hdφ⟩ : I)
    exact ⟨q.val, ⟨q.property, hqJ⟩, (hφD q.val).mp hqD⟩

variable [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem DefinableForcingTower.exists_generic (T : DefinableForcingTower V)
    {p : V} (hp : T.Condition p) :
    ∃ G : Set V, IsGenericForDefinableDenseClasses T.Condition T.LE G ∧ p ∈ G :=
  exists_genericForDefinableDenseClasses T.Condition T.LE
    (fun _ hq ↦ T.le_refl hq)
    (fun _ _ _ _ _ _ hpq hqr ↦ T.le_trans hpq hqr) hp

end ZFVP
