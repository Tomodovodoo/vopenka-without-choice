import ZFVP.SetTheory.BoundedDomainRelativization

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedDomainUnaryFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 2 :=
  boundedDomainRelativize φ (.bvar 0) (Rew.subst ![.bvar 1])

theorem boundedDomainUnaryFormula_bounded (φ : SetTheorySemisentence 1) :
    IsBoundedSetFormula (boundedDomainUnaryFormula φ) :=
  boundedDomainRelativize_bounded φ _ _

variable {V : Type*} [SetStructure V]

theorem eval_boundedDomainUnaryFormula (φ : SetTheorySemisentence 1)
    (A : V) (x : SetDomain A) :
    (boundedDomainUnaryFormula φ).Evalb ![A, x.val] ↔ φ.Evalb ![x] := by
  apply eval_boundedDomainRelativize φ _ _ ![x] ![A, x.val] rfl
  intro s
  cases s with
  | bvar i => have hi : i = 0 := Fin.eq_zero i; subst i; rfl
  | fvar e => exact Empty.elim e
  | func f ts => exact Empty.elim f

end ZFVP
