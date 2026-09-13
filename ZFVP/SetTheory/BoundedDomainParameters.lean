import ZFVP.SetTheory.BoundedDomainRelativization

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedDomainParametersFormula {n : ℕ} (φ : SetTheorySemisentence n) : SetTheorySemisentence (n + 1) :=
  boundedDomainRelativize φ (.bvar 0) (Rew.subst (fun i ↦ .bvar i.succ))

theorem boundedDomainParametersFormula_bounded {n : ℕ} (φ : SetTheorySemisentence n) :
    IsBoundedSetFormula (boundedDomainParametersFormula φ) :=
  boundedDomainRelativize_bounded φ _ _

variable {V : Type*} [SetStructure V]

theorem eval_boundedDomainParametersFormula {n : ℕ} (φ : SetTheorySemisentence n)
    (A : V) (v : Fin n → SetDomain A) :
    (boundedDomainParametersFormula φ).Evalb (A :> (fun i ↦ (v i).val)) ↔ φ.Evalb v := by
  apply eval_boundedDomainRelativize φ _ _ v _ rfl
  intro s
  cases s with
  | bvar i => rfl
  | fvar e => exact Empty.elim e
  | func f ts => exact Empty.elim f

end ZFVP
