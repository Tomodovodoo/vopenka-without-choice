import ZFVP.ModelTheory.InfinitaryGenericDomain

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

theorem closedTerm_val (t : Semiterm (limit L) Empty 0) :
    t.val (s := H.termStructure) Fin.elim0 Empty.elim = H.classOf t := by
  induction t with
  | bvar i => exact i.elim0
  | fvar i => exact i.elim
  | func f ts ih =>
    change Structure.func f (fun i ↦ (ts i).val Fin.elim0 Empty.elim) = _
    rw [funext ih]
    exact H.func_classOf f ts

noncomputable def oldEmbedding (x : H.Domain) : C.ExtensionDomain := C.oldTerm x.out

@[simp] theorem oldEmbedding_classOf (t : Semiterm (limit L) Empty 0) :
    C.oldEmbedding (H.classOf t) = C.oldTerm t := by
  apply (C.oldTerm_eq_iff _ _).mpr
  rw [closedTerm_val, closedTerm_val]
  exact Quotient.out_eq _

theorem oldEmbedding_injective : Function.Injective C.oldEmbedding := by
  intro x y he
  have hv := (C.oldTerm_eq_iff x.out y.out).mp he
  rw [closedTerm_val, closedTerm_val] at hv
  exact (Quotient.out_eq x).symm.trans (hv.trans (Quotient.out_eq y))

theorem newPoint_not_mem_oldRange : C.newPoint ∉ Set.range C.oldEmbedding := by
  rintro ⟨x, hx⟩
  exact C.newPoint_ne_oldTerm x.out hx.symm

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary
