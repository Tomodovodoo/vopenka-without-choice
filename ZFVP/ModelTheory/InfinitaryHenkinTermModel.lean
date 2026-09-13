import ZFVP.ModelTheory.InfinitaryHenkinEquality

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

def Domain := Quotient H.termSetoid

def classOf (t : Semiterm (limit L) Empty 0) : H.Domain := Quotient.mk H.termSetoid t

instance domain_countable : Countable H.Domain := inferInstanceAs (Countable (Quotient H.termSetoid))

instance domain_nonempty : Nonempty H.Domain :=
  ⟨H.classOf (.func (.inr (.const 0)) Fin.elim0)⟩

theorem classOf_eq_iff (s t : Semiterm (limit L) Empty 0) :
    H.classOf s = H.classOf t ↔ H.termRel s t := ⟨@Quotient.exact _ H.termSetoid s t, @Quotient.sound _ H.termSetoid s t⟩

theorem representative_rel (t : Semiterm (limit L) Empty 0) :
    H.termRel (H.classOf t).out t := @Quotient.mk_out _ H.termSetoid t

noncomputable instance termStructure : Structure (limit L) H.Domain where
  func := fun _ f v ↦ H.classOf (.func f (fun i ↦ (v i).out))
  rel := fun _ r v ↦ Formula.fo (.rel r (fun i ↦ (v i).out)) ∈ H.carrier

theorem func_classOf {n} (f : (limit L).Func n) (v : Fin n → Semiterm (limit L) Empty 0) :
    Structure.func (self := H.termStructure) f (fun i ↦ H.classOf (v i)) = H.classOf (.func f v) := by
  apply Quotient.sound
  exact H.func_termRel f _ _ (fun i ↦ H.representative_rel (v i))

theorem rel_classOf {n} (r : (limit L).Rel n) (v : Fin n → Semiterm (limit L) Empty 0) :
    Structure.rel (self := H.termStructure) r (fun i ↦ H.classOf (v i)) ↔
      Formula.fo (.rel r v) ∈ H.carrier :=
  H.rel_mem_congr r _ _ (fun i ↦ H.representative_rel (v i))

instance termStructure_eq : Structure.Eq (limit L) H.Domain where
  eq a b := by
    change Formula.fo (.rel Language.Eq.eq (fun i ↦ (![a, b] i).out)) ∈ H.carrier ↔ a = b
    have hv : (fun i ↦ (![a, b] i).out) = ![a.out, b.out] := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => cases i using Fin.cases with
          | zero => rfl
          | succ i => exact i.elim0
    rw [hv]
    change H.termRel a.out b.out ↔ a = b
    constructor
    · intro h
      have he := @Quotient.sound _ H.termSetoid a.out b.out h
      exact (Quotient.out_eq a).symm.trans (he.trans (Quotient.out_eq b))
    · intro h
      subst b
      exact H.termRel_refl a.out

theorem term_val {n} (t : Semiterm (limit L) Empty n)
    (v : Fin n → Semiterm (limit L) Empty 0) :
    Semiterm.val (s := H.termStructure) (fun i ↦ H.classOf (v i)) Empty.elim t =
      H.classOf ((Rew.subst v) t) := by
  induction t with
  | bvar i => rfl
  | fvar i => exact i.elim
  | func f ts ih =>
    change Structure.func f (fun i ↦ Semiterm.val _ _ (ts i)) = _
    rw [funext ih]
    exact H.func_classOf f _

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary


