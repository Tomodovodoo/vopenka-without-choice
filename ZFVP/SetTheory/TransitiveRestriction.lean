import ZFVP.SetTheory.MembershipIso
import Foundation.FirstOrder.SetTheory.Ordinal

/-! Restriction between transitive ambient sets, via syntactic relativization. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

/-- Transitivity identifies the elements of `a` computed inside `M`
with all the ambient elements of `a`. -/
def nestedDomainEquiv (M : V) [hM : IsTransitive M] (a : SetDomain M) :
    SetDomain a ≃ SetDomain a.val where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hM.transitive a.val a.property x.val x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nestedDomainEquiv_mem (M : V) [IsTransitive M] (a : SetDomain M)
    (x y : SetDomain a) :
    nestedDomainEquiv M a x ∈ nestedDomainEquiv M a y ↔ x ∈ y := Iff.rfl

/-- The restriction of an elementary map between transitive sets.
No satisfaction-set existence hypothesis is needed for this external semantic proof. -/
def transitiveRestriction (M N : V) [IsTransitive M] [IsTransitive N]
    (j : ElementaryMap (SetDomain M) (SetDomain N)) (a : SetDomain M) :
    ElementaryMap (SetDomain a.val) (SetDomain (j a).val) :=
  (ElementaryMap.ofMembershipIso (nestedDomainEquiv N (j a))
      (nestedDomainEquiv_mem N (j a))).comp
    ((j.restrict a).comp
      (ElementaryMap.ofMembershipIso (nestedDomainEquiv M a).symm (fun _ _ ↦ Iff.rfl)))

theorem transitiveRestriction_apply (M N : V) [hM : IsTransitive M] [IsTransitive N]
    (j : ElementaryMap (SetDomain M) (SetDomain N)) (a : SetDomain M)
    (x : SetDomain a.val) :
    (transitiveRestriction M N j a x).val =
      (j ⟨x.val, hM.transitive a.val a.property x.val x.property⟩).val := rfl

end ZFVP
