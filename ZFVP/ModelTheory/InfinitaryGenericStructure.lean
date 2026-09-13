import Mathlib.Tactic.FinCases
import ZFVP.ModelTheory.InfinitaryGenericSubstitution

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

def atom {n} (r : (limit L).Rel n) : Formula (limit L) n := .fo (.rel r (fun i ↦ .bvar i))

noncomputable instance extensionStructure : Structure (limit L) C.ExtensionDomain where
  func := fun _ f v ↦ CoordinateTerm.quotientFunc C.point C.refines C.coordinate_cofinal f v
  rel := fun _ r v ↦ CoordinateTerm.Eval C.point (atom r) (fun i ↦ (v i).out)

@[simp] theorem func_termClass {n} (f : (limit L).Func n) (v : Fin n → CoordinateTerm (limit L)) :
    Structure.func (self := C.extensionStructure) f (fun i ↦ C.termClass (v i)) =
      C.termClass (CoordinateTerm.func f v) :=
  CoordinateTerm.quotientFunc_mk C.point C.refines C.coordinate_cofinal f v

@[simp] theorem rel_termClass {n} (r : (limit L).Rel n) (v : Fin n → CoordinateTerm (limit L)) :
    Structure.rel (self := C.extensionStructure) r (fun i ↦ C.termClass (v i)) ↔
      CoordinateTerm.Eval C.point (atom r) v := by
  apply CoordinateTerm.eval_congr_iff C.point C.refines
  intro i
  exact @Quotient.mk_out _ C.coordinateSetoid (v i)

theorem atom_eq (b : Fin 2 → H.Domain) :
    Formula.WeakEval H.weakQuantifier (atom (Language.Eq.eq (L := limit L))) b ↔ b 0 = b 1 := by
  change Structure.rel (self := H.termStructure) (Language.Eq.eq (L := limit L)) b ↔ _
  have hb : b = ![b 0, b 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hb]
  exact Structure.Eq.eq (L := limit L) (b 0) (b 1)

theorem eval_atom_eq (v : Fin 2 → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (atom (Language.Eq.eq (L := limit L))) v ↔
      CoordinateTerm.Rel C.point (v 0) (v 1) := by
  constructor
  · rintro ⟨k, h, hh⟩
    exact ⟨k, h 0, h 1, fun b hb ↦ (atom_eq _).mp (hh b hb)⟩
  · rintro ⟨k, hs, ht, hh⟩
    have h : ∀ i, (v i).1 ≤ 1 + (C.point k).1 := by
      intro i
      fin_cases i
      · exact hs
      · exact ht
    refine ⟨k, h, ?_⟩
    intro b hb
    exact (atom_eq _).mpr (hh b hb)

instance extensionStructure_eq : Structure.Eq (limit L) C.ExtensionDomain where
  eq a b := by
    change CoordinateTerm.Eval C.point (atom Language.Eq.eq) (fun i ↦ (![a, b] i).out) ↔ a = b
    rw [C.eval_atom_eq]
    constructor
    · intro h
      have he := @Quotient.sound _ C.coordinateSetoid a.out b.out h
      exact (Quotient.out_eq a).symm.trans (he.trans (Quotient.out_eq b))
    · intro he
      subst b
      exact CoordinateTerm.rel_refl C.point C.coordinate_cofinal a.out

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary



