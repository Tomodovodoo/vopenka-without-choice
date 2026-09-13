import ZFVP.ModelTheory.InfinitaryGenericTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

abbrev coordinateSetoid := CoordinateTerm.setoid C.point C.refines C.coordinate_cofinal

def ExtensionDomain := Quotient C.coordinateSetoid

instance : Countable C.ExtensionDomain := inferInstanceAs (Countable (Quotient C.coordinateSetoid))

def termClass (t : CoordinateTerm (limit L)) : C.ExtensionDomain := Quotient.mk _ t

@[simp] theorem termClass_eq_iff (s t : CoordinateTerm (limit L)) :
    C.termClass s = C.termClass t ↔ CoordinateTerm.Rel C.point s t := Quotient.eq

def oldTerm (t : Semiterm (limit L) Empty 0) : C.ExtensionDomain := C.termClass ⟨0, t⟩

def newPoint : C.ExtensionDomain := C.termClass ⟨1, .bvar 0⟩

instance : Nonempty C.ExtensionDomain := ⟨C.newPoint⟩

theorem oldTerm_eq_iff (s t : Semiterm (limit L) Empty 0) :
    C.oldTerm s = C.oldTerm t ↔ s.val Fin.elim0 Empty.elim = t.val (s := H.termStructure) Fin.elim0 Empty.elim := by
  rw [oldTerm, oldTerm, termClass_eq_iff]
  constructor
  · rintro ⟨i, hs, ht, hh⟩
    obtain ⟨b, hb⟩ := (C.point i).realizable
    have he := hh b hb
    simpa only [show b ∘ Formula.rightEmbed hs = Fin.elim0 from Subsingleton.elim _ _,
      show b ∘ Formula.rightEmbed ht = Fin.elim0 from Subsingleton.elim _ _] using he
  · intro he
    refine ⟨0, Nat.zero_le _, Nat.zero_le _, ?_⟩
    intro b _
    simpa only [show b ∘ Formula.rightEmbed (Nat.zero_le (1 + (C.point 0).1)) = Fin.elim0
      from Subsingleton.elim _ _] using he

theorem newPoint_ne_oldTerm (t : Semiterm (limit L) Empty 0) : C.newPoint ≠ C.oldTerm t := by
  intro he
  obtain ⟨i, hi⟩ := (C.termClass_eq_iff ⟨1, .bvar 0⟩ ⟨0, t⟩).mp he
  obtain ⟨j, hj⟩ := C.avoids t
  have heq := CoordinateTerm.equalAt_persistent (C.refines (Nat.le_max_left i j)) hi
  have hne := hj (max i j) (Nat.le_max_right _ _)
  obtain ⟨b, hb⟩ := (C.point (max i j)).realizable
  obtain ⟨hs, ht, hh⟩ := heq
  have hlast : Formula.rightEmbed hs (0 : Fin 1) = Formula.lastCoordinate (C.point (max i j)).1 := by
    exact Formula.rightEmbed_last (n := 0) (m := (C.point (max i j)).1) hs
  have he := hh b hb
  change b (Formula.rightEmbed hs 0) = t.val (b ∘ Formula.rightEmbed ht) Empty.elim at he
  rw [hlast, show b ∘ Formula.rightEmbed ht = Fin.elim0 from Subsingleton.elim _ _] at he
  exact hne b hb he

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary

