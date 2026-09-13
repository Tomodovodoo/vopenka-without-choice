import ZFVP.SetTheory.LebesgueNull
import ZFVP.SetTheory.SetUltrafilter
import ZFVP.SetTheory.HartogsDictionary
import ZFVP.SetTheory.ChoiceDictionary
import ZFVP.SetTheory.VopenkaScheme
import ZFVP.ModelTheory.CodedZFVPExternal

/-! The full target theory of the Solovay consistency corollary.

The regularity sentences quantify over every internal set of Cantor-space reals.
The ultrafilter sentence places a nonprincipal internally ordinal-complete
ultrafilter on the internal Hartogs number of omega, hence on internal omega-one.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def solovayComplementFormula : SetTheorySemisentence 3 :=
  f“Y K X. ∀ z, z ∈ Y ↔ z ∈ K ∧ z ∉ X”

def solovayIntersectionFormula : SetTheorySemisentence 4 :=
  f“Y K I g. ∀ z, z ∈ Y ↔ z ∈ K ∧ ∀ i ∈ I, z ∈ !value.dfn g i”

def solovaySetUltrafilterFormula : SetTheorySemisentence 2 :=
  f“K U. U ⊆ !power.dfn K ∧ K ∈ U ∧ !isEmpty ∉ U ∧
    (∀ X ∈ U, ∀ Y, Y ⊆ K → X ⊆ Y → Y ∈ U) ∧
    (∀ X ∈ U, ∀ Y ∈ U, !inter.dfn X Y ∈ U) ∧
    ∀ X, X ⊆ K → X ∈ U ∨ !solovayComplementFormula K X ∈ U”

def solovayNonprincipalUltrafilterFormula : SetTheorySemisentence 2 :=
  f“K U. !solovaySetUltrafilterFormula K U ∧ ∀ x ∈ K, !singleton.dfn x ∉ U”

def solovayOrdinalCompleteFormula : SetTheorySemisentence 2 :=
  f“K U. ∀ I ∈ K, ∀ g ∈ !function.dfn U I, !solovayIntersectionFormula K I g ∈ U”

def omegaOneCompleteUltrafilterSentence : SetTheorySentence :=
  f“∃ U, !solovayNonprincipalUltrafilterFormula (!hartogsNumberFormula (!isω)) U ∧
    !solovayOrdinalCompleteFormula (!hartogsNumberFormula (!isω)) U”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance solovayComplementFormula_defined :
    ℒₛₑₜ-function₂[V] relativeComplement via solovayComplementFormula :=
  ⟨fun v ↦ by simp [solovayComplementFormula,
    mem_ext_iff (y := relativeComplement (v 1) (v 2)), mem_relativeComplement_iff]⟩

instance solovayIntersectionFormula_defined :
    ℒₛₑₜ-function₃[V] indexedIntersection via solovayIntersectionFormula :=
  ⟨fun v ↦ by simp [solovayIntersectionFormula,
    mem_ext_iff (y := indexedIntersection (v 1) (v 2) (v 3)), mem_indexedIntersection_iff]⟩

instance solovaySetUltrafilterFormula_defined :
    ℒₛₑₜ-relation[V] IsSetUltrafilter via solovaySetUltrafilterFormula :=
  ⟨fun v ↦ by simp [solovaySetUltrafilterFormula, IsSetUltrafilter]⟩

instance solovayNonprincipalUltrafilterFormula_defined :
    ℒₛₑₜ-relation[V] IsNonprincipalSetUltrafilter via solovayNonprincipalUltrafilterFormula :=
  ⟨fun v ↦ by simp [solovayNonprincipalUltrafilterFormula, IsNonprincipalSetUltrafilter]⟩

instance solovayOrdinalCompleteFormula_defined :
    ℒₛₑₜ-relation[V] IsOrdinalComplete via solovayOrdinalCompleteFormula :=
  ⟨fun v ↦ by simp [solovayOrdinalCompleteFormula, IsOrdinalComplete]⟩

instance omegaOneCompleteUltrafilterSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ ∃ U : V,
      IsNonprincipalSetUltrafilter (hartogsNumber (ω : V)) U ∧
      IsOrdinalComplete (hartogsNumber (ω : V)) U) omegaOneCompleteUltrafilterSentence :=
  ⟨fun v ↦ by simp [omegaOneCompleteUltrafilterSentence]⟩

/-- ZF + every VP instance + DC + LM + BP + PSP + not AC, with a complete
nonprincipal ultrafilter on internal omega-one. -/
def solovayTheory : Theory ℒₛₑₜ :=
  insert dependentChoiceSentence
    (insert lebesgueMeasurableSentence
      (insert bairePropertySentence
        (insert perfectSetPropertySentence
          (insert (∼choiceFunctionSentence)
            (insert omegaOneCompleteUltrafilterSentence zfVPTheory)))))

end ZFVP
