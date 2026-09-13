import ZFVP.SetTheory.RealBaireTransfer
import ZFVP.SetTheory.RealPerfectTransfer

/-! Fixed parameter-free sentences for category and PSP on actual Dedekind reals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isRealNowhereDenseFormula : SetTheorySemisentence 1 :=
  f“P. P ⊆ !dedekindRealsFormula ∧
    ∀ a ∈ !internalRationalsFormula, ∀ b ∈ !internalRationalsFormula, !internalRationalLTFormula a b →
      ∃ r ∈ !internalRationalsFormula, ∃ t ∈ !internalRationalsFormula,
        !internalRationalLTFormula a r ∧ !internalRationalLTFormula r t ∧ !internalRationalLTFormula t b ∧
        ∀ x ∈ !realIntervalFormula r t, x ∉ P”

def isRealMeagreFormula : SetTheorySemisentence 1 :=
  f“A. ∃ f ∈ !function.dfn (!power.dfn (!realBasicCodesFormula)) (!isω),
    (∀ n ∈ !isω, !isRealNowhereDenseFormula (!realClosedFromFormula (!value.dfn f n))) ∧
    ∀ x ∈ A, ∃ n ∈ !isω, x ∈ !realClosedFromFormula (!value.dfn f n)”

def realBairePropertyFormula : SetTheorySemisentence 1 :=
  f“A. ∃ U, !isRealOpenFormula U ∧
    !isRealMeagreFormula (!union.dfn (!sdiff.dfn A U) (!sdiff.dfn U A))”

def isPerfectRealSetFormula : SetTheorySemisentence 1 :=
  f“P. (∃ S, S ⊆ !realBasicCodesFormula ∧ P = !realClosedFromFormula S) ∧ !isNonempty P ∧
    ∀ x ∈ P, ∀ a ∈ !internalRationalsFormula, ∀ b ∈ !internalRationalsFormula,
      x ∈ !realIntervalFormula a b → ∃ y ∈ P, y ∈ !realIntervalFormula a b ∧ y ≠ x”

def realPerfectSetPropertyFormula : SetTheorySemisentence 1 :=
  f“A. !CardLE.dfn A (!isω) ∨ ∃ P, !isPerfectRealSetFormula P ∧ P ⊆ A”

def realBairePropertySentence : SetTheorySentence :=
  f“∀ A, A ⊆ !dedekindRealsFormula → !realBairePropertyFormula A”

def realPerfectSetPropertySentence : SetTheorySentence :=
  f“∀ A, A ⊆ !dedekindRealsFormula → !realPerfectSetPropertyFormula A”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isRealNowhereDenseFormula_defined :
    ℒₛₑₜ-predicate[V] IsRealNowhereDense via isRealNowhereDenseFormula :=
  ⟨fun v ↦ by simp [isRealNowhereDenseFormula, IsRealNowhereDense]⟩

instance isRealMeagreFormula_defined : ℒₛₑₜ-predicate[V] IsRealMeagre via isRealMeagreFormula :=
  ⟨fun v ↦ by simp [isRealMeagreFormula, IsRealMeagre]⟩

instance realBairePropertyFormula_defined :
    ℒₛₑₜ-predicate[V] RealBaireProperty via realBairePropertyFormula :=
  ⟨fun v ↦ by simp [realBairePropertyFormula, RealBaireProperty]⟩

instance isPerfectRealSetFormula_defined :
    ℒₛₑₜ-predicate[V] IsPerfectRealSet via isPerfectRealSetFormula :=
  ⟨fun v ↦ by simp [isPerfectRealSetFormula, IsPerfectRealSet]⟩

instance realPerfectSetPropertyFormula_defined :
    ℒₛₑₜ-predicate[V] RealPerfectSetProperty via realPerfectSetPropertyFormula :=
  ⟨fun v ↦ by simp [realPerfectSetPropertyFormula, RealPerfectSetProperty]⟩

def AllRealBaireProperty (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ A : V, A ⊆ dedekindReals V → RealBaireProperty A

def AllRealPerfectSetProperty (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ A : V, A ⊆ dedekindReals V → RealPerfectSetProperty A

instance realBairePropertySentence_defined :
    Defined (fun _ : Fin 0 → V ↦ AllRealBaireProperty V) realBairePropertySentence :=
  ⟨fun v ↦ by simp [realBairePropertySentence, AllRealBaireProperty]⟩

instance realPerfectSetPropertySentence_defined :
    Defined (fun _ : Fin 0 → V ↦ AllRealPerfectSetProperty V) realPerfectSetPropertySentence :=
  ⟨fun v ↦ by simp [realPerfectSetPropertySentence, AllRealPerfectSetProperty]⟩

theorem allRealBaireProperty_of_internalDC (hDC : InternalDependentChoice V)
    (h : AllBaireProperty V) : AllRealBaireProperty V := allRealBaireProperty_of_cantor hDC h

theorem allRealPerfectSetProperty_of_internalDC (hDC : InternalDependentChoice V)
    (h : AllPerfectSetProperty V) : AllRealPerfectSetProperty V := allRealPerfectSetProperty_of_cantor hDC h

end ZFVP
