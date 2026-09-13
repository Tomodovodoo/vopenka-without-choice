import ZFVP.ModelTheory.ForcingWellOrdering
import ZFVP.SetTheory.CardinalDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def ordinalSurjectionFormula : SetTheorySemisentence 3 :=
  f“f a X. f ∈ !function.dfn X a ∧ !range.dfn f = X”

def forcedOrdinalSurjectionWellOrderFormula : SetTheorySemisentence 7 :=
  f“P R o t p a X. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P t ∧ !IsOrdinal.dfn a ∧ !wellOrderableFormula P ∧
    !(checkedTripleForcingFormula ordinalSurjectionFormula) P R o t p a X →
      !wellOrderableFormula X”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_ordinalSurjectionFormula (v : Fin 3 → V) :
    ordinalSurjectionFormula.Evalb v ↔ v 0 ∈ (v 2) ^ (v 1) ∧ range (v 0) = v 2 := by
  simp [ordinalSurjectionFormula]

theorem eval_forcedOrdinalSurjectionWellOrderFormula (v : Fin 7 → V) :
    forcedOrdinalSurjectionWellOrderFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingName (v 0) (v 3) → IsOrdinal (v 5) → IsWellOrderable (v 0) →
      v 4 ∈ forcingFormula (v 0) (v 1) ordinalSurjectionFormula
        (standardTuple ![v 3, checkName (v 2) (v 5), checkName (v 2) (v 6)]) →
      IsWellOrderable (v 6)) := by
  simp [forcedOrdinalSurjectionWellOrderFormula]

theorem wellOrderable_of_forced_ordinal_surjection_countable [Countable V]
    {P R one τ p α X : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hα : IsOrdinal α) (hP : IsWellOrderable P)
    (hf : p ∈ forcingFormula P R ordinalSurjectionFormula
      (standardTuple ![τ, checkName one α, checkName one X])) : IsWellOrderable X := by
  have hp : p ∈ P := (forcingFormula_regular hR ordinalSurjectionFormula _).1 p hf
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let S : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let t : ForcingName P := ⟨τ, hτ⟩
  let a : ForcingName P := ⟨checkName one α, checkName_isName htop.1 α⟩
  let x : ForcingName P := ⟨checkName one X, checkName_isName htop.1 X⟩
  have he := (S.formula_truth ordinalSurjectionFormula ![t, a, x]).mpr ⟨p, hpG, hf⟩
  have hh := (eval_ordinalSurjectionFormula _).mp he
  have : IsOrdinal (S.check α) := (S.check_ordinal_iff α).mpr hα
  exact S.wellOrderable_of_check hP
    (wellOrderable_of_surjective_function (ordinal_wellOrderable (S.check α)) hh.1 hh.2)

theorem forcedOrdinalSurjectionWellOrderFormula_valid (v : Fin 7 → V) :
    forcedOrdinalSurjectionWellOrderFormula.Evalb v := by
  exact eval_of_countable_zf forcedOrdinalSurjectionWellOrderFormula (by
    intro W _ _ _ _ b
    exact (eval_forcedOrdinalSurjectionWellOrderFormula b).mpr
      (fun hR htop hτ hα hP hf ↦
        wellOrderable_of_forced_ordinal_surjection_countable hR htop hτ hα hP hf)) v

theorem wellOrderable_of_forced_ordinal_surjection
    {P R one τ p α X : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hα : IsOrdinal α) (hP : IsWellOrderable P)
    (hf : p ∈ forcingFormula P R ordinalSurjectionFormula
      (standardTuple ![τ, checkName one α, checkName one X])) : IsWellOrderable X := by
  exact (eval_forcedOrdinalSurjectionWellOrderFormula ![P, R, one, τ, p, α, X]).mp
    (forcedOrdinalSurjectionWellOrderFormula_valid ![P, R, one, τ, p, α, X]) hR htop hτ hα hP hf

end ZFVP

