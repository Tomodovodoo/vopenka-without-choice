import ZFVP.SetTheory.DeltaOneWoodinSeedColumns
import ZFVP.ModelTheory.WoodinSourceCode
import ZFVP.ModelTheory.DeltaOneForcingCodeComponents
import ZFVP.ModelTheory.BoundedForcingCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneWoodinSeedProjectionsFormula : SetTheorySemisentence 4 :=
  “G θ P π. ∃ e, !boundedEmptyFormula e ∧ ∃ u, !boundedSingletonFormula u e ∧
    ∃ Q, !sigmaOneWoodinInsertSeedFormula Q θ P u ∧
    ∃ C, !sigmaOneWoodinSeedProjectionColumnFormula C θ Q ∧ !sigmaOneWoodinSeedMatrixFormula G θ π C”

def sigmaOneWoodinSeedSectionsFormula : SetTheorySemisentence 4 :=
  “G θ E t. ∃ e, !boundedEmptyFormula e ∧ ∃ Q, !sigmaOneWoodinInsertSeedFormula Q θ t e ∧
    ∃ C, !sigmaOneWoodinSeedSectionColumnFormula C θ Q ∧ !sigmaOneWoodinSeedMatrixFormula G θ E C”

def sigmaOneWoodinSeedLiftsFormula : SetTheorySemisentence 4 :=
  “G θ P L. ∃ e, !boundedEmptyFormula e ∧ ∃ u, !boundedSingletonFormula u e ∧
    ∃ Q, !sigmaOneWoodinInsertSeedFormula Q θ P u ∧
    ∃ C, !sigmaOneWoodinSeedLiftColumnFormula C θ Q ∧ !sigmaOneWoodinSeedMatrixFormula G θ L C”

theorem sigmaOneWoodinSeedProjectionsFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedProjectionsFormula :=
  .exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedSingletonFormula_bounded.subst _))
      (.exs (.and (sigmaOneWoodinInsertSeedFormula_sigmaOne.subst _)
        (.exs (.and (sigmaOneWoodinSeedProjectionColumnFormula_sigmaOne.subst _)
          (sigmaOneWoodinSeedMatrixFormula_sigmaOne.subst _))))))))

theorem sigmaOneWoodinSeedSectionsFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedSectionsFormula :=
  .exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
    (.exs (.and (sigmaOneWoodinInsertSeedFormula_sigmaOne.subst _)
      (.exs (.and (sigmaOneWoodinSeedSectionColumnFormula_sigmaOne.subst _)
        (sigmaOneWoodinSeedMatrixFormula_sigmaOne.subst _))))))

theorem sigmaOneWoodinSeedLiftsFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSeedLiftsFormula :=
  .exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedSingletonFormula_bounded.subst _))
      (.exs (.and (sigmaOneWoodinInsertSeedFormula_sigmaOne.subst _)
        (.exs (.and (sigmaOneWoodinSeedLiftColumnFormula_sigmaOne.subst _)
          (sigmaOneWoodinSeedMatrixFormula_sigmaOne.subst _))))))))

def sigmaOneWoodinSourceCodeFormula : SetTheorySemisentence 3 :=
  “z θ s. ∃ P, !sigmaOneForcingCodePFormula P s ∧ ∃ R, !sigmaOneForcingCodeRFormula R s ∧
    ∃ π, !sigmaOneForcingCodeπFormula π s ∧ ∃ E, !sigmaOneForcingCodeEFormula E s ∧
    ∃ L, !sigmaOneForcingCodeLFormula L s ∧ ∃ t, !sigmaOneForcingCodetFormula t s ∧
    ∃ e, !boundedEmptyFormula e ∧ ∃ u, !boundedSingletonFormula u e ∧ ∃ v, !boundedProductFormula v u u ∧
    ∃ P', !sigmaOneWoodinInsertSeedFormula P' θ P u ∧ ∃ R', !sigmaOneWoodinInsertSeedFormula R' θ R v ∧
    ∃ π', !sigmaOneWoodinSeedProjectionsFormula π' θ P π ∧ ∃ E', !sigmaOneWoodinSeedSectionsFormula E' θ E t ∧
    ∃ L', !sigmaOneWoodinSeedLiftsFormula L' θ P L ∧ ∃ t', !sigmaOneWoodinInsertSeedFormula t' θ t e ∧
    !boundedForcingCodeFormula z P' R' π' E' L' t'”

def piOneWoodinSourceCodeFormula : SetTheorySemisentence 3 :=
  “z θ s. !IsOrdinal.dfn θ ∧ ∀ w, !sigmaOneWoodinSourceCodeFormula w θ s → z = w”

theorem sigmaOneWoodinSourceCodeFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinSourceCodeFormula := by
  exact (.exs (.and (sigmaOneForcingCodePFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodeRFormula_sigmaOne.subst _)
      (.exs (.and (sigmaOneForcingCodeπFormula_sigmaOne.subst _)
        (.exs (.and (sigmaOneForcingCodeEFormula_sigmaOne.subst _)
          (.exs (.and (sigmaOneForcingCodeLFormula_sigmaOne.subst _)
            (.exs (.and (sigmaOneForcingCodetFormula_sigmaOne.subst _)
              (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
                (.exs (.and (.bounded (boundedSingletonFormula_bounded.subst _))
                  (.exs (.and (.bounded (boundedProductFormula_bounded.subst _))
                    (.exs (.and (sigmaOneWoodinInsertSeedFormula_sigmaOne.subst _)
                      (.exs (.and (sigmaOneWoodinInsertSeedFormula_sigmaOne.subst _)
                        (.exs (.and (sigmaOneWoodinSeedProjectionsFormula_sigmaOne.subst _)
                          (.exs (.and (sigmaOneWoodinSeedSectionsFormula_sigmaOne.subst _)
                            (.exs (.and (sigmaOneWoodinSeedLiftsFormula_sigmaOne.subst _)
                              (.exs (.and (sigmaOneWoodinInsertSeedFormula_sigmaOne.subst _)
                                (.bounded (boundedForcingCodeFormula_bounded.subst _))))))))))))))))))))))))))))))))

theorem piOneWoodinSourceCodeFormula_piOne : IsPiFormula 1 piOneWoodinSourceCodeFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.or (sigmaOneWoodinSourceCodeFormula_sigmaOne.subst _).neg (.bounded (.rel _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneWoodinSeedProjectionsFormula_defined :
    ℒₛₑₜ-relation₄[V] (fun G θ P π ↦ IsOrdinal θ ∧ G = woodinSeedProjections θ P π)
      via sigmaOneWoodinSeedProjectionsFormula :=
  ⟨fun v ↦ by simp [sigmaOneWoodinSeedProjectionsFormula, woodinSeedProjections]⟩

instance sigmaOneWoodinSeedSectionsFormula_defined :
    ℒₛₑₜ-relation₄[V] (fun G θ E t ↦ IsOrdinal θ ∧ G = woodinSeedSections θ E t)
      via sigmaOneWoodinSeedSectionsFormula :=
  ⟨fun v ↦ by simp [sigmaOneWoodinSeedSectionsFormula, woodinSeedSections]⟩

instance sigmaOneWoodinSeedLiftsFormula_defined :
    ℒₛₑₜ-relation₄[V] (fun G θ P L ↦ IsOrdinal θ ∧ G = woodinSeedLifts θ P L)
      via sigmaOneWoodinSeedLiftsFormula :=
  ⟨fun v ↦ by simp [sigmaOneWoodinSeedLiftsFormula, woodinSeedLifts]⟩

instance sigmaOneWoodinSourceCodeFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun z θ s ↦ IsOrdinal θ ∧ z = woodinSourceCode θ s)
      via sigmaOneWoodinSourceCodeFormula :=
  ⟨fun v ↦ by simp [sigmaOneWoodinSourceCodeFormula, woodinSourceCode]⟩

instance piOneWoodinSourceCodeFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun z θ s ↦ IsOrdinal θ ∧ z = woodinSourceCode θ s)
      via piOneWoodinSourceCodeFormula :=
  ⟨fun v ↦ by simp [piOneWoodinSourceCodeFormula]; exact fun h ↦ Or.inl h⟩

end ZFVP
