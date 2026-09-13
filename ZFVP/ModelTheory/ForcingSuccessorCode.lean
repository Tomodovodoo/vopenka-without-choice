import ZFVP.SetTheory.ForcingIterationCode
import ZFVP.ModelTheory.ForcingIterationColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingSuccessorCode (k s Q S u : V) : V :=
  let C := twoStepConditions ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) Q u
  forcingIterationCodeNext (succ k) s C
    (twoStepOrder ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) Q S u)
    (successorProjectionColumn (succ k) C (forcingCodeπ s) k)
    (successorSectionColumn (succ k) (forcingCodeP s) (forcingCodeE s) k u)
    (successorLiftColumn (succ k) C (forcingCodeP s) (forcingCodeL s) k)
    ⟨(forcingCodet s) ‘ k, u⟩ₖ

theorem forcingSuccessorCode_valid {k s Q S u : V} [IsOrdinal k]
    (hs : IsForcingIterationCode (succ k) s)
    (hQ : IsForcingIterand ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) Q S u) :
    IsForcingIterationCode (succ (succ k)) (forcingSuccessorCode k s Q S u) := by
  apply hs.extend
  apply hs.system.successorColumn (by simp) _ hQ
  intro i hi
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact subset_refl _
  · exact IsOrdinal.toIsTransitive.transitive _ hi

theorem forcingSuccessorCode_extends {k s : V}
    (hs : IsForcingIterationCode (succ k) s) (Q S u : V) :
    ForcingCodeExtends s (forcingSuccessorCode k s Q S u) :=
  hs.extends_next _ _ _ _ _ _

@[simp] theorem forcingSuccessorCode_poset (k s Q S u : V) :
    (forcingCodeP (forcingSuccessorCode k s Q S u)) ‘ (succ k) =
      twoStepConditions ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) Q u := by
  simp [forcingSuccessorCode, forcingIterationCodeNext, forcingFamilyNext_new]

@[simp] theorem forcingSuccessorCode_order (k s Q S u : V) :
    (forcingCodeR (forcingSuccessorCode k s Q S u)) ‘ (succ k) =
      twoStepOrder ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) Q S u := by
  simp [forcingSuccessorCode, forcingIterationCodeNext, forcingFamilyNext_new]

@[simp] theorem forcingSuccessorCode_top (k s Q S u : V) :
    (forcingCodet (forcingSuccessorCode k s Q S u)) ‘ (succ k) =
      ⟨(forcingCodet s) ‘ k, u⟩ₖ := by
  simp [forcingSuccessorCode, forcingIterationCodeNext, forcingFamilyNext_new]

end ZFVP
