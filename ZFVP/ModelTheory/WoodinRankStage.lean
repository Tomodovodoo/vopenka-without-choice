import ZFVP.SetTheory.RankEnumerations
import ZFVP.ModelTheory.SaturatedTwoStepTransfer
import ZFVP.ModelTheory.ForcingCodeUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingRankEnumerationsFormula : SetTheorySemisentence 5 :=
  f“P R one θ κ. ∀ p ∈ P, !(binaryForcingTruthFormula shortRankEnumerationsFormula)
    p P R (!checkNameFormula one θ) (!checkNameFormula one κ)”

def woodinRankStageFormula : SetTheorySemisentence 3 :=
  f“i s K. !forcingRankEnumerationsFormula (!value.dfn (!forcingCodePFormula s) i)
    (!value.dfn (!forcingCodeRFormula s) i) (!value.dfn (!forcingCodetFormula s) i)
    i (!value.dfn K i)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ForcesRankEnumerations (P R one θ κ : V) : Prop :=
  ∀ p ∈ P, p ∈ forcingFormula P R shortRankEnumerationsFormula
    (standardTuple ![checkName one θ, checkName one κ])

instance forcingRankEnumerationsFormula_defined : Defined
    (fun v : Fin 5 → V ↦ ForcesRankEnumerations (v 0) (v 1) (v 2) (v 3) (v 4))
    forcingRankEnumerationsFormula :=
  ⟨fun v ↦ by simp [forcingRankEnumerationsFormula, ForcesRankEnumerations]⟩

def WoodinRankStage (i s K : V) : Prop :=
  ForcesRankEnumerations ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i) ((forcingCodet s) ‘ i) i (K ‘ i)

instance woodinRankStageFormula_defined : ℒₛₑₜ-relation₃[V] WoodinRankStage via woodinRankStageFormula :=
  ⟨fun v ↦ by simp [woodinRankStageFormula, WoodinRankStage]⟩

theorem ForcingContext.rankEnumerations_of_forced (A : ForcingContext V) {θ κ : V}
    (h : ForcesRankEnumerations A.P A.R A.one θ κ) :
    HasShortRankEnumerations (A.check θ) (A.check κ) := by
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  exact (Defined.eval_iff _).mp ((A.formula_truth shortRankEnumerationsFormula
    ![⟨checkName A.one θ, checkName_isName A.top.1 θ⟩,
      ⟨checkName A.one κ, checkName_isName A.top.1 κ⟩]).mpr
    ⟨p, hp, h p (A.generic.1.1 p hp)⟩)

end ZFVP
