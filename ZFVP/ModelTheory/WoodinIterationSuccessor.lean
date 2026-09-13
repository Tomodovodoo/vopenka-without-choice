import ZFVP.ModelTheory.ForcingSuccessorCode
import ZFVP.ModelTheory.WoodinSuccessorInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinIterationStage (s K i : V) : V :=
  woodinStageCode ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
    ((forcingCodet s) ‘ i) (K ‘ i)

noncomputable def woodinIterationSuccessor (k s K : V) : V :=
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := K ‘ k
  let δ := woodinPrefixCutoff P R o κ
  forcingSuccessorCode k s (saturatedWoodinPrefixPosetName P R o κ δ)
    (saturatedWoodinPrefixOrderName P R o κ δ) ∅

noncomputable def woodinIterationCardinalNext (k s K : V) : V :=
  forcingFamilyNext (succ k) K
    (woodinStageCardinal (woodinSuccessorStep (woodinIterationStage s K k)))

theorem woodinIterationSuccessor_valid {k s K δ : V} [IsOrdinal k]
    (hs : IsForcingIterationCode (succ k) s)
    (hκ : ∀ p ∈ (forcingCodeP s) ‘ k, p ∈ forcingFormula
      ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) regularCardinalFormula
      (standardTuple ![checkName ((forcingCodet s) ‘ k) (K ‘ k)]))
    (hδ : IsWoodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      ((forcingCodet s) ‘ k) (K ‘ k) δ)
    (hP : (forcingCodeP s) ‘ k ∈ hierarchy
      (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
        ((forcingCodet s) ‘ k) (K ‘ k))) :
    IsForcingIterationCode (succ (succ k)) (woodinIterationSuccessor k s K) := by
  exact forcingSuccessorCode_valid hs (saturatedWoodinPrefix_iterand_of_cutoff
    (hs.system.order.preorder k (by simp)) (hs.system.tops.top k (by simp)) hκ
    (woodinPrefixCutoff_spec hδ).2.1 hP)

theorem woodinIterationSuccessor_extends {k s : V}
    (hs : IsForcingIterationCode (succ k) s) (K : V) :
    ForcingCodeExtends s (woodinIterationSuccessor k s K) :=
  forcingSuccessorCode_extends hs _ _ _

theorem woodinIterationSuccessor_stage (k s K : V) :
    woodinIterationStage (woodinIterationSuccessor k s K)
      (woodinIterationCardinalNext k s K) (succ k) =
      woodinSuccessorStep (woodinIterationStage s K k) := by
  simp [woodinIterationStage, woodinIterationSuccessor, woodinIterationCardinalNext,
    woodinSuccessorStep, woodinSuccessorAt, forcingFamilyNext_new]

theorem woodinIterationSuccessor_old {k s K i : V} (hi : i ∈ succ k) :
    woodinIterationStage (woodinIterationSuccessor k s K)
      (woodinIterationCardinalNext k s K) i = woodinIterationStage s K i := by
  simp only [woodinIterationStage, woodinIterationSuccessor, forcingSuccessorCode,
    forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code, forcingCodet_code,
    woodinIterationCardinalNext, forcingFamilyNext_old hi]

theorem woodinIterationCardinalNext_table (k s K : V) :
    IsIterationTable (succ (succ k)) (woodinIterationCardinalNext k s K) :=
  forcingFamilyNext_table _ _ _

theorem woodinIterationSuccessor_stages {k s K δ : V}
    (hstage : ∀ i ∈ succ k, IsWoodinStage (woodinIterationStage s K i))
    (hδ : IsWoodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      ((forcingCodet s) ‘ k) (K ‘ k) δ)
    (hP : (forcingCodeP s) ‘ k ∈ hierarchy
      (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
        ((forcingCodet s) ‘ k) (K ‘ k))) :
    ∀ i ∈ succ (succ k), IsWoodinStage (woodinIterationStage
      (woodinIterationSuccessor k s K) (woodinIterationCardinalNext k s K) i) := by
  intro i hi
  rcases mem_succ_iff.mp hi with rfl | hi
  · rw [woodinIterationSuccessor_stage]
    apply woodinSuccessorStep_stage (hstage k (by simp)) (δ := δ)
    · simpa [woodinIterationStage] using hδ
    · simpa [woodinIterationStage] using hP
  · rw [woodinIterationSuccessor_old hi]
    exact hstage i hi

end ZFVP
