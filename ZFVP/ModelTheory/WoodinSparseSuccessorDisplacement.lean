import ZFVP.ModelTheory.WoodinCanonicalTailNameAction
import ZFVP.ModelTheory.WoodinSparseActualAutomorphisms
import ZFVP.ModelTheory.WoodinSparseStageInvariant
import ZFVP.ModelTheory.WoodinCanonicalTailNameUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseSuccessorDisplacement (k p q : V) : V :=
  let c := woodinSparsePrefixCode (succ k);
  let P := (forcingCodeP c) ‘ k;
  let R := (forcingCodeR c) ‘ k;
  let o := (forcingCodet c) ‘ k;
  let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k;
  sparseCanonicalPrefixDisplacement (woodinSourceIndex (succ k)) P R o κ
    (woodinPrefixCutoff P R o κ) p q

instance woodinSparseSuccessorDisplacement_definable :
    ℒₛₑₜ-function₃[V] woodinSparseSuccessorDisplacement := by
  unfold woodinSparseSuccessorDisplacement
  dsimp only
  apply sparseCanonicalPrefixDisplacement_comp
  · definability
  · definability
  · definability
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability
  · definability
  · definability

variable {Ω k : V} [IsOrdinal k]
local notation "c" => woodinSparsePrefixCode (succ k)
local notation "P" => (forcingCodeP c) ‘ k
local notation "R" => (forcingCodeR c) ‘ k
local notation "o" => (forcingCodet c) ‘ k
local notation "κ" => (kpair.π₂ (woodinIterationRec k)) ‘ k
local notation "δ" => woodinPrefixCutoff P R o κ

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
include hΩ hAC hk

theorem woodinSparseSuccessorDisplacement_cardinal_inputs :
    κ ⊆ δ ∧ o ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![checkName o κ]) := by
  let := hΩ.inaccessible.1
  have hkΩ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hsub := IsOrdinal.toIsTransitive.transitive _ hkΩ
  have hδ := (woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk).2.2.1
  let := hδ.1
  refine ⟨?_, ?_⟩
  · apply IsOrdinal.toIsTransitive.transitive
    rw [woodinSparsePrefix_successor_cutoff hΩ hAC hkΩ]
    exact woodinIterationActualCardinal_increasing hΩ hAC hk (mem_succ_self k)
  · rw [← woodinSparseStageCode_eq_prefix hΩ hAC hkΩ]
    have hs := woodinSparseStageCode_stage hΩ hAC hsub
    change IsWoodinStage (woodinIterationStage (woodinSparseStageCode k)
      (kpair.π₂ (woodinIterationRec k)) k) at hs
    simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code] using hs.2.2.2.1 _ hs.2.1.1

theorem woodinSparseSuccessorDisplacement_spec
    (p q : ForcingName P)
    (hp : o ∈ atomicMembership P R p.val (saturatedWoodinPrefixPosetName P R o κ δ))
    (hq : o ∈ atomicMembership P R q.val (saturatedWoodinPrefixPosetName P R o κ δ)) :
    IsSparseTailAction (woodinSourceIndex (succ k))
      ((forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k))
      ((forcingCodeR (woodinSparseStageCode (succ k))) ‘ (succ k))
      (woodinSparseSuccessorDisplacement k p.val q.val) := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk
  obtain ⟨hκδ, hκ⟩ := woodinSparseSuccessorDisplacement_cardinal_inputs hΩ hAC hk
  rw [(woodinSparseStageCode_successor k).1, (woodinSparseStageCode_successor k).2]
  exact sparseCanonicalPrefixDisplacement_spec hR ht hδ hP hκδ hκ p q hp hq hsp

theorem woodinSparseSuccessorDisplacement_conditions {p q : V}
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k))
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k)) :
    IsSparseTailAction (woodinSourceIndex (succ k))
      ((forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k))
      ((forcingCodeR (woodinSparseStageCode (succ k))) ‘ (succ k))
      (woodinSparseSuccessorDisplacement k (p ‘ (woodinSourceIndex (succ k)))
        (q ‘ (woodinSourceIndex (succ k)))) := by
  rw [(woodinSparseStageCode_successor k).1] at hp hq
  have hp' := (mem_woodinSparseSuccessorCarrier_iff.mp hp).2.2
  have hq' := (mem_woodinSparseSuccessorCarrier_iff.mp hq).2.2
  simp only [woodinSparseSuccessorPool, normalizedNamePool, mem_sep_iff] at hp' hq'
  exact woodinSparseSuccessorDisplacement_spec hΩ hAC hk
    ⟨_, hp'.2.1⟩ ⟨_, hq'.2.1⟩ hp'.2.2.2 hq'.2.2.2

end ZFVP

