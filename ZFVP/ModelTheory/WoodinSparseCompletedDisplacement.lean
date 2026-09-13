import ZFVP.ModelTheory.WoodinCanonicalTailNameUniform
import ZFVP.ModelTheory.WoodinSparseCompletedAutomorphism
import ZFVP.ModelTheory.WoodinSparseActualInverseRankAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseCompletedDisplacement (θ p q : V) : V :=
  let c := woodinSparsePrefixCode θ;
  sparseCanonicalHartogsDisplacement θ (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∅
    (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) (woodinSparseInverseCutoff θ c) p q

instance woodinSparseCompletedDisplacement_definable :
    ℒₛₑₜ-function₃[V] woodinSparseCompletedDisplacement := by
  unfold woodinSparseCompletedDisplacement
  dsimp only
  apply sparseCanonicalHartogsDisplacement_comp <;> definability

variable {Ω θ : V} [IsOrdinal θ]
local notation "c" => woodinSparsePrefixCode θ
local notation "P" => woodinSparseInverseBase θ c
local notation "R" => woodinSparseInverseOrder θ c
local notation "δ" => woodinSparseInverseCutoff θ c
local notation "γ" => woodinLimitCardinal (woodinIterationCardinalPrefix θ)
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
include hΩ hAC hθ h0 hlim hn

theorem woodinSparseCompletedDisplacement_cardinal_inputs :
    γ ∈ δ ∧ (∅ : V) ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName ∅ γ)]) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  refine ⟨?_, ?_⟩
  · rw [woodinSparsePrefix_inverse_cutoff hΩ hAC hsub h0 hlim hn]
    exact woodinIterationLimitCardinal_lt_actual_of_inverse hΩ hAC hθ hn
  · have hi := woodinSparsePrefix_inverse_rankInputs hΩ hAC hθ h0
      (ordinal_limit_of_not_successor hlim) hn
    exact hi.regular _ hi.top.1

theorem woodinSparseCompletedDisplacement_spec
    (p q : ForcingName P)
    (hp : (∅ : V) ∈ atomicMembership P R p.val (saturatedHartogsPosetName P R ∅ γ δ))
    (hq : (∅ : V) ∈ atomicMembership P R q.val (saturatedHartogsPosetName P R ∅ γ δ)) :
    IsSparseTailAction θ ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ)
      (woodinSparseCompletedDisplacement θ p.val q.val) := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn
  obtain ⟨hγδ, hγ⟩ := woodinSparseCompletedDisplacement_cardinal_inputs hΩ hAC hθ h0 hlim hn
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1, (woodinSparseStageCode_inverse h0 hlim hn).2]
  exact sparseCanonicalHartogsDisplacement_spec hR ht hδ hP hγδ hγ p q hp hq hsp

theorem woodinSparseCompletedDisplacement_conditions {p q : V}
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    IsSparseTailAction θ ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ)
      (woodinSparseCompletedDisplacement θ (p ‘ θ) (q ‘ θ)) := by
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hp hq
  have hp' := (mem_sparsePairCarrier_iff.mp hp).2.2
  have hq' := (mem_sparsePairCarrier_iff.mp hq).2.2
  simp only [woodinSparseInversePool, normalizedNamePool, mem_sep_iff] at hp' hq'
  exact woodinSparseCompletedDisplacement_spec hΩ hAC hθ h0 hlim hn
    ⟨_, hp'.2.1⟩ ⟨_, hq'.2.1⟩ hp'.2.2.2 hq'.2.2.2

end ZFVP
