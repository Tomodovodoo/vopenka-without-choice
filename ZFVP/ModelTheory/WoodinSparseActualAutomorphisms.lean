import ZFVP.ModelTheory.WoodinSparseAutomorphismSuccessor
import ZFVP.ModelTheory.WoodinSparseOwnCutoffs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseSuccessorAutomorphism (k f : V) : V :=
  let c := woodinSparsePrefixCode (succ k);
  let P := (forcingCodeP c) ‘ k;
  let R := (forcingCodeR c) ‘ k;
  let top := (forcingCodet c) ‘ k;
  let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k;
  sparsePrefixAutomorphism (woodinSourceIndex (succ k)) P R top κ
    (woodinPrefixCutoff P R top κ) f

instance woodinSparseSuccessorAutomorphism_definable :
    ℒₛₑₜ-function₂[V] woodinSparseSuccessorAutomorphism := by
  unfold woodinSparseSuccessorAutomorphism
  dsimp only
  apply sparsePrefixAutomorphism_comp_definable
  · definability
  · definability
  · definability
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability
  · definability

variable {Ω k f : V} [IsOrdinal k]
local notation "c" => woodinSparsePrefixCode (succ k)
local notation "P" => (forcingCodeP c) ‘ k
local notation "R" => (forcingCodeR c) ‘ k
local notation "o" => (forcingCodet c) ‘ k
local notation "κ" => (kpair.π₂ (woodinIterationRec k)) ‘ k
local notation "δ" => woodinPrefixCutoff P R o κ

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
include hΩ hAC hk

theorem woodinSparseSuccessorAutomorphism_inputs :
    IsForcingPreorder P R ∧ IsForcingTop P R o ∧
    IsChoicelessInaccessible δ ∧ P ∈ hierarchy δ ∧
    ∀ p ∈ P, IsSparseFunctionOn (woodinSourceIndex (succ k)) p := by
  let := hΩ.inaccessible.1
  have hkΩ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hc := woodinSparsePrefixCode_valid hΩ hAC hsub
  have he := woodinSparsePrefix_successor_cutoff hΩ hAC hkΩ
  have hδ : IsChoicelessInaccessible δ := by
    rw [he]
    exact ((woodinIterationExit hΩ hAC).2.1 (succ k) hk).1.inaccessible _ (mem_succ_self _)
  have hP : P ∈ hierarchy δ := by
    rw [he, ← woodinSparseStageCode_eq_prefix hΩ hAC hkΩ]
    exact woodinSparseStageCode_small hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hkΩ)
      (((woodinIterationExit hΩ hAC).2.1 (succ k) hk).1.inaccessible _ (mem_succ_self _))
      (woodinIterationActualCardinal_increasing hΩ hAC hk (mem_succ_self k))
  refine ⟨hc.system.order.preorder _ (mem_succ_self k),
    hc.system.tops.top _ (mem_succ_self k), hδ, hP, ?_⟩
  intro p hp
  rw [← woodinSparseStageCode_eq_prefix hΩ hAC hkΩ] at hp
  rw [woodinSourceIndex_successor]
  exact woodinSparseStageCode_sparse hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hkΩ) hp

theorem woodinSparseSuccessorAutomorphism_automorphism
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o) :
    IsForcingAutomorphism
      ((forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k))
      ((forcingCodeR (woodinSparseStageCode (succ k))) ‘ (succ k))
      (woodinSparseSuccessorAutomorphism k f) := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk
  rw [(woodinSparseStageCode_successor k).1, (woodinSparseStageCode_successor k).2]
  exact sparsePrefixAutomorphism_automorphism hf hR ht hft hδ hP hsp

theorem woodinSparseSuccessorAutomorphism_restrict
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    {q : V} (hq : q ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k)) :
    ((woodinSparseSuccessorAutomorphism k f) ‘ q) ↾ (woodinSourceIndex (succ k)) =
      f ‘ (q ↾ (woodinSourceIndex (succ k))) := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk
  rw [(woodinSparseStageCode_successor k).1] at hq
  exact sparsePrefixAutomorphism_restrict hf hR ht hft hδ hP hsp hq

theorem woodinSparseSuccessorAutomorphism_inverse_value
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    {q : V} (hq : q ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k)) :
    (woodinSparseSuccessorAutomorphism k (converseGraph f)) ‘
      ((woodinSparseSuccessorAutomorphism k f) ‘ q) = q := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk
  rw [(woodinSparseStageCode_successor k).1] at hq
  exact sparsePrefixAutomorphism_inverse_value hf hR ht hft hδ hP hsp hq

theorem woodinSparseSuccessorAutomorphism_base
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o) {p : V} (hp : p ∈ P) :
    (woodinSparseSuccessorAutomorphism k f) ‘ p = f ‘ p := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hc := woodinSparsePrefixCode_valid hΩ hAC hsub
  have hs := woodinSparseStageCode_valid hΩ hAC hsub
  have he := woodinSparseStageCode_extends hΩ hAC hsub
  have hpold : p ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ k := by
    rwa [← hc.tableP.value_of_subset hs.tableP he.subP (mem_succ_self k)]
  have hpnew := hs.system.split.secMaps k (mem_succ_iff.mpr (Or.inr (mem_succ_self k)))
    (succ k) (mem_succ_self _) (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)) p hpold
  rw [woodinSparseStageCode_section hΩ hAC hsub (mem_succ_self k) hpold] at hpnew
  rw [(woodinSparseStageCode_successor k).1] at hpnew
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk
  have hps := hsp p hp
  let := hps.1
  have hz : p ‘ (woodinSourceIndex (succ k)) = ∅ :=
    value_eq_empty_of_not_mem_domain (fun hh ↦ mem_irrefl _ (hps.2.1 _ hh))
  change ((sparsePrefixAutomorphism (woodinSourceIndex (succ k)) P R o κ δ f) ‘ p = f ‘ p)
  rw [sparsePrefixAutomorphism_empty_tail hf hR ht hft hδ hP hsp hpnew hz,
    IsFunction.restrict_eq_self p _ hps.2.1]

theorem woodinSparseSuccessorAutomorphism_domain
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    (hdom : ∀ p ∈ P, domain (f ‘ p) = domain p)
    {q : V} (hq : q ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k)) :
    domain ((woodinSparseSuccessorAutomorphism k f) ‘ q) = domain q := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk
  rw [(woodinSparseStageCode_successor k).1] at hq
  exact sparsePrefixAutomorphism_domain hf hR ht hft hδ hP hsp hq hdom

theorem woodinSparseSuccessorAutomorphism_top
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o) :
    (woodinSparseSuccessorAutomorphism k f) ‘ ∅ = ∅ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have ht := (woodinSparsePrefixCode_valid hΩ hAC hsub).system.tops.top k (mem_succ_self k)
  have he : o = ∅ := woodinSparsePrefixCode_top hΩ hAC hsub (mem_succ_self k)
  have h := woodinSparseSuccessorAutomorphism_base hΩ hAC hk hf hft ht.1
  rw [hft, he] at h
  exact h

end ZFVP
