import ZFVP.ModelTheory.WoodinSparseSuccessorDisplacement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseSuccessorHomogenizingMap (k f p q : V) : V :=
  let e := woodinSparseSuccessorAutomorphism k f;
  let a := woodinSourceIndex (succ k);
  compose e (woodinSparseSuccessorDisplacement k ((e ‘ p) ‘ a) (q ‘ a))

instance woodinSparseSuccessorHomogenizingMap_definable :
    ℒₛₑₜ-function₄[V] woodinSparseSuccessorHomogenizingMap := by
  unfold woodinSparseSuccessorHomogenizingMap
  dsimp only
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₂.comp <;> definability
  · apply Language.DefinableFunction₃.comp
    · definability
    · apply Language.DefinableFunction₂.comp
      · apply Language.DefinableFunction₂.comp
        · apply Language.DefinableFunction₂.comp <;> definability
        · definability
      · definability
    · definability

variable {Ω k f p q : V} [IsOrdinal k]
local notation "c" => woodinSparsePrefixCode (succ k)
local notation "P" => (forcingCodeP c) ‘ k
local notation "R" => (forcingCodeR c) ‘ k
local notation "o" => (forcingCodet c) ‘ k
local notation "C" => (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k)
local notation "T" => (forcingCodeR (woodinSparseStageCode (succ k))) ‘ (succ k)
local notation "a" => woodinSourceIndex (succ k)
local notation "e" => woodinSparseSuccessorAutomorphism k f
local notation "D" => woodinSparseSuccessorDisplacement k ((e ‘ p) ‘ a) (q ‘ a)

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
include hΩ hAC hk

theorem woodinSparseSuccessorHomogenizingMap_action
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    (hp : p ∈ C) (hq : q ∈ C) :
    IsForcingAutomorphism C T e ∧ IsSparseTailAction a C T D := by
  have he := woodinSparseSuccessorAutomorphism_automorphism hΩ hAC hk hf hft
  exact ⟨he, woodinSparseSuccessorDisplacement_conditions hΩ hAC hk (function_value_mem he.1 hp) hq⟩

theorem woodinSparseSuccessorHomogenizingMap_automorphism
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    (hp : p ∈ C) (hq : q ∈ C) :
    IsForcingAutomorphism C T (woodinSparseSuccessorHomogenizingMap k f p q) := by
  obtain ⟨he, hd⟩ := woodinSparseSuccessorHomogenizingMap_action hΩ hAC hk hf hft hp hq
  exact forcingAutomorphism_compose he hd.1

theorem woodinSparseSuccessorHomogenizingMap_restrict
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    (hp : p ∈ C) (hq : q ∈ C) {z : V} (hz : z ∈ C) :
    ((woodinSparseSuccessorHomogenizingMap k f p q) ‘ z) ↾ a = f ‘ (z ↾ a) := by
  obtain ⟨he, hd⟩ := woodinSparseSuccessorHomogenizingMap_action hΩ hAC hk hf hft hp hq
  change (((compose e D) ‘ z) ↾ a = f ‘ (z ↾ a))
  rw [value_compose_of_mem_function he.1 hd.1.1 hz, hd.2.1 _ (function_value_mem he.1 hz)]
  exact woodinSparseSuccessorAutomorphism_restrict hΩ hAC hk hf hft hz

theorem woodinSparseSuccessorHomogenizingMap_domain
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    (hp : p ∈ C) (hq : q ∈ C)
    (hdom : ∀ z ∈ P, domain (f ‘ z) = domain z) {z : V} (hz : z ∈ C) :
    domain ((woodinSparseSuccessorHomogenizingMap k f p q) ‘ z) = domain z := by
  obtain ⟨he, hd⟩ := woodinSparseSuccessorHomogenizingMap_action hΩ hAC hk hf hft hp hq
  change (domain ((compose e D) ‘ z) = domain z)
  rw [value_compose_of_mem_function he.1 hd.1.1 hz, hd.2.2.1 _ (function_value_mem he.1 hz)]
  exact woodinSparseSuccessorAutomorphism_domain hΩ hAC hk hf hft hdom hz

theorem woodinSparseSuccessorHomogenizingMap_top
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    (hp : p ∈ C) (hq : q ∈ C) :
    (woodinSparseSuccessorHomogenizingMap k f p q) ‘ ∅ = ∅ := by
  let := hΩ.inaccessible.1
  have ht := (woodinSparseStageCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hk)).system.tops.top
    (succ k) (mem_succ_self _)
  rw [woodinSparseStageCode_top hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hk)] at ht
  obtain ⟨he, hd⟩ := woodinSparseSuccessorHomogenizingMap_action hΩ hAC hk hf hft hp hq
  change ((compose e D) ‘ ∅ = ∅)
  rw [value_compose_of_mem_function he.1 hd.1.1 ht.1,
    woodinSparseSuccessorAutomorphism_top hΩ hAC hk hf hft]
  exact hd.2.2.2 _ ht.1 (value_eq_empty_of_not_mem_domain (by rw [domain_empty]; exact not_mem_empty))

theorem woodinSparseSuccessorHomogenizingMap_empty_tail
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    (hp : p ∈ C) (hq : q ∈ C) {z : V} (hz : z ∈ C) (hz0 : z ‘ a = ∅) :
    (woodinSparseSuccessorHomogenizingMap k f p q) ‘ z = f ‘ (z ↾ a) := by
  obtain ⟨he, hd⟩ := woodinSparseSuccessorHomogenizingMap_action hΩ hAC hk hf hft hp hq
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk
  have hz' := hz
  rw [(woodinSparseStageCode_successor k).1] at hz'
  have hval : e ‘ z = f ‘ (z ↾ a) :=
    sparsePrefixAutomorphism_empty_tail hf hR ht hft hδ hP hsp hz' hz0
  have hs := hsp _ (function_value_mem hf.1 (mem_sparsePairCarrier_iff.mp hz').2.1)
  let := hs.1
  have hzero : (e ‘ z) ‘ a = ∅ := by
    rw [hval]
    exact value_eq_empty_of_not_mem_domain (fun hh ↦ mem_irrefl a (hs.2.1 a hh))
  change ((compose e D) ‘ z = f ‘ (z ↾ a))
  rw [value_compose_of_mem_function he.1 hd.1.1 hz,
    hd.2.2.2 _ (function_value_mem he.1 hz) hzero]
  exact hval

theorem woodinSparseSuccessorHomogenizingMap_base
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    (hp : p ∈ C) (hq : q ∈ C) {z : V} (hz : z ∈ P) :
    (woodinSparseSuccessorHomogenizingMap k f p q) ‘ z = f ‘ z := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hc := woodinSparsePrefixCode_valid hΩ hAC hsub
  have hs := woodinSparseStageCode_valid hΩ hAC hsub
  have hex := woodinSparseStageCode_extends hΩ hAC hsub
  have hzold : z ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ k := by
    rwa [← hc.tableP.value_of_subset hs.tableP hex.subP (mem_succ_self k)]
  have hznew := hs.system.split.secMaps k (mem_succ_iff.mpr (Or.inr (mem_succ_self k)))
    (succ k) (mem_succ_self _) (mem_subset_refl k) z hzold
  rw [woodinSparseStageCode_section hΩ hAC hsub (mem_succ_self k) hzold] at hznew
  have hsp := (woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk).2.2.2.2 z hz
  let := hsp.1
  have hz0 : z ‘ a = ∅ := value_eq_empty_of_not_mem_domain (fun hh ↦ mem_irrefl a (hsp.2.1 a hh))
  rw [woodinSparseSuccessorHomogenizingMap_empty_tail hΩ hAC hk hf hft hp hq hznew hz0,
    IsFunction.restrict_eq_self z a hsp.2.1]

end ZFVP

