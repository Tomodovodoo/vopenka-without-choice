import ZFVP.ModelTheory.WoodinSparseSuccessorHomogenizingRow
import ZFVP.ModelTheory.WoodinCanonicalCommonNameUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseSuccessorCommonWitness (k f p q r : V) : V :=
  let c := woodinSparsePrefixCode (succ k);
  let P := (forcingCodeP c) ‘ k;
  let R := (forcingCodeR c) ‘ k;
  let o := (forcingCodet c) ‘ k;
  let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k;
  let δ := woodinPrefixCutoff P R o κ;
  let a := woodinSourceIndex (succ k);
  let x := ((woodinSparseSuccessorAutomorphism k f) ‘ p) ‘ a;
  let y := q ‘ a;
  let N := woodinCollapseDisplacementName P R (checkName o κ) (checkName o δ) x y;
  sparseAppend a r (canonicalTailCommonName P R o N x y)

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinSparseSuccessorCommonWitness_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (woodinSparseSuccessorCommonWitness (V := V)) := by
  unfold woodinSparseSuccessorCommonWitness
  dsimp only
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · apply canonicalTailCommonName_comp
    · definability
    · definability
    · definability
    · apply woodinCollapseDisplacementName_comp <;> definability
    · definability
    · definability

variable {Ω k f p q r : V} [IsOrdinal k]
local notation "c" => woodinSparsePrefixCode (succ k)
local notation "P" => (forcingCodeP c) ‘ k
local notation "R" => (forcingCodeR c) ‘ k
local notation "o" => (forcingCodet c) ‘ k
local notation "κ" => (kpair.π₂ (woodinIterationRec k)) ‘ k
local notation "δ" => woodinPrefixCutoff P R o κ
local notation "C" => (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k)
local notation "T" => (forcingCodeR (woodinSparseStageCode (succ k))) ‘ (succ k)
local notation "a" => woodinSourceIndex (succ k)
local notation "e" => woodinSparseSuccessorAutomorphism k f
local notation "D" => woodinSparseSuccessorDisplacement k ((e ‘ p) ‘ a) (q ‘ a)

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
include hΩ hAC hk

theorem woodinSparseSuccessorCommonWitness_spec
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ o = o)
    (hp : p ∈ C) (hq : q ∈ C) (hr : r ∈ P)
    (hrp : ⟨r,f ‘ (p ↾ a)⟩ₖ ∈ R) (hrq : ⟨r,q ↾ a⟩ₖ ∈ R)
    (hdom : ∀ z ∈ P, domain (f ‘ z) = domain z) :
    let w := woodinSparseSuccessorCommonWitness k f p q r
    w ∈ C ∧ ⟨w,(woodinSparseSuccessorHomogenizingMap k f p q) ‘ p⟩ₖ ∈ T ∧
      ⟨w,q⟩ₖ ∈ T ∧ w ↾ a = r ∧ domain w ⊆ (domain r ∪ domain p) ∪ domain q := by
  obtain ⟨he, hd⟩ := woodinSparseSuccessorHomogenizingMap_action hΩ hAC hk hf hft hp hq
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseSuccessorAutomorphism_inputs hΩ hAC hk
  obtain ⟨hκδ, hκ⟩ := woodinSparseSuccessorDisplacement_cardinal_inputs hΩ hAC hk
  have hxp := function_value_mem he.1 hp
  have hq' := hq
  rw [(woodinSparseStageCode_successor k).1] at hxp hq'
  have hrx : ⟨r,(e ‘ p) ↾ a⟩ₖ ∈ R := by
    rwa [woodinSparseSuccessorAutomorphism_restrict hΩ hAC hk hf hft hp]
  have hb := sparseCanonicalPrefixDisplacement_commonExtension hR ht hδ hP hκδ hκ hxp hq' hr hrx hrq hsp
  have hval : (woodinSparseSuccessorHomogenizingMap k f p q) ‘ p = D ‘ (e ‘ p) :=
    value_compose_of_mem_function he.1 hd.1.1 hp
  have hdomain := woodinSparseSuccessorAutomorphism_domain hΩ hAC hk hf hft hdom hp
  change woodinSparseSuccessorCommonWitness k f p q r ∈ C ∧ _
  rw [(woodinSparseStageCode_successor k).1, (woodinSparseStageCode_successor k).2, hval]
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
  simpa only [woodinSparseSuccessorCommonWitness, hdomain] using hb.2.2.2.2.2

end ZFVP

