import ZFVP.ModelTheory.WoodinSparseSuccessor
import ZFVP.ModelTheory.NormalizedCanonicalTwoStep
import ZFVP.SetTheory.ForcingAutomorphisms

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparsePrefixAutomorphism (a P R top κ δ f : V) : V :=
  let U := saturatedWoodinPrefixPosetName P R top κ δ
  let W := normalizedNamePool P R top δ U
  compose (sparsePairDecode a P W)
    (compose (normalizedTwoStepIsoMap P R top δ U P R top f) (sparsePairEncode a P W))

theorem sparsePrefixAutomorphism_comp_definable {n : ℕ}
    {a P R top κ δ f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hP : Language.DefinableFunction ℒₛₑₜ P)
    (hR : Language.DefinableFunction ℒₛₑₜ R) (ht : Language.DefinableFunction ℒₛₑₜ top)
    (hκ : Language.DefinableFunction ℒₛₑₜ κ) (hδ : Language.DefinableFunction ℒₛₑₜ δ)
    (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦
      sparsePrefixAutomorphism (a v) (P v) (R v) (top v) (κ v) (δ v) (f v)) := by
  have hU : Language.DefinableFunction ℒₛₑₜ (fun v ↦
      saturatedWoodinPrefixPosetName (P v) (R v) (top v) (κ v) (δ v)) := by
    apply Language.DefinableFunction₅.comp <;> assumption
  have hW : Language.DefinableFunction ℒₛₑₜ (fun v ↦
      normalizedNamePool (P v) (R v) (top v) (δ v)
        (saturatedWoodinPrefixPosetName (P v) (R v) (top v) (κ v) (δ v))) := by
    apply Language.DefinableFunction₅.comp <;> assumption
  unfold sparsePrefixAutomorphism
  dsimp only
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₃.comp <;> assumption
  · apply Language.DefinableFunction₂.comp
    · exact normalizedTwoStepIsoMap_comp hP hR ht hδ hU hP hR ht hf
    · apply Language.DefinableFunction₃.comp <;> assumption

variable {a P R top κ δ f : V}
local notation "U" => saturatedWoodinPrefixPosetName P R top κ δ
local notation "S" => saturatedWoodinPrefixOrderName P R top κ δ
local notation "W" => normalizedNamePool P R top δ U
local notation "C" => sparseNormalizedTwoStep a P R top δ U
local notation "T" => sparseNormalizedTwoStepOrder a P R top δ U S

variable (hf : IsForcingAutomorphism P R f) (hR : IsForcingPreorder P R)
  (ht : IsForcingTop P R top) (hft : f ‘ top = top)
  (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
  (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)

include hf hR ht hft hδ hP hsp

theorem sparsePrefixAutomorphism_automorphism :
    IsForcingAutomorphism C T (sparsePrefixAutomorphism a P R top κ δ f) := by
  have hi := normalizedSaturatedPrefix_isomorphism hf hR hR ht ht hft hδ hP hP κ
  have hd := sparsePairDecode_isomorphism («W» := W) (R := nameTwoStepOrderOn P R S
    (normalizedNameTwoStep P R top δ U)) hsp
  have he := sparsePairEncode_isomorphism («W» := W) (R := nameTwoStepOrderOn P R S
    (normalizedNameTwoStep P R top δ U)) hsp
  exact hd.comp (hi.comp he)

theorem sparsePrefixAutomorphism_value {q : V} (hq : q ∈ C) :
    (sparsePrefixAutomorphism a P R top κ δ f) ‘ q =
      sparseAppend a (f ‘ (q ↾ a)) (normalizedIsomorphismName P R top f (q ‘ a)) := by
  have hi := normalizedSaturatedPrefix_isomorphism hf hR hR ht ht hft hδ hP hP κ
  have hd := sparsePairDecode_isomorphism («W» := W) (R := nameTwoStepOrderOn P R S
    (normalizedNameTwoStep P R top δ U)) hsp
  have he := sparsePairEncode_isomorphism («W» := W) (R := nameTwoStepOrderOn P R S
    (normalizedNameTwoStep P R top δ U)) hsp
  unfold sparsePrefixAutomorphism
  dsimp only
  rw [value_compose_of_mem_function hd.1 (compose_function hi.1 he.1) hq,
    value_compose_of_mem_function hi.1 he.1 (function_value_mem hd.1 hq),
    sparsePairEncode_value_of_mem hsp (function_value_mem hi.1 (function_value_mem hd.1 hq)),
    normalizedTwoStepIsoMap_value (function_value_mem hd.1 hq), sparsePairDecode_value hq]
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair]

theorem sparsePrefixAutomorphism_restrict {q : V} (hq : q ∈ C) :
    ((sparsePrefixAutomorphism a P R top κ δ f) ‘ q) ↾ a = f ‘ (q ↾ a) := by
  have hs := hsp _ (function_value_mem hf.1 (mem_sparsePairCarrier_iff.mp hq).2.1)
  let := hs.1
  rw [sparsePrefixAutomorphism_value hf hR ht hft hδ hP hsp hq]
  exact sparseAppend_restrict hs.2.1

theorem sparsePrefixAutomorphism_empty_tail {q : V} (hq : q ∈ C) (hqa : q ‘ a = ∅) :
    (sparsePrefixAutomorphism a P R top κ δ f) ‘ q = f ‘ (q ↾ a) := by
  rw [sparsePrefixAutomorphism_value hf hR ht hft hδ hP hsp hq, hqa,
    normalizedIsomorphismName_empty hR ht.1, sparseAppend_empty]

theorem sparsePrefixAutomorphism_restrict_earlier {q b g : V} (hq : q ∈ C)
    (hb : b ⊆ a) (hcomm : ∀ p ∈ P, (f ‘ p) ↾ b = g ‘ (p ↾ b)) :
    ((sparsePrefixAutomorphism a P R top κ δ f) ‘ q) ↾ b = g ‘ (q ↾ b) := by
  rw [← restrict_restrict_of_subset hb,
    sparsePrefixAutomorphism_restrict hf hR ht hft hδ hP hsp hq,
    hcomm _ (mem_sparsePairCarrier_iff.mp hq).2.1, restrict_restrict_of_subset hb]

theorem sparsePrefixAutomorphism_inverse_value {q : V} (hq : q ∈ C) :
    (sparsePrefixAutomorphism a P R top κ δ (converseGraph f)) ‘
      ((sparsePrefixAutomorphism a P R top κ δ f) ‘ q) = q := by
  have ha := sparsePrefixAutomorphism_automorphism (κ := κ) hf hR ht hft hδ hP hsp
  have hf' := forcingAutomorphism_inverse hf
  have hft' : (converseGraph f) ‘ top = top := by
    simpa only [hft] using converseGraph_value_value hf.1 hf.2.1 ht.1
  have hm := function_value_mem ha.1 hq
  have hq' := mem_sparsePairCarrier_iff.mp hq
  have hs := hsp _ (function_value_mem hf.1 hq'.2.1)
  let := hs.1
  rw [sparsePrefixAutomorphism_value hf' hR ht hft' hδ hP hsp hm,
    sparsePrefixAutomorphism_restrict hf hR ht hft hδ hP hsp hq,
    converseGraph_value_value hf.1 hf.2.1 hq'.2.1,
    sparsePrefixAutomorphism_value hf hR ht hft hδ hP hsp hq,
    sparseAppend_value_new hs.2.1]
  have hτ := mem_sep_iff.mp hq'.2.2
  rw [normalizedIsomorphismName_inverse hf hR hR ht.1 ht.1 hft hτ.2.1 hτ.2.2.1]
  exact sparseAppend_reconstruct hq'.1

theorem sparsePrefixAutomorphism_domain {q : V} (hq : q ∈ C)
    (hdom : ∀ p ∈ P, domain (f ‘ p) = domain p) :
    domain ((sparsePrefixAutomorphism a P R top κ δ f) ‘ q) = domain q := by
  have hq' := mem_sparsePairCarrier_iff.mp hq
  have hτ := mem_sep_iff.mp hq'.2.2
  have hz : normalizedIsomorphismName P R top f (q ‘ a) = ∅ ↔ q ‘ a = ∅ := by
    constructor
    · intro he
      have hi := normalizedIsomorphismName_inverse hf hR hR ht.1 ht.1 hft hτ.2.1 hτ.2.2.1
      rw [he, normalizedIsomorphismName_empty hR ht.1] at hi
      exact hi.symm
    · intro he
      rw [he, normalizedIsomorphismName_empty hR ht.1]
  rw [sparsePrefixAutomorphism_value hf hR ht hft hδ hP hsp hq, sparseAppend_domain,
    hdom _ hq'.2.1]
  by_cases he : q ‘ a = ∅
  · rw [ite_eq_left (hz.mpr he)]
    simpa only [sparseAppend_domain, he, ↓reduceIte] using
      congrArg domain (sparseAppend_reconstruct hq'.1)
  · have hn : normalizedIsomorphismName P R top f (q ‘ a) ≠ ∅ := fun hh ↦ he (hz.mp hh)
    rw [ite_eq_right hn]
    simpa only [sparseAppend_domain, he, ↓reduceIte] using
      congrArg domain (sparseAppend_reconstruct hq'.1)

end ZFVP


