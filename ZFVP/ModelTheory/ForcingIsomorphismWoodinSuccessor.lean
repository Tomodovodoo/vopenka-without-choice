import ZFVP.ModelTheory.ForcingIsomorphismCanonicalTwoStep
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
theorem IsForcingIsomorphism.prefix_cutoff_iff {P R Q S f one top : V}
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (κ δ : V) :
    IsWoodinPrefixCutoff P R one κ δ ↔ IsWoodinPrefixCutoff Q S top κ δ := by
  apply hf.named_prefix_cutoff_iff hR hS ht ht' hft
    ⟨checkName one κ, checkName_isName ht.1 _⟩ ⟨checkName top κ, checkName_isName ht'.1 _⟩
  intro p hp
  change f ‘ p ∈ atomicEquality Q S (nameAction f (checkName one κ)) (checkName top κ)
  rw [nameAction_checkName_map ht.1, hft, atomicEquality_refl hS]
  exact function_value_mem hf.1 hp

theorem IsForcingIsomorphism.prefix_cutoff {P R Q S f one top : V}
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (κ : V) :
    woodinPrefixCutoff P R one κ = woodinPrefixCutoff Q S top κ := by
  have he : IsWoodinPrefixCutoff P R one = IsWoodinPrefixCutoff Q S top := by
    funext a b
    exact propext (hf.prefix_cutoff_iff hR hS ht ht' hft a b)
  unfold woodinPrefixCutoff
  congr 1

theorem IsForcingIsomorphism.saturated_prefix_name {P R Q S f one top δ : V}
    [IsOrdinal δ] (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (κ : V) :
    nameAction f (saturatedWoodinPrefixPosetName P R one κ δ) =
      saturatedWoodinPrefixPosetName Q S top κ δ := by
  unfold saturatedWoodinPrefixPosetName woodinPrefixPosetName
  rw [hf.saturated_name (woodinCollapseName_isName _ _ _ _)]
  apply forcingSaturatedName_eq_of_forced_equality hS
  intro q hq
  have hp := function_value_mem hf.inverse_maps hq
  have hc (a : V) : f ‘ ((converseGraph f) ‘ q) ∈ atomicEquality Q S
      (nameAction f (checkName one a)) (checkName top a) := by
    rw [nameAction_checkName_map ht.1, hft, atomicEquality_refl hS, hf.value_inverse hq]
    exact hq
  have he := hf.collapse_name_equality hR hS ht ht' hp
    ⟨_, checkName_isName ht.1 κ⟩ ⟨_, checkName_isName ht.1 δ⟩
    ⟨_, checkName_isName ht'.1 κ⟩ ⟨_, checkName_isName ht'.1 δ⟩ (hc κ) (hc δ)
  simpa only [hf.value_inverse hq] using he


theorem saturatedPrefixCollapse_isomorphism {P R Q S f one top δ : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (hf : IsForcingIsomorphism P R Q S f)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (κ : V) :
    let N := saturatedWoodinPrefixPosetName P R one κ δ
    let N' := saturatedWoodinPrefixPosetName Q S top κ δ
    IsForcingIsomorphism (twoStepConditions P R N ∅)
      (twoStepOrder P R N (saturatedWoodinPrefixOrderName P R one κ δ) ∅)
      (twoStepConditions Q S N' ∅)
      (twoStepOrder Q S N' (saturatedWoodinPrefixOrderName Q S top κ δ) ∅)
      (twoStepIsomorphismMap P R N ∅ f) := by
  dsimp only
  have hh := twoStep_reverse_order_isomorphism hR hS hf ht ht'
    (saturatedWoodinPrefixPosetName_isName P R one κ δ)
  rw [hf.saturated_prefix_name hR hS ht ht' hft κ] at hh
  exact hh


theorem woodinSuccessorStep_isomorphism {x y f : V}
    (hR : IsForcingPreorder (woodinStagePoset x) (woodinStageOrder x))
    (hS : IsForcingPreorder (woodinStagePoset y) (woodinStageOrder y))
    (hf : IsForcingIsomorphism (woodinStagePoset x) (woodinStageOrder x)
      (woodinStagePoset y) (woodinStageOrder y) f)
    (ht : IsForcingTop (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x))
    (ht' : IsForcingTop (woodinStagePoset y) (woodinStageOrder y) (woodinStageTop y))
    (hft : f ‘ (woodinStageTop x) = woodinStageTop y)
    (hκ : woodinStageCardinal x = woodinStageCardinal y) :
    let c := woodinPrefixCutoff (woodinStagePoset x) (woodinStageOrder x)
      (woodinStageTop x) (woodinStageCardinal x)
    IsForcingIsomorphism (woodinStagePoset (woodinSuccessorStep x))
      (woodinStageOrder (woodinSuccessorStep x))
      (woodinStagePoset (woodinSuccessorStep y)) (woodinStageOrder (woodinSuccessorStep y))
      (twoStepIsomorphismMap (woodinStagePoset x) (woodinStageOrder x)
        (saturatedWoodinPrefixPosetName (woodinStagePoset x) (woodinStageOrder x)
          (woodinStageTop x) (woodinStageCardinal x) c) ∅ f) := by
  dsimp only
  have hc := hf.prefix_cutoff hR hS ht ht' hft (woodinStageCardinal x)
  rw [hκ] at hc
  let : IsOrdinal (woodinPrefixCutoff (woodinStagePoset x) (woodinStageOrder x)
      (woodinStageTop x) (woodinStageCardinal y)) := by
    unfold woodinPrefixCutoff
    exact leastOrdinalOrZero_ordinal _ _ _
  simp only [woodinSuccessorStep, woodinSuccessorAt, woodinStagePoset_code,
    woodinStageOrder_code, hκ, ← hc]
  exact saturatedPrefixCollapse_isomorphism hR hS hf ht ht' hft _
end ZFVP

