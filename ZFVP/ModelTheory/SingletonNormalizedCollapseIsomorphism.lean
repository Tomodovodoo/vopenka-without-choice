import ZFVP.ModelTheory.SingletonNormalizedPoolEvaluation
import ZFVP.ModelTheory.NormalizedReverseOrderComparison

set_option maxHeartbeats 1000000

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem singletonForcing_named_truth (u : V) {n : ℕ} (v : Fin n → V)
    (hv : ∀ i, IsForcingName ({u} : V) (v i)) (φ : SetTheorySemisentence n) :
    u ∈ forcingFormula ({u} : V) (({u} : V) ×ˢ {u}) φ (standardTuple v) ↔
      φ.Evalb (fun i ↦ nameValue {u} (v i)) := by
  let A := singletonForcingContext u
  let L := singletonForcingRealization u
  let e : A.Model ≃ V := Equiv.ofBijective L.value
    ⟨L.value_injective, fun x ↦ ⟨A.check x, L.value_check x⟩⟩
  let c : Fin n → ForcingName A.P := fun i ↦ ⟨v i, hv i⟩
  have he := eval_membershipIso e L.value_mem_iff φ (fun i ↦ A.ofName (c i)) Empty.elim
  have heval : e ∘ (fun i ↦ A.ofName (c i)) = fun i ↦ nameValue {u} (v i) := rfl
  have hempty : e ∘ (Empty.elim : Empty → A.Model) = Empty.elim := by
    funext x
    exact Empty.elim x
  rw [heval, hempty] at he
  have ht := A.formula_truth φ c
  change φ.Evalb (fun i ↦ A.ofName (c i)) ↔
    ∃ p, p = u ∧ p ∈ forcingFormula ({u} : V) (({u} : V) ×ˢ {u}) φ (standardTuple v) at ht
  simpa only [exists_eq_left] using ht.symm.trans he

noncomputable def singletonNormalizedCollapseMap (u κ δ : V) : V :=
  definableGraph (normalizedNameTwoStep {u} (({u} : V) ×ˢ {u}) u δ
    (saturatedWoodinPrefixPosetName {u} (({u} : V) ×ˢ {u}) u κ δ))
    (fun z ↦ nameValue {u} (kpair.π₂ z)) (by definability)

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₅.comp

instance singletonNormalizedCollapseMap_definable :
    ℒₛₑₜ-function₃[V] singletonNormalizedCollapseMap := by
  have hN : ℒₛₑₜ-function₃[V] (fun u κ δ ↦ normalizedNameTwoStep {u} (({u} : V) ×ˢ {u}) u δ
      (saturatedWoodinPrefixPosetName {u} (({u} : V) ×ˢ {u}) u κ δ)) := by
    apply Language.DefinableFunction₅.comp
    · definability
    · definability
    · definability
    · definability
    · apply Language.DefinableFunction₅.comp <;> definability
  have h : ℒₛₑₜ-relation₄[V] (fun f u κ δ ↦ ∀ z, z ∈ f ↔
      ∃ x ∈ normalizedNameTwoStep {u} (({u} : V) ×ˢ {u}) u δ
        (saturatedWoodinPrefixPosetName {u} (({u} : V) ×ˢ {u}) u κ δ),
      z = ⟨x, nameValue {u} (kpair.π₂ x)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [singletonNormalizedCollapseMap, mem_definableGraph_iff]
  rfl
variable {u κ δ : V}

variable (hδ : IsChoicelessInaccessible δ) (hP : (Singleton.singleton u : V) ∈ hierarchy δ) (hκ : κ ⊆ δ)
include hδ hP hκ

theorem singletonNormalizedCollapseMap_function :
    singletonNormalizedCollapseMap u κ δ ∈ (woodinCollapse κ δ) ^ (normalizedNameTwoStep (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u δ (saturatedWoodinPrefixPosetName (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u κ δ)) := by
  apply definableGraph_mem_function_of_mapsTo
  intro z hz
  obtain ⟨p, _, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  rw [kpair.π₂_kpair, ← singleton_normalizedWoodinPrefixPool_image hδ hP hκ]
  exact (repl_spec _).mpr ⟨τ, hτ, rfl⟩

omit hδ hP hκ in
 theorem singletonNormalizedCollapseMap_value {z : V} (hz : z ∈ (normalizedNameTwoStep (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u δ (saturatedWoodinPrefixPosetName (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u κ δ))) :
    (singletonNormalizedCollapseMap u κ δ) ‘ z = nameValue {u} (kpair.π₂ z) :=
  value_definableGraph _ _ _ hz

theorem singletonNormalizedCollapseMap_isomorphism :
    IsForcingIsomorphism (normalizedNameTwoStep (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u δ (saturatedWoodinPrefixPosetName (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u κ δ)) (nameTwoStepOrderOn (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) (saturatedWoodinPrefixOrderName (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u κ δ) (normalizedNameTwoStep (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u δ (saturatedWoodinPrefixPosetName (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u κ δ))) (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      (singletonNormalizedCollapseMap u κ δ) := by
  have hf := singletonNormalizedCollapseMap_function hδ hP hκ
  let := IsFunction.of_mem hf
  have hR := singletonForcing_preorder u
  have hu : u ∈ (Singleton.singleton u : V) := mem_singleton_iff.mpr rfl
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro a b z ha hb
    have haN := (mem_of_mem_functions hf ha).1
    have hbN := (mem_of_mem_functions hf hb).1
    have he := (value_eq_of_kpair_mem ha).trans (value_eq_of_kpair_mem hb).symm
    rw [singletonNormalizedCollapseMap_value haN, singletonNormalizedCollapseMap_value hbN] at he
    obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp haN
    obtain ⟨q, hq, σ, hσ, rfl⟩ := mem_prod_iff.mp hbN
    have hp' := mem_singleton_iff.mp hp
    have hq' := mem_singleton_iff.mp hq
    subst p q
    simp only [kpair.π₂_kpair] at he
    have hτ' := mem_sep_iff.mp hτ
    have hσ' := mem_sep_iff.mp hσ
    have heq := forcingLeastRankName_congr hR hu hτ'.2.1 hσ'.2.1
      ((singleton_nameValue_eq_iff u τ σ).mp he)
    rw [hτ'.2.2.1, hσ'.2.2.1] at heq
    exact congrArg (kpair u) heq
  · apply subset_antisymm (range_subset_of_mem_function hf)
    intro x hx
    rw [← singleton_normalizedWoodinPrefixPool_image hδ hP hκ] at hx
    obtain ⟨τ, hτ, rfl⟩ := (repl_spec _).mp hx
    have hz : ⟨u, τ⟩ₖ ∈ (normalizedNameTwoStep (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u δ (saturatedWoodinPrefixPosetName (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u κ δ)) := kpair_mem_iff.mpr ⟨hu, hτ⟩
    have hv := value_mem_range hf hz
    rwa [singletonNormalizedCollapseMap_value hz, kpair.π₂_kpair] at hv
  · intro a ha b hb
    have haQ := function_value_mem hf ha
    have hbQ := function_value_mem hf hb
    rw [singletonNormalizedCollapseMap_value ha] at haQ
    rw [singletonNormalizedCollapseMap_value hb] at hbQ
    rw [singletonNormalizedCollapseMap_value ha, singletonNormalizedCollapseMap_value hb]
    obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp ha
    obtain ⟨q, hq, σ, hσ, rfl⟩ := mem_prod_iff.mp hb
    have hp' := mem_singleton_iff.mp hp
    have hq' := mem_singleton_iff.mp hq
    subst p q
    simp only [kpair.π₂_kpair] at haQ hbQ ⊢
    rw [saturatedWoodinPrefixOrderName, normalizedNameTwoStep_reverse_order_comparison hR (singletonForcing_top u)
      (saturatedWoodinPrefixPosetName_isName (Singleton.singleton u : V) ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) u κ δ) hu hu hτ hσ,
      woodinCollapseOrder, pair_mem_reverseInclusionOrder]
    have hbase : ⟨u, u⟩ₖ ∈ ((Singleton.singleton u : V) ×ˢ (Singleton.singleton u : V)) := kpair_mem_iff.mpr ⟨hu, hu⟩
    simp only [hbase, haQ, hbQ, true_and]
    have htruth := singletonForcing_named_truth u ![σ, τ]
      (by intro i; fin_cases i
          · exact (mem_sep_iff.mp hσ).2.1
          · exact (mem_sep_iff.mp hτ).2.1) isSubsetOf
    simpa using htruth

end ZFVP






