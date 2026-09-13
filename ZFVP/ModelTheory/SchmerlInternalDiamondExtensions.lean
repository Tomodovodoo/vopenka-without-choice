import ZFVP.ModelTheory.SchmerlInternalDiamondForcing

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem diamondCondition_of_function {κ p : V} [IsOrdinal κ] [IsFunction p]
    (hd : domain p ∈ κ) (hv : ∀ i ∈ domain p, (p ‘ i) ⊆ i) :
    p ∈ diamondConditions κ := by
  apply (mem_diamondConditions κ p).mpr
  refine ⟨hd, mem_function.intro ?_ ?_, hv⟩
  · intro z hz
    obtain ⟨i, x, rfl⟩ := IsFunction.mem_eq_kpair hz
    have hi := mem_domain_of_kpair_mem hz
    refine kpair_mem_iff.mpr ⟨hi, mem_power_iff.mpr ?_⟩
    have hix := hv i hi
    rw [value_eq_of_kpair_mem hz] at hix
    exact subset_trans hix (IsOrdinal.toIsTransitive.transitive i
      (IsOrdinal.toIsTransitive.mem_trans hi hd))
  · intro i hi
    exact ⟨p ‘ i, kpair_value_mem hi, fun x hx ↦ (value_eq_of_kpair_mem hx).symm⟩

theorem diamond_succ_mem {κ α : V} (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hα : α ∈ κ) : succ α ∈ κ := by
  let : IsOrdinal κ := hκ.1.1
  let : IsOrdinal α := IsOrdinal.of_mem hα
  obtain ⟨β, hβ, hb⟩ := regular_small_subset_bounded hκ
    (show ({α} : V) ⊆ κ from fun x hx ↦ (mem_singleton_iff.mp hx) ▸ hα)
    hω (internallyCountable_singleton α)
  let : IsOrdinal β := IsOrdinal.of_mem hβ
  have hαβ := hb α (mem_singleton_iff.mpr rfl)
  exact ordinal_mem_of_subset_mem (show succ α ⊆ β from fun x hx ↦ by
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact hαβ
    · exact IsOrdinal.toIsTransitive.mem_trans hx hαβ) hβ

noncomputable def diamondExtendValue (p i : V) : V := by
  classical
  exact if i ∈ domain p then p ‘ i else ∅

instance diamondExtendValue_definable (p : V) : ℒₛₑₜ-function₁[V] (diamondExtendValue p) := by
  have h : ℒₛₑₜ-relation[V] (fun x i ↦
    (i ∈ domain p ∧ x = p ‘ i) ∨ (i ∉ domain p ∧ x = ∅)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = diamondExtendValue p (v 1) ↔ _
  unfold diamondExtendValue
  split <;> simp_all

noncomputable def diamondExtend (p α : V) : V :=
  definableGraph α (diamondExtendValue p) (diamondExtendValue_definable p)

@[simp] theorem domain_diamondExtend (p α : V) : domain (diamondExtend p α) = α :=
  domain_definableGraph _ _ _

theorem diamondExtend_condition {κ p α : V} [IsOrdinal κ]
    (hp : p ∈ diamondConditions κ) (hα : α ∈ κ) : diamondExtend p α ∈ diamondConditions κ := by
  let : IsFunction (diamondExtend p α) := definableGraph_isFunction _ _ _
  apply diamondCondition_of_function (by simpa using hα)
  intro i hi
  rw [domain_diamondExtend] at hi
  rw [show (diamondExtend p α) ‘ i = diamondExtendValue p i from value_definableGraph _ _ _ hi]
  unfold diamondExtendValue
  split_ifs with hip
  · exact ((mem_diamondConditions κ p).mp hp).2.2 i hip
  · exact empty_subset _

theorem subset_diamondExtend {κ p α : V} (hp : p ∈ diamondConditions κ)
    (hdom : domain p ⊆ α) : p ⊆ diamondExtend p α := by
  let : IsFunction p := diamondCondition_function hp
  intro z hz
  obtain ⟨i, x, rfl⟩ := IsFunction.mem_eq_kpair hz
  have hi := mem_domain_of_kpair_mem hz
  apply (pair_mem_definableGraph_iff _ _ _ _ _).mpr
  refine ⟨hdom i hi, ?_⟩
  simpa only [diamondExtendValue, ite_eq_left hi] using (value_eq_of_kpair_mem hz).symm

theorem diamond_domain_dense {κ α : V} (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hα : α ∈ κ) : ForcingDense (diamondConditions κ) (diamondOrder κ)
      {p ∈ diamondConditions κ ; α ∈ domain p} := by
  let : IsOrdinal κ := hκ.1.1
  refine ⟨sep_subset, fun p hp ↦ ?_⟩
  have hdp := ((mem_diamondConditions κ p).mp hp).1
  obtain ⟨β, hβ, hb⟩ := regular_small_subset_bounded hκ
    (show ({domain p, α} : V) ⊆ κ from fun x hx ↦ by
      rcases (show x = domain p ∨ x = α from by simpa using hx) with rfl | rfl
      · exact hdp
      · exact hα)
    hω (internallyCountable_insert (internallyCountable_singleton α) (domain p))
  have hdomβ := hb (domain p) (by simp)
  have hαβ := hb α (by simp)
  let : IsOrdinal β := IsOrdinal.of_mem hβ
  have hq := diamondExtend_condition hp hβ
  exact ⟨diamondExtend p β, mem_sep_iff.mpr ⟨hq, by simpa using hαβ⟩,
    (pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨hq, hp, subset_diamondExtend hp (IsOrdinal.toIsTransitive.transitive _ hdomβ)⟩⟩

/-- Append any chosen subset of the current length as the next guess. -/
theorem diamond_append_condition {κ p B : V} (hκ : IsRegularCardinal κ)
    (hω : (ω : V) ∈ κ) (hp : p ∈ diamondConditions κ) (hB : B ⊆ domain p) :
    insert ⟨domain p, B⟩ₖ p ∈ diamondConditions κ := by
  let : IsOrdinal κ := hκ.1.1
  let : IsFunction p := diamondCondition_function hp
  have hfresh : domain p ∉ domain p := mem_irrefl _
  let : IsFunction (insert ⟨domain p, B⟩ₖ p) := IsFunction.insert p _ _ hfresh
  have hdom : domain (insert ⟨domain p, B⟩ₖ p) = succ (domain p) := by simp [succ]
  apply diamondCondition_of_function (hdom.symm ▸ diamond_succ_mem hκ hω
    ((mem_diamondConditions κ p).mp hp).1)
  intro i hi
  have hi' : i ∈ succ (domain p) := hdom ▸ hi
  rcases mem_succ_iff.mp hi' with rfl | hi'
  · have hv : (insert ⟨domain p, B⟩ₖ p) ‘ (domain p) = B :=
      value_eq_of_kpair_mem (by simp)
    rw [hv]
    exact hB
  · have hv : (insert ⟨domain p, B⟩ₖ p) ‘ i = p ‘ i :=
      value_eq_of_kpair_mem (mem_insert.mpr (Or.inr (kpair_value_mem hi')))
    rw [hv]
    exact ((mem_diamondConditions κ p).mp hp).2.2 i hi'

end ZFVP.Schmerl
