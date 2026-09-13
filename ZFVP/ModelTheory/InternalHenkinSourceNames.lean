import ZFVP.SetTheory.CountableUnions
import ZFVP.SetTheory.FunctionUnion

/-! Fixed source names with arbitrarily large unused indices, and actual
assignment extensions respecting those names. All constructions take place
inside the supplied ZF model. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local instance] Classical.propDecidable
attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

theorem naturalPairCode_first_subset {x y : V} (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) :
    x ⊆ naturalPairCode x y := by
  let : IsOrdinal (triangular (ordinalAdd x y)) := IsOrdinal.of_mem (triangular_natural (ordinalAdd_natural hx hy))
  unfold naturalPairCode
  rw [ordinalAdd_comm_natural (triangular_natural (ordinalAdd_natural hx hy)) hx]
  exact subset_ordinalAdd _ _

def IsSparseInternalNaming (D j : V) : Prop :=
  j ∈ (ω : V) ^ D ∧ Injective j ∧
    ∀ n ∈ (ω : V), ∃ k ∈ (ω : V), n ⊆ k ∧ k ∉ range j

instance isSparseInternalNaming_definable : ℒₛₑₜ-relation[V] IsSparseInternalNaming := by
  unfold IsSparseInternalNaming
  definability

theorem exists_sparseInternalNaming {D : V} (hD : IsInternallyCountable D) :
    ∃ j : V, IsSparseInternalNaming D j := by
  obtain ⟨f, hf, hfi⟩ := hD
  let j := definableGraph D (fun x ↦ naturalPairCode (f ‘ x) (∅ : V)) (by definability)
  have hj : j ∈ (ω : V) ^ D :=
    definableGraph_mem_function_of_mapsTo _ _ _ _
      (fun x hx ↦ naturalPairCode_natural (function_value_mem hf hx) empty_mem_ω)
  have hjv {x : V} (hx : x ∈ D) : j ‘ x = naturalPairCode (f ‘ x) (∅ : V) :=
    value_definableGraph _ _ _ hx
  let : IsFunction j := IsFunction.of_mem hj
  refine ⟨j, hj, ?_, ?_⟩
  · intro x y z hx hy
    have hxD : x ∈ D := (mem_of_mem_functions hj hx).1
    have hyD : y ∈ D := (mem_of_mem_functions hj hy).1
    have hval : naturalPairCode (f ‘ x) (∅ : V) = naturalPairCode (f ‘ y) (∅ : V) := by
      rw [← hjv hxD, ← hjv hyD, value_eq_of_kpair_mem hx, value_eq_of_kpair_mem hy]
    exact injective_value_eq hf hfi hxD hyD
      (naturalPairCode_injective (function_value_mem hf hxD) empty_mem_ω
        (function_value_mem hf hyD) empty_mem_ω hval).1
  · intro n hn
    have h1 : (1 : V) ∈ (ω : V) := one_mem_ω
    refine ⟨naturalPairCode n 1, naturalPairCode_natural hn h1,
      naturalPairCode_first_subset hn h1, ?_⟩
    intro hmem
    obtain ⟨x, hx⟩ := mem_range_iff.mp hmem
    have hxD : x ∈ D := (mem_of_mem_functions hj hx).1
    have hval : naturalPairCode (f ‘ x) (∅ : V) = naturalPairCode n 1 := by
      rw [← hjv hxD, value_eq_of_kpair_mem hx]
    have h01 := (naturalPairCode_injective (function_value_mem hf hxD) empty_mem_ω hn h1 hval).2
    have h01mem : (∅ : V) ∈ (1 : V) := by simpa only [zero_def] using zero_mem_one (V := V)
    exact not_mem_empty (h01.symm ▸ h01mem)

def RespectsInternalNames (D j n b : V) : Prop :=
  ∀ x ∈ D, j ‘ x ∈ n → b ‘ (j ‘ x) = x

instance respectsInternalNames_definable : ℒₛₑₜ-relation₄[V] RespectsInternalNames := by
  unfold RespectsInternalNames
  definability

noncomputable def internalNamedAssignmentValue (j n b x i : V) : V :=
  if i ∈ n then b ‘ i else if i ∈ range j then (converseGraph j) ‘ i else x

instance internalNamedAssignmentValue_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (internalNamedAssignmentValue (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun y j n b x i : V ↦
      (i ∈ n ∧ y = b ‘ i) ∨ (i ∉ n ∧ i ∈ range j ∧ y = (converseGraph j) ‘ i) ∨
        (i ∉ n ∧ i ∉ range j ∧ y = x)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalNamedAssignmentValue (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  unfold internalNamedAssignmentValue
  split_ifs <;> simp_all

noncomputable def extendInternalNamedAssignment (j n b m x : V) : V :=
  definableGraph m (internalNamedAssignmentValue j n b x) (by definability)

instance extendInternalNamedAssignment_isFunction (j n b m x : V) :
    IsFunction (extendInternalNamedAssignment j n b m x) := by
  unfold extendInternalNamedAssignment
  infer_instance

instance extendInternalNamedAssignment_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (extendInternalNamedAssignment (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun c j n b m x : V ↦
      ∀ p, p ∈ c ↔ ∃ i ∈ m, p = ⟨i, internalNamedAssignmentValue j n b x i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = extendInternalNamedAssignment (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  simp only [mem_ext_iff, extendInternalNamedAssignment, mem_definableGraph_iff]

theorem extendInternalNamedAssignment_value {j n b m x i : V} (hi : i ∈ m) :
    (extendInternalNamedAssignment j n b m x) ‘ i =
      if i ∈ n then b ‘ i else if i ∈ range j then (converseGraph j) ‘ i else x :=
  value_definableGraph _ _ _ hi

theorem extendInternalNamedAssignment_mem {D j n b m x : V}
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j) (hb : b ∈ D ^ n) (hx : x ∈ D) :
    extendInternalNamedAssignment j n b m x ∈ D ^ m := by
  apply definableGraph_mem_function_of_mapsTo
  intro i _
  unfold internalNamedAssignmentValue
  split_ifs with hin hir
  · exact function_value_mem hb hin
  · exact function_value_mem (converseGraph_mem_function hj hji) hir
  · exact hx

theorem extendInternalNamedAssignment_old_value {j n b m x i : V}
    (hnm : n ⊆ m) (hi : i ∈ n) :
    (extendInternalNamedAssignment j n b m x) ‘ i = b ‘ i := by
  rw [extendInternalNamedAssignment_value (hnm _ hi), ite_eq_left hi]

theorem extendInternalNamedAssignment_respects {D j n b m x : V}
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j) (hb : RespectsInternalNames D j n b) :
    RespectsInternalNames D j m (extendInternalNamedAssignment j n b m x) := by
  let : IsFunction j := IsFunction.of_mem hj
  intro y hy hiy
  rw [extendInternalNamedAssignment_value hiy]
  by_cases hi : j ‘ y ∈ n
  · rw [ite_eq_left hi]
    exact hb y hy hi
  · have hir : j ‘ y ∈ range j := mem_range_of_kpair_mem
      (kpair_value_mem (by rw [domain_eq_of_mem_function hj]; exact hy))
    rw [ite_eq_right hi, ite_eq_left hir, converseGraph_value_value hj hji hy]

theorem extendInternalNamedAssignment_restrict {D j n b m x : V}
    (hb : b ∈ D ^ n) (hnm : n ⊆ m) :
    (extendInternalNamedAssignment j n b m x) ↾ n = b := by
  let : IsFunction b := IsFunction.of_mem hb
  have he : (extendInternalNamedAssignment j n b m x) ↾ n = b ↾ n := by
    apply restrict_eq_of_values
    · intro i hi
      simpa only [extendInternalNamedAssignment, domain_definableGraph] using hnm _ hi
    · intro i hi
      rwa [domain_eq_of_mem_function hb]
    · exact fun i hi ↦ extendInternalNamedAssignment_old_value hnm hi
  exact he.trans (IsFunction.restrict_eq_self b n (by rw [domain_eq_of_mem_function hb]))

theorem extendInternalNamedAssignment_fresh_value {j n b m x k : V}
    (hkm : k ∈ m) (hkn : k ∉ n) (hkj : k ∉ range j) :
    (extendInternalNamedAssignment j n b m x) ‘ k = x := by
  rw [extendInternalNamedAssignment_value hkm, ite_eq_right hkn, ite_eq_right hkj]

theorem exists_internalNamedAssignment_extension {D j n b m : V}
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hb : b ∈ D ^ n) (hbn : RespectsInternalNames D j n b) (hnm : n ⊆ m) :
    ∃ c ∈ D ^ m, c ↾ n = b ∧ RespectsInternalNames D j m c := by
  obtain ⟨x, hx⟩ := hD.nonempty
  exact ⟨extendInternalNamedAssignment j n b m x, extendInternalNamedAssignment_mem hj hji hb hx,
    extendInternalNamedAssignment_restrict hb hnm, extendInternalNamedAssignment_respects hj hji hbn⟩

theorem exists_internalNamedAssignment_extension_at {D j n b m k x : V}
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hb : b ∈ D ^ n) (hbn : RespectsInternalNames D j n b) (hnm : n ⊆ m)
    (hkm : k ∈ m) (hkn : k ∉ n) (hkj : k ∉ range j) (hx : x ∈ D) :
    ∃ c ∈ D ^ m, c ↾ n = b ∧ RespectsInternalNames D j m c ∧ c ‘ k = x := by
  exact ⟨extendInternalNamedAssignment j n b m x, extendInternalNamedAssignment_mem hj hji hb hx,
    extendInternalNamedAssignment_restrict hb hnm, extendInternalNamedAssignment_respects hj hji hbn,
    extendInternalNamedAssignment_fresh_value hkm hkn hkj⟩

theorem exists_internalNamedAssignment_fresh_extension {D j n b x : V}
    (hj : IsSparseInternalNaming D j) (hn : n ∈ (ω : V))
    (hb : b ∈ D ^ n) (hbn : RespectsInternalNames D j n b) (hx : x ∈ D) :
    ∃ k ∈ (ω : V), n ⊆ k ∧ k ∉ range j ∧
      ∃ c ∈ D ^ succ k, c ↾ n = b ∧ RespectsInternalNames D j (succ k) c ∧ c ‘ k = x := by
  obtain ⟨k, hk, hnk, hkj⟩ := hj.2.2 n hn
  refine ⟨k, hk, hnk, hkj, ?_⟩
  apply exists_internalNamedAssignment_extension_at hj.1 hj.2.1 hb hbn
  · exact fun i hi ↦ mem_succ_iff.mpr (Or.inr (hnk i hi))
  · exact mem_succ_self k
  · exact fun hkn ↦ mem_irrefl k (hnk k hkn)
  · exact hkj
  · exact hx

end ZFVP
