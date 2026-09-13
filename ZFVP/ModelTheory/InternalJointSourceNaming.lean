import ZFVP.ModelTheory.InternalNamedConditions
import ZFVP.ModelTheory.BinaryRelationZFModel

/-! Actual assignments respecting fixed source names and an independent family
of names. Disjoint names can share one sparse countable naming. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_jointSourceAssignment {D I j k c : V} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k) (hc : c ∈ D ^ I) :
    ∃ f ∈ D ^ (ω : V), (∀ x ∈ D, f ‘ (j ‘ x) = x) ∧
      ∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i := by
  have hkinv := converseGraph_mem_function hk hki
  let b := compose (converseGraph k) c
  have hb : b ∈ D ^ range k := compose_function hkinv hc
  have hrespect : RespectsInternalNames D j (range k) b := by
    intro x hx hmem
    exact False.elim (hdis _ (value_mem_range hj hx) hmem)
  obtain ⟨a, ha⟩ := hD
  let f := extendInternalNamedAssignment j (range k) b (ω : V) a
  have hf : f ∈ D ^ (ω : V) := extendInternalNamedAssignment_mem hj hji hb ha
  refine ⟨f, hf, ?_, ?_⟩
  · intro x hx
    exact extendInternalNamedAssignment_respects hj hji hrespect x hx (function_value_mem hj hx)
  · intro i hi
    rw [extendInternalNamedAssignment_old_value (range_subset_of_mem_function hk) (value_mem_range hk hi)]
    rw [value_compose_of_mem_function hkinv hc (value_mem_range hk hi), converseGraph_value_value hk hki hi]

theorem exists_jointSourceNaming {M I j k c : V} (hD : IsNonempty (structureDomain M))
    (hj : j ∈ (ω : V) ^ structureDomain M) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k) (hc : c ∈ structureDomain M ^ I) :
    ∃ f, SourceNaming M j f ∧ ∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i := by
  obtain ⟨f, hf, hfj, hfk⟩ := exists_jointSourceAssignment hD hj hji hk hki hdis hc
  exact ⟨f, ⟨hf, hfj⟩, hfk⟩

theorem exists_binaryJointSourceNaming {D R I j k c : V} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k) (hc : c ∈ D ^ I) :
    ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
      ∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i := by
  obtain ⟨f, hf, hfj, hfk⟩ :=
    exists_jointSourceAssignment hD hj hji hk hki hdis hc
  refine ⟨f, ?_, hfk⟩
  simpa only [SourceNaming, binaryRelationStructureCode_domain] using And.intro hf hfj

theorem exists_disjointSparseSourceNames {D I : V}
    (hD : IsInternallyCountable D) (hI : IsInternallyCountable I) :
    ∃ j k, j ∈ (ω : V) ^ D ∧ Injective j ∧ k ∈ (ω : V) ^ I ∧ Injective k ∧
      (∀ n ∈ range j, n ∉ range k) ∧
      ∀ B, namedTheorySupport B ⊆ range j ∪ range k → HasFreshBackgroundNames j B := by
  let U := repl (fun x : V ↦ ⟨(0 : V), x⟩ₖ) (by definability) D ∪
    repl (fun i : V ↦ ⟨(1 : V), i⟩ₖ) (by definability) I
  have hU : IsInternallyCountable U := internallyCountable_union
    (internallyCountable_repl _ _ hD) (internallyCountable_repl _ _ hI)
  have hleft {x : V} (hx : x ∈ D) : ⟨(0 : V), x⟩ₖ ∈ U :=
    mem_union_iff.mpr (Or.inl ((repl_spec _).mpr ⟨x, hx, rfl⟩))
  have hright {i : V} (hi : i ∈ I) : ⟨(1 : V), i⟩ₖ ∈ U :=
    mem_union_iff.mpr (Or.inr ((repl_spec _).mpr ⟨i, hi, rfl⟩))
  obtain ⟨e, he⟩ := exists_sparseInternalNaming hU
  let j := definableGraph D (fun x ↦ e ‘ ⟨(0 : V), x⟩ₖ) (by definability)
  let k := definableGraph I (fun i ↦ e ‘ ⟨(1 : V), i⟩ₖ) (by definability)
  have hj : j ∈ (ω : V) ^ D := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun x hx ↦ function_value_mem he.1 (hleft hx))
  have hk : k ∈ (ω : V) ^ I := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun i hi ↦ function_value_mem he.1 (hright hi))
  have hjv {x : V} (hx : x ∈ D) : j ‘ x = e ‘ ⟨(0 : V), x⟩ₖ := value_definableGraph _ _ _ hx
  have hkv {i : V} (hi : i ∈ I) : k ‘ i = e ‘ ⟨(1 : V), i⟩ₖ := value_definableGraph _ _ _ hi
  let : IsFunction j := IsFunction.of_mem hj
  let : IsFunction k := IsFunction.of_mem hk
  have hji : Injective j := by
    intro x y z hx hy
    have hxD := (mem_of_mem_functions hj hx).1
    have hyD := (mem_of_mem_functions hj hy).1
    have hh : e ‘ ⟨(0 : V), x⟩ₖ = e ‘ ⟨(0 : V), y⟩ₖ := by
      rw [← hjv hxD, ← hjv hyD, value_eq_of_kpair_mem hx, value_eq_of_kpair_mem hy]
    exact (kpair_iff.mp (injective_value_eq he.1 he.2.1 (hleft hxD) (hleft hyD) hh)).2
  have hki : Injective k := by
    intro x y z hx hy
    have hxI := (mem_of_mem_functions hk hx).1
    have hyI := (mem_of_mem_functions hk hy).1
    have hh : e ‘ ⟨(1 : V), x⟩ₖ = e ‘ ⟨(1 : V), y⟩ₖ := by
      rw [← hkv hxI, ← hkv hyI, value_eq_of_kpair_mem hx, value_eq_of_kpair_mem hy]
    exact (kpair_iff.mp (injective_value_eq he.1 he.2.1 (hright hxI) (hright hyI) hh)).2
  have hjrange : range j ⊆ range e := by
    intro n hn
    obtain ⟨x, hx⟩ := mem_range_iff.mp hn
    have hxD := (mem_of_mem_functions hj hx).1
    rw [← value_eq_of_kpair_mem hx, hjv hxD]
    exact value_mem_range he.1 (hleft hxD)
  have hkrange : range k ⊆ range e := by
    intro n hn
    obtain ⟨i, hi⟩ := mem_range_iff.mp hn
    have hiI := (mem_of_mem_functions hk hi).1
    rw [← value_eq_of_kpair_mem hi, hkv hiI]
    exact value_mem_range he.1 (hright hiI)
  refine ⟨j, k, hj, hji, hk, hki, ?_, ?_⟩
  · intro n hnj hnk
    obtain ⟨x, hx⟩ := mem_range_iff.mp hnj
    obtain ⟨i, hi⟩ := mem_range_iff.mp hnk
    have hxD := (mem_of_mem_functions hj hx).1
    have hiI := (mem_of_mem_functions hk hi).1
    have hh : e ‘ ⟨(0 : V), x⟩ₖ = e ‘ ⟨(1 : V), i⟩ₖ := by
      rw [← hjv hxD, ← hkv hiI, value_eq_of_kpair_mem hx, value_eq_of_kpair_mem hi]
    exact zero_ne_one (kpair_iff.mp (injective_value_eq he.1 he.2.1 (hleft hxD) (hright hiI) hh)).1
  · intro B hB
    apply freshBackgroundNames_of_sparse he hjrange
    intro n hn
    rcases mem_union_iff.mp (hB n hn) with hn | hn
    · exact hjrange n hn
    · exact hkrange n hn

end ZFVP
