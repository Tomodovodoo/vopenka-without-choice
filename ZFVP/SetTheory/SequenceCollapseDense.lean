import ZFVP.SetTheory.SequenceCollapseAbsorption
import ZFVP.SetTheory.SetCollapse

/-! The sequence tree `λ^{<ω}` is a dense subposet of the collapse `Coll(ω, λ)`: the identity is
a dense embedding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A sequence contained in a function is the restriction of that function to its length. -/
theorem sequence_eq_restrict_of_subset_function {A u t m : V} (hu : IsFunction u) (ht : t ∈ A ^ m)
    (h : t ⊆ u) : t = u ↾ m := by
  have : IsFunction t := IsFunction.of_mem ht
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function ht p hp)
    exact kpair_mem_restrict_iff.mpr ⟨h _ hp, hx⟩
  · intro hp
    obtain ⟨hpu, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
    have hxt : ⟨x, t ‘ x⟩ₖ ∈ t := kpair_value_mem (by rw [domain_eq_of_mem_function ht]; exact hx)
    have := IsFunction.unique (h _ hxt) hpu
    rw [← this]
    exact hxt

/-- Sequences are finite partial functions. -/
theorem finiteSequences_subset_collapse (lam : V) : finiteSequences lam ⊆ collapseConditions lam := by
  intro s hs
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff _ _).mp hs
  refine (mem_finitePartialFunctions _ _ _).mpr ⟨?_, IsFunction.of_mem hsn, ?_⟩
  · intro p hp
    obtain ⟨i, hi, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hsn p hp)
    exact kpair_mem_iff.mpr ⟨IsOrdinal.toIsTransitive.mem_trans hi hn, hy⟩
  · rw [domain_eq_of_mem_function hsn]
    exact ⟨n, hn, CardEQ.refl n⟩

/-- Every finite partial function extends to a sequence. -/
theorem exists_sequence_extending {lam p : V} (h0 : (∅ : V) ∈ lam) (hp : p ∈ collapseConditions lam) :
    ∃ s ∈ finiteSequences lam, p ⊆ s := by
  obtain ⟨hpsub, hpf, hpfin⟩ := (mem_finitePartialFunctions _ _ _).mp hp
  have hdom : domain p ⊆ (ω : V) := by
    intro x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    exact (kpair_mem_iff.mp (hpsub _ hxy)).1
  obtain ⟨n, hn, hbound⟩ := internallyFinite_naturals_bounded hpfin hdom
  let F : V → V := fun i ↦ p ‘ i
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  refine ⟨definableGraph n F hF, (mem_finiteSequences_iff _ _).mpr ⟨n, hn,
    definableGraph_mem_function_of_mapsTo n lam F hF ?_⟩, ?_⟩
  · intro i hi
    by_cases hid : i ∈ domain p
    · obtain ⟨y, hy⟩ := mem_domain_iff.mp hid
      have : F i = y := value_eq_of_kpair_mem hy
      rw [this]
      exact (kpair_mem_iff.mp (hpsub _ hy)).2
    · have : F i = ∅ := value_eq_empty_of_not_mem_domain hid
      rw [this]
      exact h0
  · intro q hq
    obtain ⟨i, _, y, _, rfl⟩ := mem_prod_iff.mp (hpsub q hq)
    exact (pair_mem_definableGraph_iff _ _ _ _ _).mpr
      ⟨hbound i (mem_domain_of_kpair_mem hq), (value_eq_of_kpair_mem hq).symm⟩

/-- The identity is a dense embedding of the sequence tree into the collapse. -/
theorem sequence_collapse_denseEmbedding {lam : V} (h0 : (∅ : V) ∈ lam) :
    IsDenseEmbedding (finiteSequences lam) (sequenceOrder lam) (collapseConditions lam)
      (collapseOrder lam) (identity (finiteSequences lam)) := by
  have hsub := finiteSequences_subset_collapse lam
  refine ⟨mem_function_of_mem_function_of_subset (identity_mem_function _) hsub, ?_, ?_, ?_⟩
  · intro p hp q hq hqp
    obtain ⟨_, _, hpq⟩ := (pair_mem_sequenceOrder_iff _ _ _).mp hqp
    rw [identity_value hq, identity_value hp]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hsub q hq, hsub p hp, hpq⟩
  · intro p hp q hq hinc hc
    rw [identity_value hp, identity_value hq] at hc
    obtain ⟨u, hu, hup, huq⟩ := hc
    obtain ⟨_, _, hpu⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hup
    obtain ⟨_, _, hqu⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp huq
    have huf : IsFunction u := ((mem_finitePartialFunctions _ _ _).mp hu).2.1
    obtain ⟨n, hn, hpn⟩ := (mem_finiteSequences_iff _ _).mp hp
    obtain ⟨m, hm, hqm⟩ := (mem_finiteSequences_iff _ _).mp hq
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal m := IsOrdinal.of_mem hm
    have hpeq := sequence_eq_restrict_of_subset_function huf hpn hpu
    have hqeq := sequence_eq_restrict_of_subset_function huf hqm hqu
    apply hinc
    apply (sequence_compatible_iff hp hq).mpr
    rcases IsOrdinal.subset_or_supset (α := n) (β := m) with h | h
    · left
      rw [hpeq, hqeq]
      intro z hz
      obtain ⟨hzu, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
      exact kpair_mem_restrict_iff.mpr ⟨hzu, h x hx⟩
    · right
      rw [hpeq, hqeq]
      intro z hz
      obtain ⟨hzu, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
      exact kpair_mem_restrict_iff.mpr ⟨hzu, h x hx⟩
  · intro p hp
    obtain ⟨s, hs, hps⟩ := exists_sequence_extending h0 hp
    refine ⟨s, hs, ?_⟩
    rw [identity_value hs]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hsub s hs, hp, hps⟩

end ZFVP
