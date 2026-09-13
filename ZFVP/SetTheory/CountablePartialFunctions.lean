import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.ForcingClosure
import ZFVP.SetTheory.DependentChoicePathUnions

/-! The forcing of internal countable partial functions, ordered by reverse inclusion.
Descending sequences of length at most omega have lower bounds once countable
unions of countable sets are countable. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def countablePartialFunctions (D B : V) : V :=
  {p ∈ ℘ (D ×ˢ B) ; IsFunction p ∧ IsInternallyCountable (domain p)}

theorem mem_countablePartialFunctions (D B p : V) :
    p ∈ countablePartialFunctions D B ↔
      p ⊆ D ×ˢ B ∧ IsFunction p ∧ IsInternallyCountable (domain p) := by
  simp only [countablePartialFunctions, mem_sep_iff, mem_power_iff]

instance countablePartialFunctions_definable : ℒₛₑₜ-function₂[V] countablePartialFunctions := by
  have h : ℒₛₑₜ-relation₃[V] (fun Q D B ↦ ∀ p, p ∈ Q ↔
      p ⊆ D ×ˢ B ∧ IsFunction p ∧ IsInternallyCountable (domain p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = countablePartialFunctions (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_countablePartialFunctions]

theorem finitePartialFunction_countable {D B p : V} (hp : p ∈ finitePartialFunctions D B) :
    p ∈ countablePartialFunctions D B := by
  obtain ⟨hpD, hpf, hpfin⟩ := (mem_finitePartialFunctions D B p).mp hp
  exact (mem_countablePartialFunctions D B p).mpr ⟨hpD, hpf, internallyCountable_of_finite hpfin⟩

theorem empty_mem_countablePartialFunctions (D B : V) :
    (∅ : V) ∈ countablePartialFunctions D B :=
  finitePartialFunction_countable (empty_mem_finitePartialFunctions D B)

theorem countablePartialFunctions_top (D B : V) :
    IsForcingTop (countablePartialFunctions D B)
      (reverseInclusionOrder (countablePartialFunctions D B)) ∅ := by
  refine ⟨empty_mem_countablePartialFunctions D B, fun p hp ↦ ?_⟩
  exact (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, empty_mem_countablePartialFunctions D B, by simp⟩

theorem countablePartialFunction_domain {D B p : V} (hp : p ∈ countablePartialFunctions D B) :
    domain p ⊆ D := by
  intro x hx
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  exact (kpair_mem_iff.mp (((mem_countablePartialFunctions D B p).mp hp).1 _ hxy)).1

theorem countablePartialFunction_range {D B p : V} (hp : p ∈ countablePartialFunctions D B) :
    range p ⊆ B := by
  intro y hy
  obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
  exact (kpair_mem_iff.mp (((mem_countablePartialFunctions D B p).mp hp).1 _ hxy)).2

theorem countablePartialFunction_insert {D B p x y : V}
    (hp : p ∈ countablePartialFunctions D B) (hx : x ∈ D) (hy : y ∈ B)
    (hfresh : x ∉ domain p) : insert ⟨x, y⟩ₖ p ∈ countablePartialFunctions D B := by
  obtain ⟨hpD, hpf, hpc⟩ := (mem_countablePartialFunctions D B p).mp hp
  have : IsFunction p := hpf
  apply (mem_countablePartialFunctions D B _).mpr
  refine ⟨?_, IsFunction.insert p x y hfresh, ?_⟩
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact kpair_mem_iff.mpr ⟨hx, hy⟩
    · exact hpD _ hz
  · simpa using internallyCountable_insert hpc x

theorem countablePartialFunction_subset {D B p q : V}
    (hp : p ∈ countablePartialFunctions D B) (hq : q ⊆ p) :
    q ∈ countablePartialFunctions D B := by
  obtain ⟨hpD, hpf, hpc⟩ := (mem_countablePartialFunctions D B p).mp hp
  have : IsFunction p := hpf
  refine (mem_countablePartialFunctions D B q).mpr
    ⟨subset_trans hq hpD, IsFunction.ofSubset p q hq, internallyCountable_subset hpc ?_⟩
  intro x hx
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  exact mem_domain_of_kpair_mem (hq _ hxy)

theorem countablePartialFunction_union {D B p q : V}
    (hp : p ∈ countablePartialFunctions D B) (hq : q ∈ countablePartialFunctions D B)
    (hc : ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z) :
    p ∪ q ∈ countablePartialFunctions D B := by
  obtain ⟨hpD, hpf, hpc⟩ := (mem_countablePartialFunctions D B p).mp hp
  obtain ⟨hqD, hqf, hqc⟩ := (mem_countablePartialFunctions D B q).mp hq
  have : IsFunction p := hpf
  have : IsFunction q := hqf
  have hfun : IsFunction (p ∪ q) := by
    have hf : ∀ f ∈ ({p, q} : V), IsFunction f := by
      intro f hf
      rcases show f = p ∨ f = q from by simpa using hf with rfl | rfl <;> assumption
    have hcompat : CompatibleFunctionFamily ({p, q} : V) := by
      intro f hf g hg x y z hxy hxz
      have hff : f = p ∨ f = q := by simpa using hf
      have hgg : g = p ∨ g = q := by simpa using hg
      rcases hff with rfl | rfl <;> rcases hgg with rfl | rfl
      · exact IsFunction.unique hxy hxz
      · exact hc x y z hxy hxz
      · exact (hc x z y hxz hxy).symm
      · exact IsFunction.unique hxy hxz
    simpa using isFunction_sUnion hf hcompat
  refine (mem_countablePartialFunctions D B _).mpr ⟨?_, hfun, ?_⟩
  · intro z hz
    exact (mem_union_iff.mp hz).elim (hpD z) (hqD z)
  · have he : domain (p ∪ q) = domain p ∪ domain q := by
      ext x
      simp only [mem_domain_iff, mem_union_iff, exists_or]
    rw [he]
    exact internallyCountable_union hpc hqc

theorem countablePartialFunctions_compatible_iff {D B p q : V}
    (hp : p ∈ countablePartialFunctions D B) (hq : q ∈ countablePartialFunctions D B) :
    ForcingCompatible (countablePartialFunctions D B)
      (reverseInclusionOrder (countablePartialFunctions D B)) p q ↔
      ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z := by
  constructor
  · rintro ⟨r, hr, hrp, hrq⟩ x y z hxy hxz
    have : IsFunction r := ((mem_countablePartialFunctions D B r).mp hr).2.1
    exact IsFunction.unique (((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2 _ hxy)
      (((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2 _ hxz)
  · intro hc
    have hu := countablePartialFunction_union hp hq hc
    exact ⟨p ∪ q, hu,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hp, fun z hz ↦ mem_union_iff.mpr (Or.inl hz)⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hq, fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩⟩

theorem countablePartialFunctions_domain_dense {D B x y : V} (hx : x ∈ D) (hy : y ∈ B) :
    ForcingDense (countablePartialFunctions D B)
      (reverseInclusionOrder (countablePartialFunctions D B))
      {p ∈ countablePartialFunctions D B ; x ∈ domain p} := by
  classical
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  by_cases hxp : x ∈ domain p
  · exact ⟨p, mem_sep_iff.mpr ⟨hp, hxp⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hp, subset_refl _⟩⟩
  · have hq := countablePartialFunction_insert hp hx hy hxp
    refine ⟨insert ⟨x, y⟩ₖ p, mem_sep_iff.mpr ⟨hq, ?_⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hp, fun z hz ↦ mem_insert.mpr (Or.inr hz)⟩⟩
    exact mem_domain_of_kpair_mem (show ⟨x, y⟩ₖ ∈ insert ⟨x, y⟩ₖ p by simp)

/-- A finite family of countable sets has countable union, without any choice. -/
theorem internallyCountable_sUnion_of_finite {A : V} (hA : IsInternallyFinite A)
    (h : ∀ x ∈ A, IsInternallyCountable x) : IsInternallyCountable (⋃ˢ A) := by
  apply internallyFinite_induction
    (fun A ↦ (∀ x ∈ A, IsInternallyCountable x) → IsInternallyCountable (⋃ˢ A))
    (by definability) ?_ ?_ A hA h
  · intro _
    simpa using (internallyCountable_empty (V := V))
  · intro C c ih hall
    rw [sUnion_insert]
    exact internallyCountable_union (hall c (mem_insert.mpr (Or.inl rfl)))
      (ih fun x hx ↦ hall x (mem_insert.mpr (Or.inr hx)))

theorem domain_sUnion_range_eq {α f : V} [IsFunction f] (hd : domain f = α) :
    domain (⋃ˢ range f) =
      ⋃ˢ range (definableGraph α (fun i ↦ domain (f ‘ i)) (by definability)) := by
  let C := definableGraph α (fun i ↦ domain (f ‘ i)) (by definability)
  have hdC : domain C = α := domain_definableGraph _ _ _
  apply mem_ext
  intro x
  rw [mem_domain_sUnion_iff]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨i, hip⟩ := mem_range_iff.mp hp
    have hi : i ∈ α := hd ▸ mem_domain_of_kpair_mem hip
    have hpi := value_eq_of_kpair_mem hip
    have hc : C ‘ i = domain p := (value_definableGraph _ _ _ hi).trans (congrArg domain hpi)
    exact mem_sUnion_iff.mpr ⟨C ‘ i, mem_range_of_kpair_mem
      (kpair_value_mem (show i ∈ domain C from hdC.symm ▸ hi)), hc.symm ▸ hx⟩
  · rintro hx
    obtain ⟨E, hE, hx⟩ := mem_sUnion_iff.mp hx
    obtain ⟨i, hiE⟩ := mem_range_iff.mp hE
    have hi : i ∈ α := hdC ▸ mem_domain_of_kpair_mem hiE
    have hEi : E = domain (f ‘ i) := (value_eq_of_kpair_mem hiE).symm.trans
      (value_definableGraph _ _ _ hi)
    exact ⟨f ‘ i, mem_range_of_kpair_mem (kpair_value_mem
      (show i ∈ domain f from hd.symm ▸ hi)), hEi ▸ hx⟩

/-- The union of a descending sequence of countable partial functions of length at most
omega is a countable partial function. -/
theorem countablePartialFunctions_chain_union {D B α f : V} [IsOrdinal α]
    (hCC : InternalCountableChoice V) (hαω : α ⊆ (ω : V))
    (hf : IsForcingDescending (countablePartialFunctions D B)
      (reverseInclusionOrder (countablePartialFunctions D B)) α f) :
    ⋃ˢ range f ∈ countablePartialFunctions D B := by
  let := IsFunction.of_mem hf.1
  have hB : ∀ p ∈ range f, p ∈ countablePartialFunctions D B := range_subset_of_mem_function hf.1
  have hfun : ∀ p ∈ range f, IsFunction p :=
    fun p hp ↦ ((mem_countablePartialFunctions D B p).mp (hB p hp)).2.1
  have hc : CompatibleFunctionFamily (range f) :=
    compatible_range_of_increasing hf.1
      (fun s hs ↦ ((mem_countablePartialFunctions D B s).mp hs).2.1)
      (fun i hi j hj ↦ ((pair_mem_reverseInclusionOrder _ _ _).mp (hf.2 i hi j hj)).2.2)
  have hd : domain f = α := domain_eq_of_mem_function hf.1
  refine (mem_countablePartialFunctions D B _).mpr ⟨?_, isFunction_sUnion hfun hc, ?_⟩
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_sUnion_iff.mp hz
    exact ((mem_countablePartialFunctions D B p).mp (hB p hp)).1 z hzp
  · rw [domain_sUnion_range_eq hd]
    let C := definableGraph α (fun i ↦ domain (f ‘ i)) (by definability)
    have hdC : domain C = α := domain_definableGraph _ _ _
    have hcount : ∀ i ∈ α, IsInternallyCountable (C ‘ i) := by
      intro i hi
      rw [show C ‘ i = domain (f ‘ i) from value_definableGraph _ _ _ hi]
      exact ((mem_countablePartialFunctions D B _).mp (function_value_mem hf.1 hi)).2.2
    let := IsFunction.of_mem (definableGraph_mem_function α (fun i ↦ domain (f ‘ i)) (by definability))
    rcases IsOrdinal.subset_iff.mp hαω with rfl | hαmem
    · exact countable_union_of_countableChoice hCC hdC hcount
    · have hdomfin : IsInternallyFinite (domain C) := by
        rw [hdC]
        exact internallyFinite_of_cardLE_natural hαmem (CardLE.refl _)
      have hCfin : IsInternallyFinite C := internallyFinite_function hdomfin
      apply internallyCountable_sUnion_of_finite (internallyFinite_range hCfin)
      intro E hE
      obtain ⟨i, hiE⟩ := mem_range_iff.mp hE
      have hi : i ∈ α := hdC ▸ mem_domain_of_kpair_mem hiE
      rw [← value_eq_of_kpair_mem hiE]
      exact hcount i hi

theorem countablePartialFunctions_closedAt {D B α : V} (hCC : InternalCountableChoice V)
    (hα : IsOrdinal α) (hαω : α ⊆ (ω : V)) :
    IsForcingClosedAt (countablePartialFunctions D B)
      (reverseInclusionOrder (countablePartialFunctions D B)) α := by
  let := hα
  intro f hf
  let := IsFunction.of_mem hf.1
  have hp := countablePartialFunctions_chain_union hCC hαω hf
  refine ⟨⋃ˢ range f, hp, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, function_value_mem hf.1 hi, ?_⟩⟩
  intro z hz
  exact mem_sUnion_iff.mpr ⟨f ‘ i, mem_range_of_kpair_mem (kpair_value_mem
    (show i ∈ domain f from (domain_eq_of_mem_function hf.1).symm ▸ hi)), hz⟩

end ZFVP
