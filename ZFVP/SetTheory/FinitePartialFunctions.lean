import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.ForcingOrder
import ZFVP.SetTheory.FunctionUnion

/-! The forcing of internal finite partial functions, ordered by reverse inclusion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def finitePartialFunctions (D B : V) : V :=
  {p ∈ ℘ (D ×ˢ B) ; IsFunction p ∧ IsInternallyFinite (domain p)}

theorem mem_finitePartialFunctions (D B p : V) :
    p ∈ finitePartialFunctions D B ↔
      p ⊆ D ×ˢ B ∧ IsFunction p ∧ IsInternallyFinite (domain p) := by
  simp only [finitePartialFunctions, mem_sep_iff, mem_power_iff]

instance finitePartialFunctions_definable : ℒₛₑₜ-function₂[V] finitePartialFunctions := by
  have h : ℒₛₑₜ-relation₃[V] (fun Q D B ↦ ∀ p, p ∈ Q ↔
      p ⊆ D ×ˢ B ∧ IsFunction p ∧ IsInternallyFinite (domain p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = finitePartialFunctions (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_finitePartialFunctions]

noncomputable def reverseInclusionOrder (P : V) : V :=
  {s ∈ P ×ˢ P ; kpair.π₂ s ⊆ kpair.π₁ s}

instance reverseInclusionOrder_definable : ℒₛₑₜ-function₁[V] reverseInclusionOrder := by
  have h : ℒₛₑₜ-relation[V] (fun R P ↦ ∀ s, s ∈ R ↔
      s ∈ P ×ˢ P ∧ kpair.π₂ s ⊆ kpair.π₁ s) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = reverseInclusionOrder (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [reverseInclusionOrder, mem_sep_iff]

theorem pair_mem_reverseInclusionOrder (P p q : V) :
    ⟨p, q⟩ₖ ∈ reverseInclusionOrder P ↔ p ∈ P ∧ q ∈ P ∧ q ⊆ p := by
  simp only [reverseInclusionOrder, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem reverseInclusionOrder_poset (P : V) : IsForcingPoset P (reverseInclusionOrder P) := by
  refine ⟨⟨fun s hs ↦ (mem_sep_iff.mp hs).1, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact (pair_mem_reverseInclusionOrder P p p).mpr ⟨hp, hp, subset_refl _⟩
  · intro p hp q hq r hr hpq hqr
    exact (pair_mem_reverseInclusionOrder P p r).mpr ⟨hp, hr,
      subset_trans ((pair_mem_reverseInclusionOrder P q r).mp hqr).2.2
        ((pair_mem_reverseInclusionOrder P p q).mp hpq).2.2⟩
  · intro p hp q hq hpq hqp
    exact SetTheory.subset_antisymm ((pair_mem_reverseInclusionOrder P q p).mp hqp).2.2
      ((pair_mem_reverseInclusionOrder P p q).mp hpq).2.2

theorem empty_mem_finitePartialFunctions (D B : V) :
    (∅ : V) ∈ finitePartialFunctions D B := by
  apply (mem_finitePartialFunctions D B ∅).mpr
  refine ⟨by simp, inferInstance, ?_⟩
  simpa using (internallyFinite_empty (V := V))

theorem finitePartialFunctions_top (D B : V) :
    IsForcingTop (finitePartialFunctions D B)
      (reverseInclusionOrder (finitePartialFunctions D B)) ∅ := by
  refine ⟨empty_mem_finitePartialFunctions D B, fun p hp ↦ ?_⟩
  exact (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hp, empty_mem_finitePartialFunctions D B, by simp⟩

theorem finitePartialFunction_domain {D B p : V} (hp : p ∈ finitePartialFunctions D B) :
    domain p ⊆ D := by
  intro x hx
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  exact (kpair_mem_iff.mp (((mem_finitePartialFunctions D B p).mp hp).1 _ hxy)).1

theorem finitePartialFunction_range {D B p : V} (hp : p ∈ finitePartialFunctions D B) :
    range p ⊆ B := by
  intro y hy
  obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
  exact (kpair_mem_iff.mp (((mem_finitePartialFunctions D B p).mp hp).1 _ hxy)).2

theorem finitePartialFunction_insert {D B p x y : V}
    (hp : p ∈ finitePartialFunctions D B) (hx : x ∈ D) (hy : y ∈ B)
    (hfresh : x ∉ domain p) : insert ⟨x, y⟩ₖ p ∈ finitePartialFunctions D B := by
  obtain ⟨hpD, hpf, hpfin⟩ := (mem_finitePartialFunctions D B p).mp hp
  have : IsFunction p := hpf
  apply (mem_finitePartialFunctions D B _).mpr
  refine ⟨?_, IsFunction.insert p x y hfresh, ?_⟩
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact kpair_mem_iff.mpr ⟨hx, hy⟩
    · exact hpD _ hz
  · simpa using internallyFinite_insert hpfin x

theorem finitePartialFunction_subset {D B p q : V}
    (hp : p ∈ finitePartialFunctions D B) (hq : q ⊆ p) :
    q ∈ finitePartialFunctions D B := by
  obtain ⟨hpD, hpf, hpfin⟩ := (mem_finitePartialFunctions D B p).mp hp
  have : IsFunction p := hpf
  refine (mem_finitePartialFunctions D B q).mpr
    ⟨subset_trans hq hpD, IsFunction.ofSubset p q hq, internallyFinite_subset hpfin ?_⟩
  intro x hx
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  exact mem_domain_of_kpair_mem (hq _ hxy)

theorem finitePartialFunction_union {D B p q : V}
    (hp : p ∈ finitePartialFunctions D B) (hq : q ∈ finitePartialFunctions D B)
    (hc : ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z) :
    p ∪ q ∈ finitePartialFunctions D B := by
  obtain ⟨hpD, hpf, hpfin⟩ := (mem_finitePartialFunctions D B p).mp hp
  obtain ⟨hqD, hqf, hqfin⟩ := (mem_finitePartialFunctions D B q).mp hq
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
  refine (mem_finitePartialFunctions D B _).mpr ⟨?_, hfun, ?_⟩
  · intro z hz
    exact (mem_union_iff.mp hz).elim (hpD z) (hqD z)
  · have he : domain (p ∪ q) = domain p ∪ domain q := by
      ext x
      simp only [mem_domain_iff, mem_union_iff, exists_or]
    rw [he]
    exact internallyFinite_union hpfin hqfin

theorem finitePartialFunctions_compatible_iff {D B p q : V}
    (hp : p ∈ finitePartialFunctions D B) (hq : q ∈ finitePartialFunctions D B) :
    ForcingCompatible (finitePartialFunctions D B)
      (reverseInclusionOrder (finitePartialFunctions D B)) p q ↔
      ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z := by
  constructor
  · rintro ⟨r, hr, hrp, hrq⟩ x y z hxy hxz
    have : IsFunction r := ((mem_finitePartialFunctions D B r).mp hr).2.1
    exact IsFunction.unique (((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2 _ hxy)
      (((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2 _ hxz)
  · intro hc
    have hu := finitePartialFunction_union hp hq hc
    exact ⟨p ∪ q, hu,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hp, fun z hz ↦ mem_union_iff.mpr (Or.inl hz)⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hq, fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩⟩

theorem finitePartialFunctions_domain_dense {D B x y : V} (hx : x ∈ D) (hy : y ∈ B) :
    ForcingDense (finitePartialFunctions D B)
      (reverseInclusionOrder (finitePartialFunctions D B))
      {p ∈ finitePartialFunctions D B ; x ∈ domain p} := by
  classical
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  by_cases hxp : x ∈ domain p
  · exact ⟨p, mem_sep_iff.mpr ⟨hp, hxp⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hp, subset_refl _⟩⟩
  · have hq := finitePartialFunction_insert hp hx hy hxp
    refine ⟨insert ⟨x, y⟩ₖ p, mem_sep_iff.mpr ⟨hq, ?_⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hp, fun z hz ↦ mem_insert.mpr (Or.inr hz)⟩⟩
    exact mem_domain_of_kpair_mem (show ⟨x, y⟩ₖ ∈ insert ⟨x, y⟩ₖ p by simp)

end ZFVP
