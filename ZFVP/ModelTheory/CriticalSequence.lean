import ZFVP.ModelTheory.CriticalPointCardinal
import ZFVP.SetTheory.NaturalIteration
import ZFVP.SetTheory.FiniteCofinality

/-! The critical sequence runs through all internal natural numbers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def criticalIterate (f κ n : V) : V :=
  naturalIteration (fun x ↦ f ‘ x) (by definability) κ n

instance criticalIterate_definable (f κ : V) : ℒₛₑₜ-function₁[V] (criticalIterate f κ) :=
  naturalIteration_definable _ (by definability) _

@[simp] theorem criticalIterate_zero (f κ : V) : criticalIterate f κ 0 = κ :=
  naturalIteration_zero _ _ _

theorem criticalIterate_succ (f κ : V) {n : V} (hn : n ∈ (ω : V)) :
    criticalIterate f κ (succ n) = f ‘ (criticalIterate f κ n) :=
  naturalIteration_succ _ _ _ hn

noncomputable def criticalSequence (f κ : V) : V :=
  naturalIterationGraph (fun x ↦ f ‘ x) (by definability) κ

instance criticalSequence_isFunction (f κ : V) : IsFunction (criticalSequence f κ) :=
  naturalIterationGraph_isFunction _ _ _

@[simp] theorem criticalSequence_domain (f κ : V) : domain (criticalSequence f κ) = ω :=
  domain_naturalIterationGraph _ _ _

theorem criticalSequence_value (f κ : V) {n : V} (hn : n ∈ (ω : V)) :
    (criticalSequence f κ) ‘ n = criticalIterate f κ n := naturalIterationGraph_value _ _ _ hn

noncomputable def criticalLimit (f κ : V) : V := ⋃ˢ range (criticalSequence f κ)

theorem mem_criticalLimit_iff (f κ x : V) :
    x ∈ criticalLimit f κ ↔ ∃ n ∈ (ω : V), x ∈ criticalIterate f κ n := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hn : n ∈ (ω : V) := by simpa using mem_domain_of_kpair_mem hny
    exact ⟨n, hn, (value_eq_of_kpair_mem hny).symm.trans (criticalSequence_value f κ hn) ▸ hxy⟩
  · rintro ⟨n, hn, hxn⟩
    refine mem_sUnion_iff.mpr ⟨criticalIterate f κ n, ?_, hxn⟩
    rw [← criticalSequence_value f κ hn]
    exact mem_range_of_kpair_mem (kpair_value_mem (by simpa using hn))

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem iterate_spec {n : V} (hn : n ∈ (ω : V)) :
    IsOrdinal (criticalIterate f κ n) ∧ criticalIterate f κ n ∈ hierarchy δ ∧
      criticalIterate f κ n ∈ f ‘ (criticalIterate f κ n) := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  exact naturalIteration_invariant (fun x ↦ f ‘ x) (by definability) κ
    (fun x ↦ IsOrdinal x ∧ x ∈ hierarchy δ ∧ x ∈ f ‘ x) (by definability)
    ⟨hκ.ordinal, hκ.mem_domain, hκ.lt_value h⟩
    (fun x hx ↦ ⟨h.value_ordinal hx.1 hx.2.1, function_value_mem h.function hx.2.1,
      (h.value_mem_iff hx.2.1 (function_value_mem h.function hx.2.1)).mpr hx.2.2⟩) n hn

theorem iterate_increasing {n : V} (hn : n ∈ (ω : V)) :
    criticalIterate f κ n ∈ criticalIterate f κ (succ n) := by
  rw [criticalIterate_succ f κ hn]
  exact (iterate_spec hδ h hκ hn).2.2

theorem iterate_mem_limit {n : V} (hn : n ∈ (ω : V)) :
    criticalIterate f κ n ∈ criticalLimit f κ :=
  (mem_criticalLimit_iff f κ _).mpr ⟨succ n, ω_succ_closed hn, iterate_increasing hδ h hκ hn⟩

theorem limit_ordinal : IsOrdinal (criticalLimit f κ) := by
  apply IsOrdinal.sUnion
  intro y hy
  obtain ⟨n, hny⟩ := mem_range_iff.mp hy
  have hn : n ∈ (ω : V) := by simpa using mem_domain_of_kpair_mem hny
  have he : y = criticalIterate f κ n :=
    (value_eq_of_kpair_mem hny).symm.trans (criticalSequence_value f κ hn)
  exact he.symm ▸ (iterate_spec hδ h hκ hn).1

theorem sequence_function : criticalSequence f κ ∈ (criticalLimit f κ) ^ (ω : V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ (by definability) (fun n hn ↦ iterate_mem_limit hδ h hκ hn)

theorem cofinal : IsCofinalMap (criticalLimit f κ) (ω : V) (criticalSequence f κ) := by
  refine ⟨sequence_function hδ h hκ, ?_⟩
  intro x hx
  obtain ⟨n, hn, hxn⟩ := (mem_criticalLimit_iff f κ x).mp hx
  let := (iterate_spec hδ h hκ hn).1
  exact ⟨n, hn, (criticalSequence_value f κ hn).symm ▸ IsOrdinal.toIsTransitive.transitive x hxn⟩

theorem limit_subset_domain : criticalLimit f κ ⊆ δ := by
  let := hδ.ordinal
  intro x hx
  obtain ⟨n, hn, hxn⟩ := (mem_criticalLimit_iff f κ x).mp hx
  let := (iterate_spec hδ h hκ hn).1
  exact IsOrdinal.toIsTransitive.mem_trans hxn (ordinal_mem_hierarchy_iff.mp (iterate_spec hδ h hκ hn).2.1)

theorem limit_succ_closed {x : V} (hx : x ∈ criticalLimit f κ) : succ x ∈ criticalLimit f κ := by
  let := limit_ordinal hδ h hκ
  let := IsOrdinal.of_mem hx
  obtain ⟨n, hn, hxn⟩ := (mem_criticalLimit_iff f κ x).mp hx
  let := (iterate_spec hδ h hκ hn).1
  let := (iterate_spec hδ h hκ (ω_succ_closed hn)).1
  have hs : succ x ⊆ criticalIterate f κ n := by
    intro y hy
    rcases mem_succ_iff.mp hy with rfl | hy
    · exact hxn
    · exact IsOrdinal.toIsTransitive.mem_trans hy hxn
  have hsn : succ x ∈ criticalIterate f κ (succ n) := by
    rcases IsOrdinal.subset_iff.mp hs with he | hl
    · exact he.symm ▸ iterate_increasing hδ h hκ hn
    · exact IsOrdinal.toIsTransitive.mem_trans hl (iterate_increasing hδ h hκ hn)
  exact (mem_criticalLimit_iff f κ _).mpr ⟨succ n, ω_succ_closed hn, hsn⟩

theorem limit_cofinality : internalCofinality (criticalLimit f κ) = (ω : V) := by
  let := limit_ordinal hδ h hκ
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  have hκlim : κ ∈ criticalLimit f κ := by simpa using iterate_mem_limit hδ h hκ (by simp : (0 : V) ∈ ω)
  have h0κ : (0 : V) ∈ κ := by
    let := hκ.ordinal
    exact IsOrdinal.toIsTransitive.mem_trans (by simp : (0 : V) ∈ ω) (hκ.omega_lt h)
  exact SetTheory.subset_antisymm (internalCofinality_minimal (cofinal hδ h hκ))
    (infinite_cofinality_of_succ_closed _ (IsOrdinal.toIsTransitive.mem_trans h0κ hκlim)
      (fun _ hx ↦ limit_succ_closed hδ h hκ hx))

end CriticalSequence

end ZFVP
