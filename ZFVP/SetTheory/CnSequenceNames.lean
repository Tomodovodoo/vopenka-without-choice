import ZFVP.SetTheory.CnSigmaClosure
import ZFVP.SetTheory.ForcingSequenceNames
import ZFVP.SetTheory.FiniteCodingClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.domain_closed {δ x : V} (hδ : Cn 1 δ) (hx : x ∈ hierarchy δ) :
    domain x ∈ hierarchy δ := by
  let := hδ.ordinal
  apply subset_mem_hierarchy_limit hδ.successor_closed
    (sUnion_mem_hierarchy_limit hδ.successor_closed (sUnion_mem_hierarchy_limit hδ.successor_closed hx))
  intro z hz
  exact (mem_sep_iff.mp hz).1

theorem Cn.range_closed {δ x : V} (hδ : Cn 1 δ) (hx : x ∈ hierarchy δ) :
    range x ∈ hierarchy δ := by
  let := hδ.ordinal
  apply subset_mem_hierarchy_limit hδ.successor_closed
    (sUnion_mem_hierarchy_limit hδ.successor_closed (sUnion_mem_hierarchy_limit hδ.successor_closed hx))
  intro z hz
  exact (mem_sep_iff.mp hz).1

theorem Cn.union_closed {δ x y : V} (hδ : Cn 1 δ)
    (hx : x ∈ hierarchy δ) (hy : y ∈ hierarchy δ) : x ∪ y ∈ hierarchy δ := by
  let := hδ.ordinal
  have hu := sUnion_mem_hierarchy_limit hδ.successor_closed (pair_mem_hierarchy_limit hδ.successor_closed hx hy)
  simpa only [pair_eq_doubleton, ← union_def] using hu

theorem pairName_mem_power_product {one σ τ T : V} (hσ : σ ∈ T) (hτ : τ ∈ T) :
    pairName one σ τ ∈ ℘ (T ×ˢ ({one} : V)) := by
  rw [mem_power_iff]
  intro z hz
  rcases show z = ⟨σ, one⟩ₖ ∨ z = ⟨τ, one⟩ₖ from by simpa [pairName] using hz with rfl | rfl
  · exact kpair_mem_iff.mpr ⟨hσ, by simp⟩
  · exact kpair_mem_iff.mpr ⟨hτ, by simp⟩

theorem Cn.sequenceName_closed {δ one s : V} [IsFunction s] (hδ : Cn 1 δ)
    (hone : one ∈ hierarchy δ) (hs : s ∈ hierarchy δ) : sequenceName one s ∈ hierarchy δ := by
  let := hδ.ordinal
  let D := domain (checkName one (domain s))
  let T := D ∪ range s
  let H₁ := ℘ (T ×ˢ ({one} : V))
  let H₂ := ℘ (H₁ ×ˢ ({one} : V))
  have hD : D ∈ hierarchy δ := hδ.domain_closed (hδ.checkName_closed hone (hδ.domain_closed hs))
  have hT : T ∈ hierarchy δ := hδ.union_closed hD (hδ.range_closed hs)
  have honeSet : ({one} : V) ∈ hierarchy δ := by
    simpa using pair_mem_hierarchy_limit hδ.successor_closed hone hone
  have hH₁ : H₁ ∈ hierarchy δ := power_mem_hierarchy_limit hδ.successor_closed
    (prod_mem_hierarchy_limit hδ.successor_closed hT honeSet)
  have hH₂ : H₂ ∈ hierarchy δ := power_mem_hierarchy_limit hδ.successor_closed
    (prod_mem_hierarchy_limit hδ.successor_closed hH₁ honeSet)
  apply subset_mem_hierarchy_limit hδ.successor_closed
    (prod_mem_hierarchy_limit hδ.successor_closed hH₂ honeSet)
  intro z hz
  obtain ⟨i, hi, rfl⟩ := (mem_sequenceName _ _ _).mp hz
  have hci : checkName one i ∈ T := mem_union_iff.mpr (Or.inl
    (mem_domain_of_kpair_mem ((mem_checkName_iff one (domain s) _).mpr ⟨i, hi, rfl⟩)))
  have hsi : s ‘ i ∈ T := mem_union_iff.mpr (Or.inr (mem_range_of_kpair_mem (kpair_value_mem hi)))
  exact kpair_mem_iff.mpr ⟨pairName_mem_power_product
    (pairName_mem_power_product hci hci) (pairName_mem_power_product hci hsi), by simp⟩

end ZFVP
