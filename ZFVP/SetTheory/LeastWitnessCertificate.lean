import ZFVP.SetTheory.LeastRankWitnesses
import ZFVP.SetTheory.BoundedPairBinding
import ZFVP.SetTheory.PiOneHierarchy

/-! A canonical certificate recording the least witness rank, two rank segments,
and the full set of witnesses at that rank. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLeastWitnessCertificate (R : V → Prop) (ξ U W C : V) : Prop :=
  IsOrdinal ξ ∧ U = hierarchy ξ ∧ W = hierarchy (succ ξ) ∧ IsNonempty C ∧ C ⊆ W ∧
    (∀ u ∈ C, ξ = rank u ∧ R u) ∧ (∀ u ∈ U, ¬R u) ∧
    ∀ u ∈ W, ξ = rank u → R u → u ∈ C

theorem isLeastWitnessCertificate_definable (R : V → Prop) (hR : ℒₛₑₜ-predicate R) :
    ℒₛₑₜ-relation₄[V] (IsLeastWitnessCertificate R) := by
  unfold IsLeastWitnessCertificate
  definability

theorem IsLeastWitnessCertificate.least_rank {R : V → Prop} {ξ U W C : V}
    (h : IsLeastWitnessCertificate R ξ U W C) :
    IsLeastWitnessRank (fun (_ : V) u ↦ R u) ∅ ξ := by
  let := h.1
  obtain ⟨u, hu⟩ := h.2.2.2.1
  obtain ⟨hr, hR⟩ := h.2.2.2.2.2.1 u hu
  refine ⟨h.1, ⟨u, hR, hr.symm⟩, ?_⟩
  rintro β hβ ⟨v, hv, hrβ⟩
  let := hβ
  rcases IsOrdinal.mem_trichotomy β ξ with hl | he | hg
  · have hvU : v ∈ U := by
      rw [h.2.1, mem_hierarchy_iff_rank_mem, hrβ]
      exact hl
    exact False.elim (h.2.2.2.2.2.2.1 v hvU hv)
  · exact subset_of_eq he.symm
  · exact IsOrdinal.toIsTransitive.transitive _ hg

theorem IsLeastWitnessCertificate.members {R : V → Prop} {ξ U W C : V}
    (h : IsLeastWitnessCertificate R ξ U W C) (u : V) : u ∈ C ↔ R u ∧ rank u = ξ := by
  let := h.1
  constructor
  · intro hu
    have hv := h.2.2.2.2.2.1 u hu
    exact ⟨hv.2, hv.1.symm⟩
  · rintro ⟨hu, hr⟩
    apply h.2.2.2.2.2.2.2 u
    · rw [h.2.2.1, mem_hierarchy_iff_rank_mem, hr]
      simp
    · exact hr.symm
    · exact hu

theorem IsLeastWitnessCertificate.unique {R : V → Prop} {ξ U W C η U' W' C' : V}
    (h : IsLeastWitnessCertificate R ξ U W C)
    (h' : IsLeastWitnessCertificate R η U' W' C') :
    ξ = η ∧ U = U' ∧ W = W' ∧ C = C' := by
  have hr := h.least_rank
  have hr' := h'.least_rank
  have he : ξ = η := subset_antisymm (hr.2.2 η hr'.1 hr'.2.1) (hr'.2.2 ξ hr.1 hr.2.1)
  refine ⟨he, h.2.1.trans ((congrArg hierarchy he).trans h'.2.1.symm),
    h.2.2.1.trans ((congrArg (fun α ↦ hierarchy (succ α)) he).trans h'.2.2.1.symm), ?_⟩
  apply mem_ext
  intro u
  rw [h.members, h'.members, he]

theorem leastWitnessCertificate_exists (R : V → Prop) (hR : ℒₛₑₜ-predicate R)
    (hex : ∃ u, R u) : ∃ ξ U W C, IsLeastWitnessCertificate R ξ U W C := by
  obtain ⟨C, hC, _⟩ := leastRankWitnessSet_existsUnique (fun (_ : V) u ↦ R u)
    (by definability) (∅ : V) hex
  obtain ⟨ξ, hξ, hmem⟩ := hC
  let := hξ.1
  have hc : IsNonempty C := by
    obtain ⟨u, hu, hr⟩ := hξ.2.1
    exact ⟨u, (hmem u).mpr ⟨hu, hr⟩⟩
  refine ⟨ξ, hierarchy ξ, hierarchy (succ ξ), C, hξ.1, rfl, rfl, hc, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [mem_hierarchy_iff_rank_mem, ((hmem u).mp hu).2]
    simp
  · intro u hu
    exact ⟨((hmem u).mp hu).2.symm, ((hmem u).mp hu).1⟩
  · intro u hu hRu
    have hr : rank u ∈ ξ := (mem_hierarchy_iff_rank_mem _ _).mp hu
    have hs : ξ ⊆ rank u := hξ.2.2 (rank u) inferInstance ⟨u, hRu, rfl⟩
    exact mem_irrefl (rank u) (hs _ hr)
  · intro u _ hr hu
    exact (hmem u).mpr ⟨hu, hr.symm⟩

end ZFVP
