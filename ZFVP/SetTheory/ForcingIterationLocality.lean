import ZFVP.SetTheory.ForcingIterationSystem

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Every law of an iteration is witnessed inside a successor prefix. -/
theorem IsForcingIterationSystem.of_prefixes {θ P R π E L t : V} [IsOrdinal θ]
    (h : ∀ j ∈ θ, IsForcingIterationSystem (succ j) P R π E L t) :
    IsForcingIterationSystem θ P R π E L t := by
  have self (i : V) : i ∈ succ i := mem_succ_iff.mpr (Or.inl rfl)
  have below {i j : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) : i ∈ succ j := by
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  have trans {i j k : V} (hij : i ⊆ j) (hjk : j ⊆ k) : i ⊆ k := fun x hx ↦ hjk x (hij x hx)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_⟩⟩
  · intro i hi j hj hij
    exact (h j hj).split.projMaps i (below hi hj hij) j (self j) hij
  · intro i hi j hj hij
    exact (h j hj).split.secMaps i (below hi hj hij) j (self j) hij
  · intro i hi
    exact (h i hi).split.secId i (self i)
  · intro i hi j hj k hk hij hjk
    exact (h k hk).split.projComp i (below hi hk (trans hij hjk)) j (below hj hk hjk)
      k (self k) hij hjk
  · intro i hi j hj k hk hij hjk
    exact (h k hk).split.secComp i (below hi hk (trans hij hjk)) j (below hj hk hjk)
      k (self k) hij hjk
  · intro i hi j hj hij
    exact (h j hj).split.retraction i (below hi hj hij) j (self j) hij
  · intro i hi
    exact (h i hi).order.preorder i (self i)
  · intro i hi j hj hij
    exact (h j hj).order.projMono i (below hi hj hij) j (self j) hij
  · intro i hi j hj hij
    exact (h j hj).order.below i (below hi hj hij) j (self j) hij
  · intro i hi j hj hij
    exact (h j hj).functions.projection i (below hi hj hij) j (self j) hij
  · intro i hi j hj hij
    exact (h j hj).functions.sectionMap i (below hi hj hij) j (self j) hij
  · intro i hi
    exact (h i hi).tops.top i (self i)
  · intro i hi j hj hij
    exact (h j hj).tops.projTop i (below hi hj hij) j (self j) hij
  · intro i hi j hj hij
    exact (h j hj).tops.secTop i (below hi hj hij) j (self j) hij
  · intro i hi j hj hij
    exact (h j hj).lifts.lift i (below hi hj hij) j (self j) hij
  · intro i hi j hj k hk hij hjk
    exact (h k hk).lifts.commute i (below hi hk (trans hij hjk)) j (below hj hk hjk)
      k (self k) hij hjk
  · intro i hi k hk j hj hik hkj
    exact (h j hj).compatible.compatible i (below hi hj (trans hik hkj)) k (below hk hj hkj)
      j (self j) hik hkj

end ZFVP
