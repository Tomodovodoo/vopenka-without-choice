import ZFVP.ModelTheory.WoodinSparseWitnessPrefix

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCoherentForcingAutomorphismFamily.of_code_values {θ c d H : V}
    (h : IsCoherentForcingAutomorphismFamily θ c H)
    (hP : ∀ i ∈ θ, (forcingCodeP c) ‘ i = (forcingCodeP d) ‘ i)
    (hR : ∀ i ∈ θ, (forcingCodeR c) ‘ i = (forcingCodeR d) ‘ i)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, (forcingCodeπ c) ‘ ⟨i,j⟩ₖ = (forcingCodeπ d) ‘ ⟨i,j⟩ₖ)
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, (forcingCodeE c) ‘ ⟨i,j⟩ₖ = (forcingCodeE d) ‘ ⟨i,j⟩ₖ) :
    IsCoherentForcingAutomorphismFamily θ d H := by
  constructor
  · intro i hi
    rw [← hP i hi, ← hR i hi]
    exact h.iso i hi
  · intro i hi j hj hij p hp
    rw [← hP j hj] at hp
    rw [← hπ i hi j hj]
    exact h.proj i hi j hj hij p hp
  · intro i hi j hj hij p hp
    rw [← hP i hi] at hp
    rw [← hE i hi j hj]
    exact h.sec i hi j hj hij p hp

theorem IsCoherentForcingAutomorphismFamily.of_code_extension {θ η c d H : V}
    (h : IsCoherentForcingAutomorphismFamily θ c H)
    (hc : IsForcingIterationCode η c) (hd : IsForcingIterationCode θ d)
    (he : ForcingCodeExtends d c) : IsCoherentForcingAutomorphismFamily θ d H := by
  have hP := fun i hi ↦ hd.tableP.value_of_subset hc.tableP he.subP (x := i) hi
  have hR := fun i hi ↦ hd.tableR.value_of_subset hc.tableR he.subR (x := i) hi
  have hπ := fun i hi j hj ↦ hd.tableπ.value_of_subset hc.tableπ he.subπ (kpair_mem_iff.mpr ⟨hi,hj⟩ : ⟨i,j⟩ₖ ∈ θ ×ˢ θ)
  have hE := fun i hi j hj ↦ hd.tableE.value_of_subset hc.tableE he.subE (kpair_mem_iff.mpr ⟨hi,hj⟩ : ⟨i,j⟩ₖ ∈ θ ×ˢ θ)
  constructor
  · intro i hi
    rw [hP i hi, hR i hi]
    exact h.iso i hi
  · intro i hi j hj hij p hp
    rw [hP j hj] at hp
    rw [hπ i hi j hj]
    exact h.proj i hi j hj hij p hp
  · intro i hi j hj hij p hp
    rw [hP i hi] at hp
    rw [hE i hi j hj]
    exact h.sec i hi j hj hij p hp

theorem IsCoherentAutomorphismRow.of_code_extension {θ η c d H f : V}
    (h : IsCoherentAutomorphismRow θ c H f)
    (hc : IsForcingIterationCode (succ θ) c) (hd : IsForcingIterationCode η d)
    (he : ForcingCodeExtends c d) : IsCoherentAutomorphismRow θ d H f := by
  have hP := fun i hi ↦ hc.tableP.value_of_subset hd.tableP he.subP (x := i) hi
  have hR := hc.tableR.value_of_subset hd.tableR he.subR (mem_succ_self θ)
  have ht := hc.tablet.value_of_subset hd.tablet he.subt (mem_succ_self θ)
  have hπ := fun i hi ↦ hc.tableπ.value_of_subset hd.tableπ he.subπ (kpair_mem_iff.mpr ⟨mem_succ_iff.mpr (Or.inr hi),mem_succ_self θ⟩ : ⟨i,θ⟩ₖ ∈ succ θ ×ˢ succ θ)
  have hE := fun i hi ↦ hc.tableE.value_of_subset hd.tableE he.subE (kpair_mem_iff.mpr ⟨mem_succ_iff.mpr (Or.inr hi),mem_succ_self θ⟩ : ⟨i,θ⟩ₖ ∈ succ θ ×ˢ succ θ)
  constructor
  · rw [← hP θ (mem_succ_self θ), ← hR]
    exact h.iso
  · rw [← ht]
    exact h.fixesTop
  · intro i hi p hp
    rw [← hP θ (mem_succ_self θ)] at hp
    rw [← hπ i hi]
    exact h.proj i hi p hp
  · intro i hi p hp
    rw [← hP i (mem_succ_iff.mpr (Or.inr hi))] at hp
    rw [← hE i hi]
    exact h.sec i hi p hp

end ZFVP
