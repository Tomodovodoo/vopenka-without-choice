import ZFVP.ModelTheory.ForcingHierarchyName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- The induction is internal to the quotient: a checked recursion table and
an internal evaluation graph make its entire predicate definable. -/
theorem hierarchyName_value (A : ForcingContext V) (θ : V) [IsOrdinal θ] :
    A.ofName (A.hierarchyName θ) = hierarchy (A.check θ) := by
  let C := forcingNameHierarchy A.P (succ θ)
  have hC : ∀ τ ∈ C, IsForcingName A.P τ := forcingNameHierarchy_names A.P (succ θ)
  let E := A.evaluationGraph C hC
  let g := definableGraph (succ θ) (forcingHierarchyName A.P A.one) (by definability)
  let μ : A.Model → A.Model := fun β ↦ E ‘ ((A.check g) ‘ β)
  have hμ (γ : V) (hγ : γ ∈ succ θ) [IsOrdinal γ] :
      μ (A.check γ) = A.ofName (A.hierarchyName γ) := by
    change E ‘ ((A.check g) ‘ (A.check γ)) = _
    rw [A.check_value (by simpa only [g, domain_definableGraph] using hγ)]
    rw [show g ‘ γ = forcingHierarchyName A.P A.one γ from value_definableGraph _ _ _ hγ]
    exact A.evaluationGraph_value C hC _ (forcingHierarchyName_mem_level A.top.1 hγ)
  have hall := transfinite_induction
    (fun β : A.Model ↦ β ∈ A.check (succ θ) → hierarchy β = μ β) (by unfold μ; definability) ?_
  · have ht := hall (IsOrdinal.toOrdinal (A.check θ)) ((A.check_mem_iff _ _).mpr (by simp))
    exact (hμ θ (by simp)).symm.trans ht.symm
  intro β ih hβ
  obtain ⟨γ, hγ, heγ⟩ := (A.mem_check_iff (succ θ) (β : A.Model)).mp hβ
  let := IsOrdinal.of_mem hγ
  have hIH (η : V) (hηγ : η ∈ γ) :
      let _ := IsOrdinal.of_mem hηγ
      A.ofName (A.hierarchyName η) = hierarchy (A.check η) := by
    let := IsOrdinal.of_mem hηγ
    have hηθ : η ∈ succ θ := IsOrdinal.toIsTransitive.mem_trans hηγ hγ
    have hηβ : A.check η ∈ (β : A.Model) := heγ.symm ▸ (A.check_mem_iff η γ).mpr hηγ
    have hi := ih (IsOrdinal.toOrdinal (A.check η)) hηβ ((A.check_mem_iff _ _).mpr hηθ)
    exact (hμ η hηθ).symm.trans hi.symm
  rw [heγ, hμ γ hγ]
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨η, hηγ, hxη⟩ := (mem_hierarchy_iff_of_ordinal (A.check γ) x).mp hx
    obtain ⟨ξ, hξγ, rfl⟩ := (A.mem_check_iff γ η).mp hηγ
    let := IsOrdinal.of_mem hξγ
    have hx' : x ⊆ A.ofName (A.hierarchyName ξ) := by rwa [hIH ξ hξγ]
    obtain ⟨τ, hτ, heτ⟩ := A.subset_hierarchyName_representative ξ x hx'
    exact (A.mem_hierarchyName_iff γ x).mpr
      ⟨τ, (mem_forcingNameHierarchy A.P γ τ.val).mpr ⟨ξ, hξγ, hτ⟩, heτ.symm⟩
  · intro hx
    obtain ⟨τ, hτ, rfl⟩ := (A.mem_hierarchyName_iff γ x).mp hx
    obtain ⟨ξ, hξγ, hτξ⟩ := (mem_forcingNameHierarchy A.P γ τ.val).mp hτ
    let := IsOrdinal.of_mem hξγ
    apply (mem_hierarchy_iff_of_ordinal (A.check γ) (A.ofName τ)).mpr
    refine ⟨A.check ξ, (A.check_mem_iff _ _).mpr hξγ, ?_⟩
    intro y hy
    obtain ⟨ν, p, _hp, hνp, hey⟩ := (A.mem_ofName_iff τ y).mp hy
    have hν : ν.val ∈ forcingNameHierarchy A.P ξ := (kpair_mem_iff.mp (hτξ _ hνp)).1
    rw [← hIH ξ hξγ]
    exact (A.mem_hierarchyName_iff ξ y).mpr ⟨ν, hν, hey⟩

end ForcingContext
end ZFVP
