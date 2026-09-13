import ZFVP.SetTheory.ForcingOrder
import ZFVP.SetTheory.FunctionUnion
import ZFVP.SetTheory.FiniteSequences

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCoherentThread (θ π f : V) : Prop :=
  ∀ j ∈ θ, ∀ i ∈ j, i ∈ θ → (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ j) = f ‘ i

instance isCoherentThread_definable : ℒₛₑₜ-relation₃[V] IsCoherentThread := by
  unfold IsCoherentThread
  definability

/-- Internal coherent threads, with a common set bounding coordinate values. -/
noncomputable def forcingInverseLimit (θ P π U : V) : V :=
  {f ∈ U ^ θ ; (∀ i ∈ θ, f ‘ i ∈ P ‘ i) ∧
    IsCoherentThread θ π f}

instance forcingInverseLimit_definable : ℒₛₑₜ-function₄[V] forcingInverseLimit := by
  have h : ℒₛₑₜ-relation₅[V] (fun C θ P π U ↦
      ∀ f, f ∈ C ↔ f ∈ U ^ θ ∧ (∀ i ∈ θ, f ‘ i ∈ P ‘ i) ∧
        IsCoherentThread θ π f) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingInverseLimit (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [forcingInverseLimit, mem_sep_iff]

theorem mem_forcingInverseLimit_iff (θ P π U f : V) :
    f ∈ forcingInverseLimit θ P π U ↔ f ∈ U ^ θ ∧
      (∀ i ∈ θ, f ‘ i ∈ P ‘ i) ∧
      ∀ j ∈ θ, ∀ i ∈ j, i ∈ θ → (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ j) = f ‘ i :=
  mem_sep_iff

/-- The coordinatewise order on any set of threads. -/
noncomputable def forcingThreadOrder (θ R C : V) : V :=
  {z ∈ C ×ˢ C ; ∀ i ∈ θ, ⟨(kpair.π₁ z) ‘ i, (kpair.π₂ z) ‘ i⟩ₖ ∈ R ‘ i}

instance forcingThreadOrder_definable : ℒₛₑₜ-function₃[V] forcingThreadOrder := by
  have h : ℒₛₑₜ-relation₄[V] (fun S θ R C ↦
      ∀ z, z ∈ S ↔ z ∈ C ×ˢ C ∧
        ∀ i ∈ θ, ⟨(kpair.π₁ z) ‘ i, (kpair.π₂ z) ‘ i⟩ₖ ∈ R ‘ i) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadOrder (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingThreadOrder, mem_sep_iff]

theorem mem_forcingThreadOrder_iff (θ R C f g : V) :
    ⟨f, g⟩ₖ ∈ forcingThreadOrder θ R C ↔
      f ∈ C ∧ g ∈ C ∧ ∀ i ∈ θ, ⟨f ‘ i, g ‘ i⟩ₖ ∈ R ‘ i := by
  simp only [forcingThreadOrder, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem forcingThreadOrder_preorder {θ P R C : V}
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (hC : ∀ f ∈ C, ∀ i ∈ θ, f ‘ i ∈ P ‘ i) :
    IsForcingPreorder C (forcingThreadOrder θ R C) := by
  refine ⟨sep_subset, ?_, ?_⟩
  · intro f hf
    exact (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
      ⟨hf, hf, fun i hi ↦ (hR i hi).2.1 _ (hC f hf i hi)⟩
  · intro f hf g hg k hk hfg hgk
    have hfg' := (mem_forcingThreadOrder_iff _ _ _ _ _).mp hfg
    have hgk' := (mem_forcingThreadOrder_iff _ _ _ _ _).mp hgk
    exact (mem_forcingThreadOrder_iff _ _ _ _ _).mpr ⟨hf, hk, fun i hi ↦
      (hR i hi).2.2 _ (hC f hf i hi) _ (hC g hg i hi) _ (hC k hk i hi)
        (hfg'.2.2 i hi) (hgk'.2.2 i hi)⟩

theorem forcingInverseLimit_preorder {θ P R π U : V}
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i)) :
    IsForcingPreorder (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U)) :=
  forcingThreadOrder_preorder hR (fun _ hf ↦
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1)

theorem forcingThreadOrder_top {θ P R C t : V} (ht : t ∈ C)
    (hC : ∀ f ∈ C, ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (htop : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i)) :
    IsForcingTop C (forcingThreadOrder θ R C) t := by
  exact ⟨ht, fun f hf ↦ (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
    ⟨hf, ht, fun i hi ↦ (htop i hi).2 _ (hC f hf i hi)⟩⟩

theorem forcingInverseLimit_restrict {θ η P π U f : V} (hη : η ⊆ θ)
    (hf : f ∈ forcingInverseLimit θ P π U) :
    f ↾ η ∈ forcingInverseLimit η P π U := by
  obtain ⟨hfun, hval, hcoh⟩ := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  let := IsFunction.of_mem hfun
  have hv : ∀ i ∈ η, (f ↾ η) ‘ i = f ‘ i := fun i hi ↦
    value_restrict ((domain_eq_of_mem_function hfun).symm ▸ hη i hi) hi
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  refine ⟨function_restrict_mem hfun hη, ?_, ?_⟩
  · intro i hi
    rw [hv i hi]
    exact hval i (hη i hi)
  · intro j hj i hij hi
    rw [hv j hj, hv i hi]
    exact hcoh j (hη j hj) i hij (hη i hi)

theorem forcingInverseLimit_restrict_monotone {θ η P R π U f g : V}
    (hη : η ⊆ θ)
    (hfg : ⟨f, g⟩ₖ ∈ forcingThreadOrder θ R (forcingInverseLimit θ P π U)) :
    ⟨f ↾ η, g ↾ η⟩ₖ ∈ forcingThreadOrder η R (forcingInverseLimit η P π U) := by
  obtain ⟨hf, hg, hfg⟩ := (mem_forcingThreadOrder_iff _ _ _ _ _).mp hfg
  have hf' := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).1
  have hg' := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hg).1
  let := IsFunction.of_mem hf'
  let := IsFunction.of_mem hg'
  apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
  refine ⟨forcingInverseLimit_restrict hη hf, forcingInverseLimit_restrict hη hg, ?_⟩
  intro i hi
  rw [value_restrict ((domain_eq_of_mem_function hf').symm ▸ hη i hi) hi,
    value_restrict ((domain_eq_of_mem_function hg').symm ▸ hη i hi) hi]
  exact hfg i (hη i hi)

end ZFVP
