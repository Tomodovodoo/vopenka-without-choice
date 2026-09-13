import ZFVP.SetTheory.ForcingSystemExtension
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The graphs storing stage data have exactly their advertised domains. -/
structure IsIterationTable (A f : V) : Prop where
  function : IsFunction f
  domain_eq : domain f = A

theorem IsIterationTable.subset_of_values {A B f g : V}
    (hf : IsIterationTable A f) (hg : IsIterationTable B g)
    (hAB : A ⊆ B) (hv : ∀ x ∈ A, f ‘ x = g ‘ x) : f ⊆ g := by
  have : IsFunction f := hf.function
  have : IsFunction g := hg.function
  intro p hp
  obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hp
  have hx : x ∈ A := hf.domain_eq ▸ mem_domain_of_kpair_mem hp
  exact kpair_mem_iff_value.mpr ⟨hg.domain_eq.symm ▸ hAB x hx,
    (hv x hx).symm.trans (value_eq_of_kpair_mem hp)⟩

theorem forcingFamilyNext_table (θ P Q : V) :
    IsIterationTable (succ θ) (forcingFamilyNext θ P Q) := by
  unfold forcingFamilyNext
  exact ⟨inferInstance, domain_definableGraph _ _ _⟩

theorem forcingMatrixNext_table (θ M C d : V) :
    IsIterationTable (succ θ ×ˢ succ θ) (forcingMatrixNext θ M C d) := by
  unfold forcingMatrixNext
  exact ⟨inferInstance, domain_definableGraph _ _ _⟩

theorem forcingFamilyNext_extends {θ P : V} (h : IsIterationTable θ P) (Q : V) :
    P ⊆ forcingFamilyNext θ P Q := by
  apply h.subset_of_values (forcingFamilyNext_table θ P Q)
  · intro i hi; exact mem_succ_iff.mpr (Or.inr hi)
  · intro i hi; exact (forcingFamilyNext_old hi).symm

theorem forcingMatrixNext_extends {θ M : V} (h : IsIterationTable (θ ×ˢ θ) M)
    (C d : V) : M ⊆ forcingMatrixNext θ M C d := by
  apply h.subset_of_values (forcingMatrixNext_table θ M C d)
  · intro z hz
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hz
    exact mem_prod_iff.mpr ⟨i, mem_succ_iff.mpr (Or.inr hi), j,
      mem_succ_iff.mpr (Or.inr hj), rfl⟩
  · intro z hz
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hz
    exact (forcingMatrixNext_old (mem_succ_iff.mpr (Or.inr hi)) hj).symm

theorem IsIterationTable.sUnion {A B : V}
    (hF : ∀ f ∈ B, IsFunction f) (hC : CompatibleFunctionFamily B)
    (hD : ∀ x, x ∈ A ↔ ∃ f ∈ B, x ∈ domain f) :
    IsIterationTable A (⋃ˢ B) := by
  refine ⟨isFunction_sUnion hF hC, ?_⟩
  apply mem_ext
  intro x
  exact (mem_domain_sUnion_iff B x).trans (hD x).symm

/-- Increasing function graphs agree wherever their domains overlap. -/
theorem compatibleFunctionFamily_of_directed {B : V}
    (hF : ∀ f ∈ B, IsFunction f)
    (hD : ∀ f ∈ B, ∀ g ∈ B, ∃ h ∈ B, f ⊆ h ∧ g ⊆ h) :
    CompatibleFunctionFamily B := by
  intro f hf g hg x y z hxy hxz
  obtain ⟨h, hh, hfh, hgh⟩ := hD f hf g hg
  have : IsFunction h := hF h hh
  exact (value_eq_of_kpair_mem (hfh _ hxy)).symm.trans
    (value_eq_of_kpair_mem (hgh _ hxz))

theorem IsIterationTable.restrict_union {A B f : V}
    (hf : IsIterationTable A f) (hF : ∀ g ∈ B, IsFunction g)
    (hC : CompatibleFunctionFamily B) (hfB : f ∈ B) :
    (⋃ˢ B) ↾ A = f := by
  have : IsFunction f := hf.function
  have : IsFunction (⋃ˢ B) := isFunction_sUnion hF hC
  have hsub : A ⊆ domain (⋃ˢ B) := by
    intro x hx
    exact (mem_domain_sUnion_iff B x).mpr ⟨f, hfB, hf.domain_eq.symm ▸ hx⟩
  have he := restrict_eq_of_values hsub (show A ⊆ domain f by rw [hf.domain_eq])
    (fun x hx ↦ value_sUnion_of_mem hF hC hfB (hf.domain_eq.symm ▸ hx))
  exact he.trans (IsFunction.restrict_eq_self f A (by rw [hf.domain_eq]))

end ZFVP
