import ZFVP.SetTheory.LowenheimSkolemCardinals
import ZFVP.SetTheory.TransitiveCollapseFixation
import ZFVP.ModelTheory.ElementaryBoundedWitness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- No lower rank surjects onto a weakly LS cardinal. -/
theorem IsWeaklyLSCardinal.no_surjection {κ γ f : V}
    (hκ : IsWeaklyLSCardinal κ) (hγ : γ ∈ κ)
    (hf : f ∈ κ ^ (hierarchy γ)) : range f ≠ κ := by
  intro hr
  have : IsOrdinal κ := hκ.1.1
  have : IsFunction f := IsFunction.of_mem hf
  let α := rank ({f, κ} : V)
  have := hierarchy_transitive α
  have hfα : f ∈ hierarchy α := (mem_hierarchy_iff_rank_mem f α).mpr
    (rank_mem (show f ∈ ({f, κ} : V) by simp))
  have hκα : κ ∈ α := by
    simpa only [rank_of_ordinal] using rank_mem (show κ ∈ ({f, κ} : V) by simp)
  have hκVα : κ ∈ hierarchy α := ordinal_mem_hierarchy_iff.mpr hκα
  obtain ⟨X, hX, hγX, hfX, C, hC, p, hp⟩ :=
    hκ.2.2 γ hγ α inferInstance
      (IsOrdinal.toIsTransitive.transitive _ hκα) f hfα
  have hκX : κ ∈ X := by
    rw [← hr]
    exact hX.range_mem hfX (hr.symm ▸ hκVα)
  have hκsub : κ ⊆ X := by
    intro y hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp (hr.symm ▸ hy)
    have hxd := mem_domain_of_kpair_mem hxy
    have hxγ : x ∈ hierarchy γ := domain_eq_of_mem_function hf ▸ hxd
    exact value_eq_of_kpair_mem hxy ▸ hX.function_value_mem hfX (hγX x hxγ) hxd
  have hpκ := transitiveCollapse_fixes_transitive_member hp hκsub hκX
  have hκC : κ ∈ C := hpκ ▸ function_value_mem hp.2.1 hκX
  have hκV : κ ∈ hierarchy κ := (hierarchy_transitive κ).mem_trans hκC hC
  exact mem_irrefl κ (ordinal_mem_hierarchy_iff.mp hκV)

end ZFVP

