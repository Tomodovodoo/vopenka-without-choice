import ZFVP.ModelTheory.SymmetricLiftStructureDomain
import ZFVP.ModelTheory.TransitiveZFUnionName
import ZFVP.SetTheory.EndExtensionCoding

/-! The internal symmetric lift domain contains all internally finite assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (L : SymmetricLiftData S U W f)

theorem check_mem_graph_domain {x : V} (hx : x ∈ U) : S.check x ∈ domain L.graph := by
  let one : SetDomain U := ⟨S.one, (inferInstance : IsTransitive U).mem_trans S.top.1 L.poset_mem⟩
  let a : SetDomain U := ⟨x, hx⟩
  have hn : checkName S.one x ∈ U := by
    exact TransitiveZF.checkName_val U one a ▸ (checkName one a).property
  exact (L.graph_domain _).mpr ⟨⟨checkName S.one x,
    hereditarilySymmetric_checkName S.poset S.group S.normal S.top x⟩, hn, rfl⟩

theorem graph_domain_omega : (ω : S.Model) ∈ domain L.graph := by
  have hw : (ω : V) ∈ U := TransitiveZF.omega_val U ▸ (ω : SetDomain U).property
  have he : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  exact he ▸ L.check_mem_graph_domain hw

theorem graph_domain_doubleton {x y : S.Model} (hx : x ∈ domain L.graph) (hy : y ∈ domain L.graph) :
    doubleton x y ∈ domain L.graph := by
  obtain ⟨σ, hσ, rfl⟩ := (L.graph_domain x).mp hx
  obtain ⟨τ, hτ, rfl⟩ := (L.graph_domain y).mp hy
  let hU := TransitiveZF.sequenceSupport U
  have hone := (inferInstance : IsTransitive U).mem_trans S.top.1 L.poset_mem
  have hpair : (S.pairName σ τ).val ∈ U := by
    simpa only [SymmetricContext.pairName, pair_eq_doubleton] using
      hU.doubleton_closed _ (hU.kpair_closed _ hσ _ hone) _ (hU.kpair_closed _ hτ _ hone)
  refine (L.graph_domain _).mpr ⟨S.pairName σ τ, hpair, ?_⟩
  simp only [S.of_pair, pair_eq_doubleton]

theorem graph_domain_sUnion {x : S.Model} (hx : x ∈ domain L.graph) : ⋃ˢ x ∈ domain L.graph := by
  obtain ⟨τ, hτ, rfl⟩ := (L.graph_domain x).mp hx
  let P : SetDomain U := ⟨S.P, L.poset_mem⟩
  let R : SetDomain U := ⟨S.R, L.relation_mem⟩
  let a : SetDomain U := ⟨τ.val, hτ⟩
  have hn : (S.unionName τ).val ∈ U := by
    change forcingUnionName S.P S.R τ.val ∈ U
    exact TransitiveZF.forcingUnionName_val U P R a ▸ (forcingUnionName P R a).property
  refine (L.graph_domain _).mpr ⟨S.unionName τ, hn, ?_⟩
  apply mem_ext
  intro z
  exact mem_sUnion_iff.trans (S.mem_unionName_iff τ z).symm

theorem graph_domain_union {x y : S.Model} (hx : x ∈ domain L.graph) (hy : y ∈ domain L.graph) :
    x ∪ y ∈ domain L.graph := by
  have he : ⋃ˢ doubleton x y = x ∪ y := by
    apply mem_ext
    intro z
    simp only [mem_sUnion_iff, mem_doubleton_iff, mem_union_iff]
    constructor
    · rintro ⟨a, rfl | rfl, hz⟩ <;> tauto
    · rintro (hz | hz)
      · exact ⟨x, Or.inl rfl, hz⟩
      · exact ⟨y, Or.inr rfl, hz⟩
  exact he ▸ L.graph_domain_sUnion (L.graph_domain_doubleton hx hy)

instance graph_domain_sequenceSupport : IsSequenceSupport (domain L.graph) where
  toIsTransitive := L.graph_domain_transitive
  omega_mem := L.graph_domain_omega
  doubleton_closed := fun _ hx _ hy ↦ L.graph_domain_doubleton hx hy
  kpair_closed x hx y hy := by
    have hs : doubleton x x = ({x} : S.Model) := by ext z; simp
    simpa only [kpair, pair_eq_doubleton, hs] using
      L.graph_domain_doubleton (L.graph_domain_doubleton hx hx) (L.graph_domain_doubleton hx hy)
  succ_closed x hx := by
    have he : succ x = x ∪ doubleton x x := by ext z; simp only [mem_succ_iff, mem_union_iff, mem_doubleton_iff]; tauto
    exact he.symm ▸ L.graph_domain_union hx (L.graph_domain_doubleton hx hx)
  union_closed := fun _ hx _ hy ↦ L.graph_domain_union hx hy

end SymmetricLiftData
end ZFVP
