import ZFVP.ModelTheory.SymmetricModelGraph
import ZFVP.ModelTheory.TransitiveZFSymmetricMap

/-! The restriction of the forcing lift is a function belonging to the symmetric model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure SymmetricLiftData (S : SymmetricContext V) (U W f : V) where
  embedding : IsCodedMembershipEmbedding U W f
  poset_mem : S.P ∈ U
  relation_mem : S.R ∈ U
  group_mem : S.Γ ∈ U
  filter_mem : S.F ∈ U
  fix_poset : f ‘ S.P = S.P
  fix_relation : f ‘ S.R = S.R
  fix_group : f ‘ S.Γ = S.Γ
  fix_filter : f ‘ S.F = S.F
  fix_conditions : ∀ p ∈ S.P, f ‘ p = p
  fix_automorphisms : ∀ π ∈ S.Γ, f ‘ π = π

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (L : SymmetricLiftData S U W f)

noncomputable def nameDomain (_L : SymmetricLiftData S U W f) : V := {τ ∈ U ; IsHereditarilySymmetricName S.P S.Γ S.F τ}

include L

omit [IsTransitive U] [IsTransitive W] [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem nameDomain_hs {σ : V} (hσ : σ ∈ L.nameDomain) :
    IsHereditarilySymmetricName S.P S.Γ S.F σ := (mem_sep_iff.mp hσ).2

theorem image_hs {σ : V} (hσ : σ ∈ U) (hhs : IsHereditarilySymmetricName S.P S.Γ S.F σ) :
    IsHereditarilySymmetricName S.P S.Γ S.F (f ‘ σ) :=
  L.embedding.preserves_hereditarilySymmetricName ⟨S.P, L.poset_mem⟩ ⟨S.Γ, L.group_mem⟩
    ⟨S.F, L.filter_mem⟩ ⟨σ, hσ⟩ L.fix_poset L.fix_group L.fix_filter hhs

noncomputable def imageName (σ : S.Name) (hσ : σ.val ∈ U) : S.Name :=
  ⟨f ‘ σ.val, L.image_hs hσ σ.property⟩

theorem graphName_hs :
    IsHereditarilySymmetricName S.P S.Γ S.F (nameMapGraph S.one L.nameDomain f) :=
  L.embedding.symmetric_graphName ⟨S.P, L.poset_mem⟩ ⟨S.Γ, L.group_mem⟩ ⟨S.F, L.filter_mem⟩
    S.poset S.group S.normal S.top L.fix_poset L.fix_group L.fix_filter L.fix_automorphisms

noncomputable def graph : S.Model := S.mapGraph L.nameDomain f L.graphName_hs

theorem image_eq_of_eq (σ τ : S.Name) (hσ : σ.val ∈ U) (hτ : τ.val ∈ U)
    (he : S.ofName σ = S.ofName τ) : S.ofName (L.imageName σ hσ) = S.ofName (L.imageName τ hτ) := by
  have hs := (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ σ τ).mp he
  have ht := L.embedding.genericMeets_atomicEquality_map ⟨S.P, L.poset_mem⟩ ⟨S.R, L.relation_mem⟩
    ⟨σ.val, hσ⟩ ⟨τ.val, hτ⟩ S.G L.fix_poset L.fix_relation
    (fun p hp ↦ L.fix_conditions p (S.generic.1.1 p hp)) hs
  exact (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ _ _).mpr ht

instance graph_isFunction : IsFunction L.graph := by
  apply S.mapGraph_isFunction L.nameDomain f L.graphName_hs
    (fun _ hσ ↦ L.nameDomain_hs hσ)
    (fun _ hσ ↦ L.image_hs (mem_sep_iff.mp hσ).1 (L.nameDomain_hs hσ))
  intro σ hσ τ hτ he
  exact L.image_eq_of_eq ⟨σ, L.nameDomain_hs hσ⟩ ⟨τ, L.nameDomain_hs hτ⟩
    (mem_sep_iff.mp hσ).1 (mem_sep_iff.mp hτ).1 he

theorem graph_domain (x : S.Model) :
    x ∈ domain L.graph ↔ ∃ σ : S.Name, σ.val ∈ U ∧ x = S.ofName σ := by
  rw [graph, S.mem_domain_mapGraph_iff L.nameDomain f L.graphName_hs
    (fun _ hσ ↦ L.nameDomain_hs hσ)
    (fun _ hσ ↦ L.image_hs (mem_sep_iff.mp hσ).1 (L.nameDomain_hs hσ))]
  constructor
  · rintro ⟨σ, hσ, he⟩
    exact ⟨⟨σ, L.nameDomain_hs hσ⟩, (mem_sep_iff.mp hσ).1, he⟩
  · rintro ⟨σ, hσ, he⟩
    exact ⟨σ.val, mem_sep_iff.mpr ⟨hσ, σ.property⟩, he⟩

theorem graph_value (σ : S.Name) (hσ : σ.val ∈ U) :
    L.graph ‘ (S.ofName σ) = S.ofName (L.imageName σ hσ) := by
  have : IsFunction (S.mapGraph L.nameDomain f L.graphName_hs) := L.graph_isFunction
  exact S.mapGraph_value L.nameDomain f L.graphName_hs
    (fun _ hτ ↦ L.nameDomain_hs hτ)
    (fun _ hτ ↦ L.image_hs (mem_sep_iff.mp hτ).1 (L.nameDomain_hs hτ))
    (mem_sep_iff.mpr ⟨hσ, σ.property⟩)

theorem exists_symmetric_lift : ∃ E : S.Model, IsFunction E ∧
    (∀ x, x ∈ domain E ↔ ∃ σ : S.Name, σ.val ∈ U ∧ x = S.ofName σ) ∧
    ∀ σ : S.Name, ∀ hσ : σ.val ∈ U, E ‘ (S.ofName σ) = S.ofName (L.imageName σ hσ) :=
  ⟨L.graph, L.graph_isFunction, L.graph_domain, L.graph_value⟩

end SymmetricLiftData
end ZFVP
