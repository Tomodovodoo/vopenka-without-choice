import ZFVP.ModelTheory.TransitiveZFNames
import ZFVP.SetTheory.NameValue
import ZFVP.SetTheory.HereditarySymmetry
import ZFVP.SetTheory.GenericName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Values of ground-model names, with the filter taken in the ambient model. -/
noncomputable def forcingExtensionDomain (U P G : V) : V :=
  repl (nameValue G) (by definability) {τ ∈ U ; IsForcingName P τ}

noncomputable def symmetricExtensionDomain (U P Γ F G : V) : V :=
  repl (nameValue G) (by definability) {τ ∈ U ; IsHereditarilySymmetricName P Γ F τ}

theorem mem_forcingExtensionDomain_iff (U P G x : V) :
    x ∈ forcingExtensionDomain U P G ↔
      ∃ τ ∈ U, IsForcingName P τ ∧ x = nameValue G τ := by
  simp only [forcingExtensionDomain, repl_spec, mem_sep_iff]
  aesop

theorem mem_symmetricExtensionDomain_iff (U P Γ F G x : V) :
    x ∈ symmetricExtensionDomain U P Γ F G ↔
      ∃ τ ∈ U, IsHereditarilySymmetricName P Γ F τ ∧ x = nameValue G τ := by
  simp only [symmetricExtensionDomain, repl_spec, mem_sep_iff]
  aesop

theorem symmetricExtensionDomain_subset (U P Γ F G : V) :
    symmetricExtensionDomain U P Γ F G ⊆ forcingExtensionDomain U P G := by
  intro x hx
  obtain ⟨τ, hτU, hτ, he⟩ := (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mp hx
  exact (mem_forcingExtensionDomain_iff _ _ _ _).mpr ⟨τ, hτU, hτ.1, he⟩

theorem forcingExtensionDomain_transitive (U P G : V) [IsTransitive U] :
    IsTransitive (forcingExtensionDomain U P G) := by
  constructor
  intro x hx y hy
  obtain ⟨τ, hτU, hτ, rfl⟩ := (mem_forcingExtensionDomain_iff _ _ _ _).mp hx
  obtain ⟨σ, p, _, hσp, rfl⟩ := (mem_nameValue_iff _ _ _).mp hy
  have hpairU := (inferInstance : IsTransitive U).mem_trans hσp hτU
  exact (mem_forcingExtensionDomain_iff _ _ _ _).mpr
    ⟨σ, (kpair_components_mem_transitive hpairU).1, forcingName_subname hτ hσp, rfl⟩

theorem symmetricExtensionDomain_transitive (U P Γ F G : V) [IsTransitive U] :
    IsTransitive (symmetricExtensionDomain U P Γ F G) := by
  constructor
  intro x hx y hy
  obtain ⟨τ, hτU, hτ, rfl⟩ := (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mp hx
  obtain ⟨σ, p, _, hσp, rfl⟩ := (mem_nameValue_iff _ _ _).mp hy
  have hpairU := (inferInstance : IsTransitive U).mem_trans hσp hτU
  exact (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mpr
    ⟨σ, (kpair_components_mem_transitive hpairU).1,
      hereditarilySymmetric_mem_closure hτ (subname_mem_nameClosure hσp), rfl⟩

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem genericName_val (P one : SetDomain U) :
    (genericName P one).val = genericName P.val one.val := by
  unfold genericName
  apply repl_val U
  intro p _
  rw [kpair_val U, checkName_val U]

theorem generic_mem_forcingExtensionDomain (P one : SetDomain U) (G : V)
    (honeP : one ∈ P) (honeG : one.val ∈ G) (hGP : G ⊆ P.val) :
    G ∈ forcingExtensionDomain U P.val G := by
  have hnameU := (genericName P one).property
  rw [genericName_val U] at hnameU
  exact (mem_forcingExtensionDomain_iff _ _ _ _).mpr
    ⟨genericName P.val one.val, hnameU, genericName_isName (show one.val ∈ P.val from honeP),
      (nameValue_genericName honeG hGP).symm⟩

theorem ground_subset_forcingExtensionDomain (P one : SetDomain U) (G : V)
    (honeP : one ∈ P) (honeG : one.val ∈ G) : U ⊆ forcingExtensionDomain U P.val G := by
  intro x hx
  let x' : SetDomain U := ⟨x, hx⟩
  have hcheck := (checkName one x').property
  rw [checkName_val U] at hcheck
  exact (mem_forcingExtensionDomain_iff _ _ _ _).mpr
    ⟨checkName one.val x, hcheck, checkName_isName (show one.val ∈ P.val from honeP) x,
      (nameValue_checkName honeG x).symm⟩

theorem ground_subset_symmetricExtensionDomain (P one : SetDomain U) (R Γ F G : V)
    (hR : IsForcingPoset P.val R) (hΓ : IsForcingAutomorphismGroup P.val R Γ)
    (hF : IsNormalSubgroupFilter P.val Γ F) (hone : IsForcingTop P.val R one.val)
    (honeG : one.val ∈ G) : U ⊆ symmetricExtensionDomain U P.val Γ F G := by
  intro x hx
  let x' : SetDomain U := ⟨x, hx⟩
  have hcheck := (checkName one x').property
  rw [checkName_val U] at hcheck
  exact (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mpr
    ⟨checkName one.val x, hcheck, hereditarilySymmetric_checkName hR hΓ hF hone x,
      (nameValue_checkName honeG x).symm⟩

theorem pairName_mem_ground {σ τ one : V} (hσ : σ ∈ U) (hτ : τ ∈ U) (hone : one ∈ U) :
    ({⟨σ, one⟩ₖ, ⟨τ, one⟩ₖ} : V) ∈ U := by
  let σ' : SetDomain U := ⟨σ, hσ⟩
  let τ' : SetDomain U := ⟨τ, hτ⟩
  let one' : SetDomain U := ⟨one, hone⟩
  have h := ({⟨σ', one'⟩ₖ, ⟨τ', one'⟩ₖ} : SetDomain U).property
  simpa only [insert_val U, singleton_val U, kpair_val U] using h

theorem forcingExtensionDomain_pair {P G one x y : V} (honeU : one ∈ U)
    (honeP : one ∈ P) (honeG : one ∈ G)
    (hx : x ∈ forcingExtensionDomain U P G) (hy : y ∈ forcingExtensionDomain U P G) :
    ({x, y} : V) ∈ forcingExtensionDomain U P G := by
  obtain ⟨σ, hσU, hσ, rfl⟩ := (mem_forcingExtensionDomain_iff _ _ _ _).mp hx
  obtain ⟨τ, hτU, hτ, rfl⟩ := (mem_forcingExtensionDomain_iff _ _ _ _).mp hy
  exact (mem_forcingExtensionDomain_iff _ _ _ _).mpr
    ⟨{⟨σ, one⟩ₖ, ⟨τ, one⟩ₖ}, pairName_mem_ground U hσU hτU honeU,
      forcingName_pair hσ hτ honeP, (nameValue_pair honeG σ τ).symm⟩

theorem symmetricExtensionDomain_pair {P R Γ F G one x y : V} (honeU : one ∈ U)
    (hR : IsForcingPoset P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hone : IsForcingTop P R one) (honeG : one ∈ G)
    (hx : x ∈ symmetricExtensionDomain U P Γ F G) (hy : y ∈ symmetricExtensionDomain U P Γ F G) :
    ({x, y} : V) ∈ symmetricExtensionDomain U P Γ F G := by
  obtain ⟨σ, hσU, hσ, rfl⟩ := (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mp hx
  obtain ⟨τ, hτU, hτ, rfl⟩ := (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mp hy
  exact (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mpr
    ⟨{⟨σ, one⟩ₖ, ⟨τ, one⟩ₖ}, pairName_mem_ground U hσU hτU honeU,
      hereditarilySymmetric_pair hR hΓ hF hone hσ hτ, (nameValue_pair honeG σ τ).symm⟩

end TransitiveZF
end ZFVP
