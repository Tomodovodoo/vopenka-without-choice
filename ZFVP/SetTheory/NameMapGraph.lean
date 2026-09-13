import ZFVP.SetTheory.SymmetricPairNames

/-! A name for the graph induced by an internal map on a set of names. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def nameMapGraph (one D f : V) : V :=
  repl (fun σ ↦ ⟨orderedPairName one σ (f ‘ σ), one⟩ₖ) (by definability) D

instance nameMapGraph_definable : ℒₛₑₜ-function₃[V] nameMapGraph := by
  have h : ℒₛₑₜ-relation₄ (fun B one D f : V ↦
      ∀ z, z ∈ B ↔ ∃ σ ∈ D, z = ⟨orderedPairName one σ (f ‘ σ), one⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameMapGraph (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [nameMapGraph, repl_spec]

theorem mem_nameMapGraph_iff (one D f z : V) :
    z ∈ nameMapGraph one D f ↔ ∃ σ ∈ D, z = ⟨orderedPairName one σ (f ‘ σ), one⟩ₖ :=
  repl_spec (by definability)

theorem nameMapGraph_isName {P one D f : V} (hone : one ∈ P)
    (hD : ∀ σ ∈ D, IsForcingName P σ) (hf : ∀ σ ∈ D, IsForcingName P (f ‘ σ)) :
    IsForcingName P (nameMapGraph one D f) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, hσ, rfl⟩ := (mem_nameMapGraph_iff _ _ _ _).mp hz
  exact ⟨orderedPairName one σ (f ‘ σ), one, hone, rfl,
    orderedPairName_isName hone (hD σ hσ) (hf σ hσ)⟩

theorem nameMapGraph_fixed {P one D f π : V} (hone : one ∈ P) (hfix : π ‘ one = one)
    (hD : ∀ σ ∈ D, IsForcingName P σ) (hf : ∀ σ ∈ D, IsForcingName P (f ‘ σ))
    (hperm : ∀ ν : V, ν ∈ D ↔ ∃ σ ∈ D, ν = nameAction π σ)
    (hequiv : ∀ σ ∈ D, f ‘ (nameAction π σ) = nameAction π (f ‘ σ)) :
    nameAction π (nameMapGraph one D f) = nameMapGraph one D f := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  rw [mem_nameAction_iff (nameMapGraph_isName hone hD hf), mem_nameMapGraph_iff]
  constructor
  · rintro ⟨ν, p, hνp, rfl⟩
    obtain ⟨σ, hσ, he⟩ := (mem_nameMapGraph_iff _ _ _ _).mp hνp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    refine ⟨nameAction π σ, (hperm _).mpr ⟨σ, hσ, rfl⟩, ?_⟩
    rw [nameAction_orderedPairName hone (hD σ hσ) (hf σ hσ), hfix, hequiv σ hσ]
  · rintro ⟨ν, hν, rfl⟩
    obtain ⟨σ, hσ, rfl⟩ := (hperm ν).mp hν
    refine ⟨orderedPairName one σ (f ‘ σ), one,
      (mem_nameMapGraph_iff _ _ _ _).mpr ⟨σ, hσ, rfl⟩, ?_⟩
    rw [nameAction_orderedPairName hone (hD σ hσ) (hf σ hσ), hfix, hequiv σ hσ]

theorem hereditarilySymmetric_nameMapGraph {P R Γ F one D f : V}
    (hR : IsForcingPoset P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hone : IsForcingTop P R one)
    (hD : ∀ σ ∈ D, IsHereditarilySymmetricName P Γ F σ)
    (hf : ∀ σ ∈ D, IsHereditarilySymmetricName P Γ F (f ‘ σ))
    (hperm : ∀ π ∈ Γ, ∀ ν : V, ν ∈ D ↔ ∃ σ ∈ D, ν = nameAction π σ)
    (hequiv : ∀ π ∈ Γ, ∀ σ ∈ D, f ‘ (nameAction π σ) = nameAction π (f ‘ σ)) :
    IsHereditarilySymmetricName P Γ F (nameMapGraph one D f) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨nameMapGraph_isName hone.1 (fun σ hσ ↦ (hD σ hσ).1) (fun σ hσ ↦ (hf σ hσ).1), ?_⟩, ?_⟩
  · have he : nameStabilizer Γ (nameMapGraph one D f) = Γ := by
      apply SetTheory.mem_ext_iff.mpr
      intro π
      simp only [nameStabilizer, mem_sep_iff]
      exact ⟨And.left, fun hπ ↦ ⟨hπ, nameMapGraph_fixed hone.1
        (forcingAutomorphism_top hR hone (hΓ.1 π hπ))
        (fun σ hσ ↦ (hD σ hσ).1) (fun σ hσ ↦ (hf σ hσ).1) (hperm π hπ) (hequiv π hπ)⟩⟩
    rw [he]
    exact hF.2.1
  · intro ν p hp
    obtain ⟨σ, hσ, he⟩ := (mem_nameMapGraph_iff _ _ _ _).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact hereditarilySymmetric_orderedPairName hR hΓ hF hone (hD σ hσ) (hf σ hσ)

theorem mem_nameValue_nameMapGraph_iff {G one : V} (hone : one ∈ G) (D f z : V) :
    z ∈ nameValue G (nameMapGraph one D f) ↔
      ∃ σ ∈ D, z = ⟨nameValue G σ, nameValue G (f ‘ σ)⟩ₖ := by
  rw [mem_nameValue_iff]
  constructor
  · rintro ⟨ν, p, _, hνp, rfl⟩
    obtain ⟨σ, hσ, he⟩ := (mem_nameMapGraph_iff _ _ _ _).mp hνp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨σ, hσ, nameValue_orderedPairName hone σ (f ‘ σ)⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨orderedPairName one σ (f ‘ σ), one, hone,
      (mem_nameMapGraph_iff _ _ _ _).mpr ⟨σ, hσ, rfl⟩, (nameValue_orderedPairName hone σ (f ‘ σ)).symm⟩

theorem nameValue_nameMapGraph_mem_function {G one D f : V} (hone : one ∈ G)
    (huniq : ∀ σ ∈ D, ∀ τ ∈ D, nameValue G σ = nameValue G τ →
      nameValue G (f ‘ σ) = nameValue G (f ‘ τ)) :
    nameValue G (nameMapGraph one D f) ∈
      (repl (fun σ ↦ nameValue G (f ‘ σ)) (by definability) D) ^
        (repl (nameValue G) (by definability) D) := by
  apply mem_function.intro
  · intro z hz
    obtain ⟨σ, hσ, rfl⟩ := (mem_nameValue_nameMapGraph_iff hone D f z).mp hz
    exact kpair_mem_iff.mpr ⟨(repl_spec (by definability)).mpr ⟨σ, hσ, rfl⟩,
      (repl_spec (by definability)).mpr ⟨σ, hσ, rfl⟩⟩
  · intro x hx
    obtain ⟨σ, hσ, rfl⟩ := (repl_spec (by definability)).mp hx
    refine ⟨nameValue G (f ‘ σ), (mem_nameValue_nameMapGraph_iff hone D f _).mpr ⟨σ, hσ, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨τ, hτ, he⟩ := (mem_nameValue_nameMapGraph_iff hone D f _).mp hy
    obtain ⟨heq, rfl⟩ := kpair_iff.mp he
    exact (huniq σ hσ τ hτ heq).symm

theorem nameValue_nameMapGraph_value {G one D f : V} (hone : one ∈ G)
    (huniq : ∀ σ ∈ D, ∀ τ ∈ D, nameValue G σ = nameValue G τ →
      nameValue G (f ‘ σ) = nameValue G (f ‘ τ)) {σ : V} (hσ : σ ∈ D) :
    (nameValue G (nameMapGraph one D f)) ‘ (nameValue G σ) = nameValue G (f ‘ σ) := by
  have := IsFunction.of_mem (nameValue_nameMapGraph_mem_function hone huniq)
  exact value_eq_of_kpair_mem ((mem_nameValue_nameMapGraph_iff hone D f _).mpr ⟨σ, hσ, rfl⟩)

end ZFVP
