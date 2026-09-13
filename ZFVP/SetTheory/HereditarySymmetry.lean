import ZFVP.SetTheory.SymmetricSystems

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem hereditarilySymmetric_iff (P Γ F τ : V) : IsHereditarilySymmetricName P Γ F τ ↔
    IsSymmetricName P Γ F τ ∧
      ∀ σ : V, ∀ p : V, ⟨σ, p⟩ₖ ∈ τ → IsHereditarilySymmetricName P Γ F σ := by
  constructor
  · intro hτ
    exact ⟨hereditarilySymmetric_symmetric hτ,
      fun σ p hp ↦ hereditarilySymmetric_mem_closure hτ (subname_mem_nameClosure hp)⟩
  · rintro ⟨hτ, hc⟩
    let X : V := {σ ∈ nameClosure τ ; σ = τ ∨ IsHereditarilySymmetricName P Γ F σ}
    have hτX : τ ∈ X := mem_sep_iff.mpr ⟨mem_nameClosure_self τ, Or.inl rfl⟩
    have hX : IsSubnameClosed X := by
      intro σ hσ υ hυ
      obtain ⟨hσC, hσH⟩ := mem_sep_iff.mp hσ
      obtain ⟨p, hp⟩ := mem_domain_iff.mp hυ
      refine mem_sep_iff.mpr ⟨nameClosure_closed τ σ hσC υ (mem_domain_of_kpair_mem hp), Or.inr ?_⟩
      rcases hσH with rfl | hσH
      · exact hc υ p hp
      · exact hereditarilySymmetric_mem_closure hσH (subname_mem_nameClosure hp)
    refine ⟨hτ.1, fun σ hσ ↦ ?_⟩
    rcases (mem_sep_iff.mp (nameClosure_minimal hX hτX σ hσ)).2 with rfl | hσH
    · exact hτ.2
    · exact (hereditarilySymmetric_symmetric hσH).2

theorem nameStabilizer_checkName {P R Γ one : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hone : IsForcingTop P R one) (x : V) :
    nameStabilizer Γ (checkName one x) = Γ := by
  apply SetTheory.mem_ext_iff.mpr
  intro π
  simp only [nameStabilizer, mem_sep_iff]
  exact ⟨And.left, fun hπ ↦ ⟨hπ, nameAction_checkName hone.1 (forcingAutomorphism_top hR hone (hΓ.1 π hπ)) x⟩⟩

theorem hereditarilySymmetric_checkName {P R Γ F one : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hone : IsForcingTop P R one) (x : V) : IsHereditarilySymmetricName P Γ F (checkName one x) := by
  apply set_induction (fun x ↦ IsHereditarilySymmetricName P Γ F (checkName one x)) (by definability) ?_ x
  intro x ih
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨checkName_isName hone.1 x, ?_⟩, ?_⟩
  · rw [nameStabilizer_checkName hR hΓ hone]
    exact hF.2.1
  · intro σ p hp
    obtain ⟨y, hy, he⟩ := (mem_checkName_iff one x _).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ih y hy

theorem nameStabilizer_pair_contains_inter {P R Γ σ τ one : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hone : IsForcingTop P R one)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) :
    nameStabilizer Γ σ ∩ nameStabilizer Γ τ ⊆ nameStabilizer Γ ({⟨σ, one⟩ₖ, ⟨τ, one⟩ₖ} : V) := by
  intro π hπ
  obtain ⟨hπσ, hπτ⟩ := mem_inter_iff.mp hπ
  obtain ⟨hπΓ, hσfix⟩ := mem_sep_iff.mp hπσ
  have hτfix := (mem_sep_iff.mp hπτ).2
  refine mem_sep_iff.mpr ⟨hπΓ, ?_⟩
  rw [nameAction_pair hσ hτ hone.1, hσfix, hτfix, forcingAutomorphism_top hR hone (hΓ.1 π hπΓ)]

theorem hereditarilySymmetric_pair {P R Γ F σ τ one : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hone : IsForcingTop P R one) (hσ : IsHereditarilySymmetricName P Γ F σ)
    (hτ : IsHereditarilySymmetricName P Γ F τ) :
    IsHereditarilySymmetricName P Γ F ({⟨σ, one⟩ₖ, ⟨τ, one⟩ₖ} : V) := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  have hname := forcingName_pair hσ.1 hτ.1 hone.1
  refine ⟨⟨hname, ?_⟩, ?_⟩
  · exact hF.2.2.1 _
      (hF.2.2.2.1 _ (hereditarilySymmetric_symmetric hσ).2 _ (hereditarilySymmetric_symmetric hτ).2)
      _ (nameStabilizer_subgroup hΓ hname) (nameStabilizer_pair_contains_inter hR hΓ hone hσ.1 hτ.1)
  · intro υ p hp
    rcases show (υ = σ ∧ p = one) ∨ (υ = τ ∧ p = one) from by simpa only [mem_insert, mem_singleton_iff, kpair_iff] using hp with h | h
    · exact h.1 ▸ hσ
    · exact h.1 ▸ hτ

end ZFVP
