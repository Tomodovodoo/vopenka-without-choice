import ZFVP.ModelTheory.FaithfulStageCaseTwo
import ZFVP.ModelTheory.FaithfulStageElementarity

/-! Enayat, Theorem 4.4: an actual elementary rank stage and a coded full satisfaction class
for every proper faithful end extension of arbitrary models of ZF. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsFaithful.exists_fullSatisfactionStage {j : MembershipEndExtension V W}
    (hf : j.IsFaithful) (hp : j.IsProper) :
    ∃ γ : W, IsOrdinal γ ∧ (∀ α : V, j α ≠ γ) ∧
      (∀ x : V, j x ∈ hierarchy γ) ∧
      IsFullSatisfactionClass V (stageSatisfaction j γ) := by
  obtain ⟨δ, hδ, hnew⟩ := hf.isPowersetPreserving.exists_new_ordinal hp
  have : IsOrdinal δ := hδ
  obtain ⟨θ, hθ, hδθ, hrefl⟩ := exists_reflectsCaseOne δ
  have : IsOrdinal θ := hθ
  have hex : ∃ γ : W, IsLeastStageDefinableParamNew j δ θ γ := by
    by_contra hn
    exact false_of_faithful_stage_without_least hf hδθ hnew
      (fun γ hγ ↦ hn ⟨γ, hγ⟩)
  obtain ⟨γ, hγ⟩ := hex
  have : IsOrdinal γ := hγ.1
  have hγnew : ∀ α : V, j α ≠ γ := hγ.2.1.2
  have hsub := hf.isPowersetPreserving.map_mem_hierarchy_of_new hγnew
  exact ⟨γ, hγ.1, hγnew, hsub, stageSatisfaction_isFullSatisfactionClass j γ hsub
    (elementary_of_least_of_powersetPreserving hf.isPowersetPreserving hδθ hrefl hγ)⟩

/-- The actual elementary embedding has underlying function exactly the given inclusion into
the rank stage. Surjectivity distinguishes the topped case from a proper elementary extension. -/
theorem IsFaithful.exists_elementaryStage {j : MembershipEndExtension V W}
    (hf : j.IsFaithful) (hp : j.IsProper) :
    ∃ γ : W, IsOrdinal γ ∧ (∀ α : V, j α ≠ γ) ∧
      ∃ e : ElementaryMap V (SetDomain (hierarchy γ)), (∀ x : V, (e x).val = j x) ∧
        IsFullSatisfactionClass V (stageSatisfaction j γ) := by
  obtain ⟨γ, hγ, hn, hs, hS⟩ := hf.exists_fullSatisfactionStage hp
  exact ⟨γ, hγ, hn, elementaryStageMap j γ hs hS, fun _ ↦ rfl, hS⟩

/-- The topped/proper alternatives in Theorem 4.4(a), with the topped alternative
stating that the image is exactly the whole rank stage. -/
theorem IsFaithful.elementaryStage_dichotomy {j : MembershipEndExtension V W}
    (hf : j.IsFaithful) (hp : j.IsProper) :
    ∃ γ : W, IsOrdinal γ ∧ (∀ α : V, j α ≠ γ) ∧
      ∃ e : ElementaryMap V (SetDomain (hierarchy γ)), (∀ x : V, (e x).val = j x) ∧
        (Function.Surjective e.toFun ∨
          ∃ y : SetDomain (hierarchy γ), ∀ x : V, e x ≠ y) := by
  obtain ⟨γ, hγ, hn, e, he, _⟩ := hf.exists_elementaryStage hp
  refine ⟨γ, hγ, hn, e, he, ?_⟩
  by_cases hs : Function.Surjective e.toFun
  · exact Or.inl hs
  · right
    by_contra hn
    exact hs (fun y ↦ by
      by_contra hy
      exact hn ⟨y, fun x hx ↦ hy ⟨x, hx⟩⟩)
def stageTruthPredicate (γ u : W) : Prop :=
  MembershipSatisfies (hierarchy γ) (kpair.π₁ u) (kpair.π₁ (kpair.π₂ u))
    (kpair.π₂ (kpair.π₂ u))

instance stageTruthPredicate_definable : ℒₛₑₜ-relation[W] stageTruthPredicate := by
  unfold stageTruthPredicate
  definability

theorem IsFaithful.exists_codedFullSatisfactionClass {j : MembershipEndExtension V W}
    (hf : j.IsFaithful) (hp : j.IsProper) :
    ∃ D : W → Prop, (ℒₛₑₜ-predicate[W] D) ∧
      IsFullSatisfactionClass V (fun n φ b ↦ D (j ⟨n, ⟨φ, b⟩ₖ⟩ₖ)) := by
  obtain ⟨γ, _, _, _, hS⟩ := hf.exists_fullSatisfactionStage hp
  refine ⟨stageTruthPredicate γ, by definability, ?_⟩
  have he : (fun n φ b : V ↦ stageTruthPredicate γ (j ⟨n, ⟨φ, b⟩ₖ⟩ₖ)) =
      stageSatisfaction j γ := by
    funext n φ b
    simp only [stageTruthPredicate, stageSatisfaction, j.map_kpair, kpair.π₁_kpair, kpair.π₂_kpair]
  rw [he]
  exact hS

end MembershipEndExtension
end ZFVP

