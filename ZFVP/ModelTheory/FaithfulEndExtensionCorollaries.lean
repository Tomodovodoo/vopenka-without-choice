import ZFVP.ModelTheory.FaithfulEndExtensionTheorem

/-! The topped clause of Enayat Theorem 4.4(a) and Proposition 5.4. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace MembershipEndExtension

/-- If the elementary stage inclusion is onto, every ordinal below its height is old.
Together with newness of the height this is the topped case. -/
theorem old_below_surjective_stage {j : MembershipEndExtension V W} {γ : W}
    [IsOrdinal γ] (e : ElementaryMap V (SetDomain (hierarchy γ)))
    (he : ∀ x : V, (e x).val = j x) (hs : Function.Surjective e.toFun) :
    ∀ ξ ∈ γ, ∃ x : V, j x = ξ := by
  intro ξ hξ
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξstage : ξ ∈ hierarchy γ := ordinal_mem_hierarchy_iff.mpr hξ
  obtain ⟨x, hx⟩ := hs ⟨ξ, hξstage⟩
  exact ⟨x, (he x).symm.trans (congrArg Subtype.val hx)⟩

theorem IsFaithful.topped_of_surjective_stage {j : MembershipEndExtension V W}
    (hf : j.IsFaithful) {γ : W} [IsOrdinal γ] (hn : ∀ x : V, j x ≠ γ)
    (e : ElementaryMap V (SetDomain (hierarchy γ)))
    (he : ∀ x : V, (e x).val = j x) (hs : Function.Surjective e.toFun) :
    j.IsRankExtension ∧ (∀ x : V, j x ≠ γ) ∧ (∀ ξ ∈ γ, ∃ x : V, j x = ξ) ∧
      ∀ ξ : W, IsOrdinal ξ → (∀ x : V, j x ≠ ξ) → γ ⊆ ξ := by
  have hold := old_below_surjective_stage e he hs
  refine ⟨hf.isRankExtension, hn, hold, ?_⟩
  intro ξ hξ hnew
  have : IsOrdinal ξ := hξ
  rcases IsOrdinal.mem_trichotomy γ ξ with hlt | heq | hgt
  · exact IsOrdinal.toIsTransitive.transitive γ hlt
  · exact heq ▸ subset_refl γ
  · obtain ⟨x, hx⟩ := hold ξ hgt
    exact False.elim (hnew x hx)

/-- The full stated dichotomy: a topped rank extension with least new ordinal,
or a proper elementary inclusion in a rank stage. -/
theorem IsFaithful.topped_or_proper_elementaryStage {j : MembershipEndExtension V W}
    (hf : j.IsFaithful) (hp : j.IsProper) :
    j.IsRankExtension ∧ ∃ γ : W, IsOrdinal γ ∧ (∀ x : V, j x ≠ γ) ∧
      ∃ e : ElementaryMap V (SetDomain (hierarchy γ)), (∀ x : V, (e x).val = j x) ∧
        ((Function.Surjective e.toFun ∧ (∀ ξ ∈ γ, ∃ x : V, j x = ξ) ∧
            ∀ ξ : W, IsOrdinal ξ → (∀ x : V, j x ≠ ξ) → γ ⊆ ξ) ∨
          ∃ y : SetDomain (hierarchy γ), ∀ x : V, e x ≠ y) := by
  obtain ⟨γ, hγ, hn, e, he, hs | hp'⟩ := hf.elementaryStage_dichotomy hp
  · have : IsOrdinal γ := hγ
    have ht := hf.topped_of_surjective_stage hn e he hs
    exact ⟨hf.isRankExtension, γ, hγ, hn, e, he, Or.inl ⟨hs, ht.2.2⟩⟩
  · exact ⟨hf.isRankExtension, γ, hγ, hn, e, he, Or.inr hp'⟩

end MembershipEndExtension

/-- Enayat Proposition 5.4, for arbitrary source and target universes. -/
theorem IsRatherClassless.no_proper_rank_extension (hV : IsRatherClassless V)
    (j : MembershipEndExtension V W) (hr : j.IsRankExtension) : ¬ j.IsProper := by
  intro hp
  have hc := hV.isConservative_of_isPowersetPreserving hr.isPowersetPreserving
  obtain ⟨δ, hδ, hn⟩ := hc.exists_new_ordinal hp
  have : IsOrdinal δ := hδ
  exact MembershipEndExtension.false_of_new_ordinal hc δ hn

end ZFVP


