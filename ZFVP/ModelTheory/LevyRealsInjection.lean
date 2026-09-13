import ZFVP.ModelTheory.LevyOrdinalLocalization
import ZFVP.ModelTheory.StageCountability
import ZFVP.ModelTheory.LevyCollapseOmegaOne
import ZFVP.SetTheory.Hartogs

/-! No injection of `κ̌` into the reals of the Levy extension has a code that lies in a bounded
stage: the reals of a stage are countable in `V[G]` while `κ̌` is its first uncountable ordinal.
Hence no such injection is definable from ground sets, reals and ordinals. This is the source of
the failure of choice in the Solovay model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The code of a function into the reals: the pairs `(α, q)` with `q ∈ f(α)`. -/
noncomputable def realsCode {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (D f : W) : W :=
  {q ∈ D ; kpair.π₂ q ∈ f ‘ (kpair.π₁ q)}

theorem mem_realsCode_iff {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (D f q : W) :
    q ∈ realsCode D f ↔ q ∈ D ∧ kpair.π₂ q ∈ f ‘ (kpair.π₁ q) :=
  mem_sep_iff

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

theorem realsCode_subset (f : (levyContext κ hG).Model) :
    realsCode ((levyContext κ hG).check (κ ×ˢ ((ω : V) ×ˢ ((2 : ℕ) : V)))) f ⊆
      (levyContext κ hG).check (κ ×ˢ ((ω : V) ×ˢ ((2 : ℕ) : V))) :=
  sep_subset

include hAC hU hc hω hκ in
/-- An injection of `κ̌` into the reals has no code in a bounded stage. -/
theorem no_injection_of_localized_code {f : (levyContext κ hG).Model}
    (hf : f ∈ (cantorSpace (levyContext κ hG).Model) ^ (levyContext κ hG).check κ) (hinj : Injective f)
    (hloc : IsLocalized hG (realsCode ((levyContext κ hG).check (κ ×ˢ ((ω : V) ×ˢ ((2 : ℕ) : V)))) f)) :
    False := by
  obtain ⟨ξ, hξ, C', hC'⟩ := hloc
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  let W := levyContext κ hG
  let N := levySubContext ξ hξ' hG
  let L := levySubRealization ξ hξ' hG
  let j := L.embedding
  let D : V := κ ×ˢ ((ω : V) ×ˢ ((2 : ℕ) : V))
  have hff : IsFunction f := IsFunction.of_mem hf
  have hfd : domain f = W.check κ := domain_eq_of_mem_function hf
  have hjcheck : ∀ a : V, j (N.check a) = W.check a := fun a ↦ L.value_check a
  have h2 : j ((2 : ℕ) : N.Model) = ((2 : ℕ) : W.Model) := j.map_numeral 2
  have hωj : j (ω : N.Model) = (ω : W.Model) := j.map_omega
  -- every value of `f` is a real of the stage
  have hvals : ∀ β ∈ κ, f ‘ (W.check β) ∈ L.value (cantorSpace N.Model) := by
    intro β hβ
    have hβκ : W.check β ∈ W.check κ := (W.check_mem_iff _ _).mpr hβ
    have hfβ : f ‘ (W.check β) ∈ cantorSpace W.Model := function_value_mem hf hβκ
    have hfβsub : f ‘ (W.check β) ⊆ W.check ((ω : V) ×ˢ ((2 : ℕ) : V)) := by
      have h := subset_prod_of_mem_function ((mem_cantorSpace_iff _).mp hfβ)
      have hprod : W.check ((ω : V) ×ˢ ((2 : ℕ) : V)) = (ω : W.Model) ×ˢ ((2 : ℕ) : W.Model) := by
        have h := W.checkEmbedding.map_prod (ω : V) ((2 : ℕ) : V)
        change W.check _ = W.check _ ×ˢ W.check _ at h
        have h2 : W.check ((2 : ℕ) : V) = ((2 : ℕ) : W.Model) := W.checkEmbedding.map_numeral 2
        rw [h, W.check_omega_eq, h2]
      rw [hprod]
      exact h
    -- the value is the image of a separation in the stage
    let s : N.Model := {q ∈ N.check ((ω : V) ×ˢ ((2 : ℕ) : V)) ; ⟨N.check β, q⟩ₖ ∈ C'}
    have hmemC : ∀ q, ⟨N.check β, q⟩ₖ ∈ C' ↔ ⟨W.check β, j q⟩ₖ ∈ realsCode (W.check D) f := by
      intro q
      have hk : j ⟨N.check β, q⟩ₖ = ⟨W.check β, j q⟩ₖ := by rw [j.map_kpair, hjcheck]
      rw [← hC', ← hk]
      exact (j.mem_iff _ _).symm
    have hQ : ∀ a S : W.Model, ℒₛₑₜ-predicate (fun q ↦ ⟨a, q⟩ₖ ∈ S) := fun a S ↦ by definability
    have hQ' : ∀ a S : N.Model, ℒₛₑₜ-predicate (fun q ↦ ⟨a, q⟩ₖ ∈ S) := fun a S ↦ by definability
    have hs : j s = f ‘ (W.check β) := by
      have hsep := j.map_separation (N.check ((ω : V) ×ˢ ((2 : ℕ) : V)))
        (fun q ↦ ⟨N.check β, q⟩ₖ ∈ C') (fun q ↦ ⟨W.check β, q⟩ₖ ∈ realsCode (W.check D) f)
        (hQ' _ _) (hQ _ _) (fun q _ ↦ hmemC q)
      change j s = _ at hsep
      rw [hsep, hjcheck]
      apply mem_ext
      intro q
      rw [mem_sep_iff, mem_realsCode_iff, kpair.π₁_kpair, kpair.π₂_kpair]
      constructor
      · rintro ⟨-, -, hq⟩
        exact hq
      · intro hq
        have hqD : ⟨W.check β, q⟩ₖ ∈ W.check D := by
          have hD : W.check D = W.check κ ×ˢ W.check ((ω : V) ×ˢ ((2 : ℕ) : V)) := by
            have h := W.checkEmbedding.map_prod κ ((ω : V) ×ˢ ((2 : ℕ) : V))
            exact h
          rw [hD]
          exact kpair_mem_iff.mpr ⟨hβκ, hfβsub q hq⟩
        exact ⟨hfβsub q hq, hqD, hq⟩
    have hsN : s ∈ cantorSpace N.Model := by
      rw [mem_cantorSpace_iff]
      apply (j.function_iff s (ω : N.Model) ((2 : ℕ) : N.Model)).mp
      rw [hs, h2, hωj]
      exact (mem_cantorSpace_iff _).mp hfβ
    rw [← hs]
    exact (j.mem_iff _ _).mpr hsN
  have hrange : range f ⊆ L.value (cantorSpace N.Model) := by
    intro r hr
    obtain ⟨α, hαr⟩ := mem_range_iff.mp hr
    obtain ⟨α', hα, r', -, he⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf _ hαr)
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    obtain ⟨β, hβ, rfl⟩ := (W.mem_check_iff _ _).mp hα
    rw [← value_eq_of_kpair_mem hαr]
    exact hvals β hβ
  have hcount : range f ≤# (ω : W.Model) :=
    (cardLE_of_subset hrange).trans (stage_reals_countable hAC hU hc hω hκ hG ξ hξ)
  have hfr : f ∈ (range f) ^ W.check κ := by
    rw [mem_function_iff]
    refine ⟨fun q hq ↦ ?_, (mem_function_iff.mp hf).2⟩
    obtain ⟨a, ha, b, -, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf q hq)
    exact kpair_mem_iff.mpr ⟨ha, mem_range_of_kpair_mem hq⟩
  have h1 : W.check κ ≤# range f := ⟨f, hfr, hinj⟩
  have hκω : W.check κ ≤# (ω : W.Model) := h1.trans hcount
  rw [← levy_check_hartogs hAC hU hc hω hκ hG] at hκω
  exact not_hartogsNumber_cardLE _ hκω

include hAC hU hc hω hκ in
/-- No injection of `κ̌` into the reals has a code definable from ground sets, reals and ordinals. -/
theorem no_groundRealDefinable_injection {f : (levyContext κ hG).Model}
    (hf : f ∈ (cantorSpace (levyContext κ hG).Model) ^ (levyContext κ hG).check κ) (hinj : Injective f)
    (hdef : (levyContext κ hG).IsGroundRealDefinable
      (realsCode ((levyContext κ hG).check (κ ×ˢ ((ω : V) ×ˢ ((2 : ℕ) : V)))) f)) : False :=
  no_injection_of_localized_code hAC hU hc hω hκ hG hf hinj
    (groundRealDefinable_subset_check_localized hAC hU hc hω hκ hG (realsCode_subset hG f) hdef)

end

end ZFVP
