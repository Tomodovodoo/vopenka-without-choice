import ZFVP.ModelTheory.LevyStageGeneralCover
import ZFVP.SetTheory.GroundUniquenessCoding
import ZFVP.SetTheory.ClosedRankStages
import ZFVP.SetTheory.EndExtensionCollapseDescent
import ZFVP.SetTheory.EndExtensionSets
import ZFVP.SetTheory.FiniteCodingClosure
import ZFVP.SetTheory.CodingUniverse

/-! The check of a ground model rank stage is ground-like in the Levy extension.

`GroundLike M δ θ` collects the hypotheses of Laver's uniqueness lemma: transitivity, closure
under intersections, the cover and approximation properties for subsets of `θ`, the bounded cover
property, and closure under the four operations of the coding argument (images, transported
membership, membership relations, Mostowski collapses, and reading a subset off two collapses).

For a limit ordinal `lam` closed under successor and under `β ↦ hartogsNumber (hierarchy β)`, the
check of `hierarchy lam` in the Levy extension of a measurable `κ` satisfies all of them, with
`δ = (κ⁺)ˇ` and any `θ` of the stage. The closure fields come from two ingredients: each of the
coding operations commutes with the check embedding, and each of them lands back inside the stage.

The last theorem is the parameter agreement of the uniqueness lemma: for a ground set `S` whose
power set is in the stage, the members of the checked stage below `Š` are exactly the checked
subsets of `S`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

variable (j : MembershipEndExtension V W)

/-- Images move along a membership end extension. -/
theorem map_imageSet (g B : V) : j (imageSet g B) = imageSet (j g) (j B) := by
  unfold imageSet
  rw [j.map_range, j.map_restrict]

/-- Transported membership moves along a membership end extension. -/
theorem map_inducedImageRelation (g B : V) :
    j (inducedImageRelation g B) = inducedImageRelation (j g) (j B) := by
  have he := j.map_separation (imageSet g B ×ˢ imageSet g B)
    (fun p ↦ ∃ b ∈ B, ∃ b' ∈ B, b ∈ b' ∧ p = ⟨g ‘ b, g ‘ b'⟩ₖ)
    (fun p ↦ ∃ b ∈ j B, ∃ b' ∈ j B, b ∈ b' ∧ p = ⟨(j g) ‘ b, (j g) ‘ b'⟩ₖ)
    inferInstance inferInstance ?_
  · unfold inducedImageRelation
    rw [he, j.map_prod, j.map_imageSet]
  · intro p _
    constructor
    · rintro ⟨b, hb, b', hb', hbb', rfl⟩
      exact ⟨j b, (j.mem_iff _ _).mpr hb, j b', (j.mem_iff _ _).mpr hb',
        (j.mem_iff _ _).mpr hbb', by rw [j.map_kpair, j.map_value_total, j.map_value_total]⟩
    · rintro ⟨b, hb, b', hb', hbb', heq⟩
      obtain ⟨b₀, hb₀, rfl⟩ := j.endExtension B b hb
      obtain ⟨b₀', hb₀', rfl⟩ := j.endExtension B b' hb'
      refine ⟨b₀, hb₀, b₀', hb₀', (j.mem_iff _ _).mp hbb', j.injective ?_⟩
      rw [heq, j.map_kpair, j.map_value_total, j.map_value_total]

/-- Reading a subset off two collapses moves along a membership end extension. -/
theorem map_decodeSet (B f f' T : V) :
    j (decodeSet B f f' T) = decodeSet (j B) (j f) (j f') (j T) := by
  have he := j.map_separation B
    (fun b ↦ ∃ t ∈ T, f ‘ t = f' ‘ b)
    (fun b ↦ ∃ t ∈ j T, (j f) ‘ t = (j f') ‘ b)
    inferInstance inferInstance ?_
  · unfold decodeSet
    rw [he]
  · intro b _
    constructor
    · rintro ⟨t, ht, heq⟩
      exact ⟨j t, (j.mem_iff _ _).mpr ht,
        by rw [← j.map_value_total, ← j.map_value_total, heq]⟩
    · rintro ⟨t, ht, heq⟩
      obtain ⟨t₀, ht₀, rfl⟩ := j.endExtension T t ht
      exact ⟨t₀, ht₀, j.injective (by rw [j.map_value_total, j.map_value_total]; exact heq)⟩

end MembershipEndExtension

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section RankBounds

variable {lam : V} [IsOrdinal lam]

/-- The image of a set under `g` sits inside the double union of `g`. -/
theorem imageSet_subset_sUnion_sUnion (g B : V) : imageSet g B ⊆ ⋃ˢ ⋃ˢ g := by
  intro z hz
  obtain ⟨x, hx⟩ := mem_range_iff.mp hz
  exact mem_sUnion_sUnion_of_kpair_mem_right (restrict_subset g B _ hx)

/-- A rank stage closed under successor is closed under images. -/
theorem imageSet_mem_hierarchy (hlim : ∀ β ∈ lam, succ β ∈ lam) {g B : V}
    (hg : g ∈ hierarchy lam) (hB : B ∈ hierarchy lam) : imageSet g B ∈ hierarchy lam :=
  subset_mem_hierarchy_limit hlim
    (sUnion_mem_hierarchy_limit hlim (sUnion_mem_hierarchy_limit hlim hg))
    (imageSet_subset_sUnion_sUnion g B)

/-- A rank stage closed under successor is closed under transported membership. -/
theorem inducedImageRelation_mem_hierarchy (hlim : ∀ β ∈ lam, succ β ∈ lam) {g B : V}
    (hg : g ∈ hierarchy lam) (hB : B ∈ hierarchy lam) :
    inducedImageRelation g B ∈ hierarchy lam :=
  subset_mem_hierarchy_limit hlim
    (prod_mem_hierarchy_limit hlim (imageSet_mem_hierarchy hlim hg hB)
      (imageSet_mem_hierarchy hlim hg hB))
    (inducedImageRelation_subset g B)

/-- A rank stage closed under successor contains the membership relation of each of its
members. -/
theorem membershipRelation_mem_hierarchy (hlim : ∀ β ∈ lam, succ β ∈ lam) {B : V}
    (hB : B ∈ hierarchy lam) : membershipRelation B ∈ hierarchy lam :=
  subset_mem_hierarchy_limit hlim (prod_mem_hierarchy_limit hlim hB hB)
    (fun _ hp ↦ (mem_sep_iff.mp hp).1)

/-- A decoded subset lies in any rank stage holding the set it is carved out of. -/
theorem decodeSet_mem_hierarchy {B f f' T : V} (hB : B ∈ hierarchy lam) :
    decodeSet B f f' T ∈ hierarchy lam :=
  mem_hierarchy_of_subset' hB (fun _ hb ↦ (mem_decodeSet_iff B f f' T _).mp hb |>.1)

end RankBounds

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  {θ lam : V} [IsOrdinal lam]

/-- The check of an image is the image of the checks. -/
theorem check_imageSet (g B : V) :
    (levyContext κ hG).check (imageSet g B) =
      imageSet ((levyContext κ hG).check g) ((levyContext κ hG).check B) :=
  (levyContext κ hG).checkEmbedding.map_imageSet g B

/-- The check of a transported membership relation is the transported membership relation of the
checks. -/
theorem check_inducedImageRelation (g B : V) :
    (levyContext κ hG).check (inducedImageRelation g B) =
      inducedImageRelation ((levyContext κ hG).check g) ((levyContext κ hG).check B) :=
  (levyContext κ hG).checkEmbedding.map_inducedImageRelation g B

/-- The check of a decoded subset is the decoded subset of the checks. -/
theorem check_decodeSet (B f f' T : V) :
    (levyContext κ hG).check (decodeSet B f f' T) =
      decodeSet ((levyContext κ hG).check B) ((levyContext κ hG).check f)
        ((levyContext κ hG).check f') ((levyContext κ hG).check T) :=
  (levyContext κ hG).checkEmbedding.map_decodeSet B f f' T

include hAC hU hc hω hκ in
/-- The check of a rank stage closed under successor and under the Hartogs numbers of the earlier
stages is ground-like in the Levy extension, with `δ = (κ⁺)ˇ` and any `θ` of the stage. -/
theorem levy_stage_groundLike (hlim : ∀ β ∈ lam, succ β ∈ lam)
    (hclosed : ∀ β ∈ lam, hartogsNumber (hierarchy β) ∈ lam)
    (hθ : θ ∈ hierarchy lam) (hHlam : hartogsNumber κ ∈ lam) (hκlam : κ ∈ lam) :
    GroundLike ((levyContext κ hG).check (hierarchy lam))
      ((levyContext κ hG).check (hartogsNumber κ)) ((levyContext κ hG).check θ) := by
  have hθM : (levyContext κ hG).check θ ∈ (levyContext κ hG).check (hierarchy lam) :=
    ((levyContext κ hG).check_mem_iff _ _).mpr hθ
  refine
    { transitive := (levy_stage_transitive (κ := κ) (hG := hG) (lam := lam)).transitive
      inter := levy_stage_interClosed hG
      cover := levy_stage_hasSmallCover_of_mem hAC hU hc hω hκ hG hlim hθ hκlam
      approx := levy_stage_hasApproximation_of_mem hAC hU hc hω hκ hG hlim hθ hκlam
      boundedCover := ?_
      image := ?_
      inducedRelation := ?_
      membershipRelation_mem := ?_
      collapse := ?_
      decode := ?_ }
  · -- bounded cover: cut the bounding set down to `θ̌`
    intro A hAθ hcard
    obtain ⟨C, hCM, hAC', f, hfM, hf, hinj⟩ :=
      levy_stage_boundedCover hAC hU hc hω hκ hG hlim hθ hHlam hAθ hcard
    refine ⟨C ∩ (levyContext κ hG).check θ, levy_stage_interClosed hG C hCM _ hθM,
      fun x hx ↦ mem_inter_iff.mpr ⟨hAC' x hx, hAθ x hx⟩,
      fun x hx ↦ (mem_inter_iff.mp hx).2, ?_⟩
    exact ⟨C, hCM, fun x hx ↦ (mem_inter_iff.mp hx).1, f, hfM, hf, hinj⟩
  · -- images
    intro g hg B hB
    obtain ⟨g₀, hg₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hg
    obtain ⟨B₀, hB₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hB
    rw [← check_imageSet]
    exact ((levyContext κ hG).check_mem_iff _ _).mpr (imageSet_mem_hierarchy hlim hg₀ hB₀)
  · -- transported membership
    intro g hg B hB
    obtain ⟨g₀, hg₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hg
    obtain ⟨B₀, hB₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hB
    rw [← check_inducedImageRelation]
    exact ((levyContext κ hG).check_mem_iff _ _).mpr
      (inducedImageRelation_mem_hierarchy hlim hg₀ hB₀)
  · -- membership relations
    intro B hB
    obtain ⟨B₀, hB₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hB
    have hmr : membershipRelation ((levyContext κ hG).check B₀)
        = (levyContext κ hG).check (membershipRelation B₀) :=
      ((levyContext κ hG).checkEmbedding.map_membershipRelation B₀).symm
    rw [hmr]
    exact ((levyContext κ hG).check_mem_iff _ _).mpr (membershipRelation_mem_hierarchy hlim hB₀)
  · -- Mostowski collapses
    intro R hR D hD hwf hext
    obtain ⟨R₀, hR₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hR
    obtain ⟨D₀, hD₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hD
    have hwf₀ : IsInternallyWellFounded R₀ D₀ :=
      (levyContext κ hG).checkEmbedding.isInternallyWellFounded_of_map (R := R₀) (D := D₀) hwf
    have hext₀ : IsExtensionalOn R₀ D₀ :=
      (levyContext κ hG).checkEmbedding.isExtensionalOn_of_map (R := R₀) (D := D₀) hext
    have hmap := ((levyContext κ hG).checkEmbedding.mostowskiMap_map hwf₀ hext₀).symm
    rw [show mostowskiMap ((levyContext κ hG).check R₀) ((levyContext κ hG).check D₀)
      = (levyContext κ hG).check (mostowskiMap R₀ D₀) from hmap]
    exact ((levyContext κ hG).check_mem_iff _ _).mpr
      (collapse_mem_hierarchy hAC hlim hclosed hR₀ hD₀ hwf₀ hext₀)
  · -- decoding
    intro B hB f hf f' hf' T hT
    obtain ⟨B₀, hB₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hB
    obtain ⟨f₀, hf₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hf
    obtain ⟨f₀', hf₀', rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hf'
    obtain ⟨T₀, hT₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hT
    rw [← check_decodeSet]
    exact ((levyContext κ hG).check_mem_iff _ _).mpr (decodeSet_mem_hierarchy hB₀)

/-- Parameter agreement: below the check of a ground set `S` whose power set lies in the stage,
the checked stage and the check of `℘ S` have the same members. -/
theorem check_stage_subset_iff (hlim : ∀ β ∈ lam, succ β ∈ lam) {S : V}
    (hS : ℘ S ∈ hierarchy lam) (X : (levyContext κ hG).Model)
    (hX : X ⊆ (levyContext κ hG).check S) :
    X ∈ (levyContext κ hG).check (hierarchy lam) ↔ X ∈ (levyContext κ hG).check (℘ S) := by
  constructor
  · intro hXM
    obtain ⟨X₀, hX₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hXM
    exact ((levyContext κ hG).check_mem_iff _ _).mpr (mem_power_iff.mpr
      (((levyContext κ hG).checkEmbedding.subset_iff X₀ S).mp hX))
  · intro hXP
    obtain ⟨X₀, hX₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hXP
    exact ((levyContext κ hG).check_mem_iff _ _).mpr
      ((hierarchy_transitive lam).transitive (℘ S) hS X₀ hX₀)

end

end ZFVP
