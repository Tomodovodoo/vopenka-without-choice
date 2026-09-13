import ZFVP.SetTheory.GroundUniquenessCoding
import ZFVP.SetTheory.GroundUniquenessFormulas

/-! A parameter-free defining formula for the `GroundLike` structure.

The closure clauses of `ZFVP.GroundLike` name the noncomputable operations `imageSet`,
`inducedImageRelation`, `membershipRelation`, `mostowskiMap` and `decodeSet`. Here each clause is
restated as "every set with the defining property of that operation lies in `M`", which mentions
only membership, so the whole predicate becomes a first-order formula with no parameters from the
model. `isGroundLike_iff` shows the restatement is the structure, and `eval_groundLikeFormula`
reads the structure off the formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `R` is well founded on the internal subsets of `D`. -/
def isInternallyWellFoundedFormula : SetTheorySemisentence 2 :=
  f“R D. ∀ A, A ⊆ D → !isNonempty A → ∃ x ∈ A, ∀ y ∈ A, !kpair.dfn y x ∉ R”

/-- `M` looks like a rank stage of a ground model for `d` and `t`. -/
def groundLikeFormula : SetTheorySemisentence 3 :=
  f“M d t. (∀ x ∈ M, x ⊆ M) ∧ !interClosedFormula M ∧ !hasSmallCoverFormula M d t ∧
    !hasApproximationFormula M d t ∧
    (∀ A, A ⊆ t → !CardLE.dfn A d → ∃ C ∈ M, A ⊆ C ∧ C ⊆ t ∧ !mBoundedFormula M d C) ∧
    (∀ g ∈ M, ∀ B ∈ M, ∀ I, (∀ z, z ∈ I ↔ ∃ b ∈ B, !kpair.dfn b z ∈ g) → I ∈ M) ∧
    (∀ g ∈ M, ∀ B ∈ M, ∀ I, (∀ z, z ∈ I ↔ ∃ b ∈ B, !kpair.dfn b z ∈ g) →
      ∀ W, (∀ q, q ∈ W ↔ (q ∈ !prod.dfn I I ∧ ∃ b ∈ B, ∃ c ∈ B, b ∈ c ∧
        q = !kpair.dfn (!value.dfn g b) (!value.dfn g c))) → W ∈ M) ∧
    (∀ B ∈ M, ∀ W, (∀ q, q ∈ W ↔ (q ∈ !prod.dfn B B ∧ ∃ x ∈ B, ∃ y ∈ B, x ∈ y ∧
      q = !kpair.dfn x y)) → W ∈ M) ∧
    (∀ R ∈ M, ∀ D ∈ M, !isInternallyWellFoundedFormula R D → !isExtensionalOnFormula R D →
      ∀ C h, !isTransitiveCollapseFormula R D C h → h ∈ M) ∧
    (∀ B ∈ M, ∀ u ∈ M, ∀ w ∈ M, ∀ T ∈ M, ∀ Y,
      (∀ b, b ∈ Y ↔ (b ∈ B ∧ ∃ s ∈ T, !value.dfn u s = !value.dfn w b)) → Y ∈ M)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isInternallyWellFoundedFormula_defined :
    ℒₛₑₜ-relation[V] IsInternallyWellFounded via isInternallyWellFoundedFormula :=
  ⟨fun v ↦ by simp [isInternallyWellFoundedFormula, IsInternallyWellFounded, isNonempty_def]⟩

/-! ### The defining properties of the five operations -/

/-- Membership in `imageSet g B` read off the graph of `g`, with no hypothesis on `g`. -/
theorem mem_imageSet_iff_kpair (g B z : V) : z ∈ imageSet g B ↔ ∃ b ∈ B, ⟨b, z⟩ₖ ∈ g := by
  rw [imageSet, mem_range_iff]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hbg, hbB⟩ := kpair_mem_restrict_iff.mp hb
    exact ⟨b, hbB, hbg⟩
  · rintro ⟨b, hbB, hbg⟩
    exact ⟨b, kpair_mem_restrict_iff.mpr ⟨hbg, hbB⟩⟩

/-- Membership in `inducedImageRelation g B`, unfolding the separation. -/
theorem mem_inducedImageRelation_iff (g B q : V) :
    q ∈ inducedImageRelation g B ↔
      q ∈ imageSet g B ×ˢ imageSet g B ∧
        ∃ b ∈ B, ∃ c ∈ B, b ∈ c ∧ q = ⟨g ‘ b, g ‘ c⟩ₖ := mem_sep_iff

/-- Membership in `membershipRelation B`, with the pair spelled out. -/
theorem mem_membershipRelation_iff (B q : V) :
    q ∈ membershipRelation B ↔
      q ∈ B ×ˢ B ∧ ∃ x ∈ B, ∃ y ∈ B, x ∈ y ∧ q = ⟨x, y⟩ₖ := by
  constructor
  · intro hq
    have hprod : q ∈ B ×ˢ B := (mem_sep_iff.mp hq).1
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hprod
    exact ⟨hprod, x, hx, y, hy, ((pair_mem_membershipRelation B x y).mp hq).2.2, rfl⟩
  · rintro ⟨-, x, hx, y, hy, hxy, rfl⟩
    exact (pair_mem_membershipRelation B x y).mpr ⟨hx, hy, hxy⟩

/-! ### The flat restatement -/

/-- The `GroundLike` conditions with every closure clause phrased through the defining property of
the operation it uses, so that no noncomputable operation is named. -/
def IsGroundLike (M δ θ : V) : Prop :=
  (∀ x ∈ M, x ⊆ M) ∧
  InterClosed M ∧
  HasSmallCover M δ θ ∧
  HasApproximation M δ θ ∧
  (∀ A, A ⊆ θ → A ≤# δ → ∃ C ∈ M, A ⊆ C ∧ C ⊆ θ ∧ MBounded M δ C) ∧
  (∀ g ∈ M, ∀ B ∈ M, ∀ I : V, (∀ z : V, z ∈ I ↔ ∃ b ∈ B, ⟨b, z⟩ₖ ∈ g) → I ∈ M) ∧
  (∀ g ∈ M, ∀ B ∈ M, ∀ I : V, (∀ z : V, z ∈ I ↔ ∃ b ∈ B, ⟨b, z⟩ₖ ∈ g) →
    ∀ W : V, (∀ q : V, q ∈ W ↔ (q ∈ I ×ˢ I ∧ ∃ b ∈ B, ∃ c ∈ B, b ∈ c ∧ q = ⟨g ‘ b, g ‘ c⟩ₖ)) →
      W ∈ M) ∧
  (∀ B ∈ M, ∀ W : V, (∀ q : V, q ∈ W ↔ (q ∈ B ×ˢ B ∧ ∃ x ∈ B, ∃ y ∈ B, x ∈ y ∧ q = ⟨x, y⟩ₖ)) →
    W ∈ M) ∧
  (∀ R ∈ M, ∀ D ∈ M, IsInternallyWellFounded R D → IsExtensionalOn R D →
    ∀ C f : V, IsTransitiveCollapse R D C f → f ∈ M) ∧
  (∀ B ∈ M, ∀ f ∈ M, ∀ f' ∈ M, ∀ T ∈ M, ∀ Y : V,
    (∀ b : V, b ∈ Y ↔ (b ∈ B ∧ ∃ t ∈ T, f ‘ t = f' ‘ b)) → Y ∈ M)

theorem isGroundLike_iff (M δ θ : V) : IsGroundLike M δ θ ↔ GroundLike M δ θ := by
  constructor
  · rintro ⟨htr, hint, hcov, happ, hbc, himg, hind, hmem, hcol, hdec⟩
    refine ⟨htr, hint, hcov, happ, hbc, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg B hB
      exact himg g hg B hB _ (mem_imageSet_iff_kpair g B)
    · intro g hg B hB
      exact hind g hg B hB _ (mem_imageSet_iff_kpair g B) _ (mem_inducedImageRelation_iff g B)
    · intro B hB
      exact hmem B hB _ (mem_membershipRelation_iff B)
    · intro R hR D hD hwf hext
      exact hcol R hR D hD hwf hext _ _ (mostowskiMap_isTransitiveCollapse hwf hext)
    · intro B hB f hf f' hf' T hT
      exact hdec B hB f hf f' hf' T hT _ (mem_decodeSet_iff B f f' T)
  · intro h
    refine ⟨h.transitive, h.inter, h.cover, h.approx, h.boundedCover, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg B hB I hI
      have : I = imageSet g B := mem_ext fun z ↦ (hI z).trans (mem_imageSet_iff_kpair g B z).symm
      exact this ▸ h.image g hg B hB
    · intro g hg B hB I hI W hW
      have hIeq : I = imageSet g B :=
        mem_ext fun z ↦ (hI z).trans (mem_imageSet_iff_kpair g B z).symm
      subst hIeq
      have : W = inducedImageRelation g B :=
        mem_ext fun q ↦ (hW q).trans (mem_inducedImageRelation_iff g B q).symm
      exact this ▸ h.inducedRelation g hg B hB
    · intro B hB W hW
      have : W = membershipRelation B :=
        mem_ext fun q ↦ (hW q).trans (mem_membershipRelation_iff B q).symm
      exact this ▸ h.membershipRelation_mem B hB
    · intro R hR D hD hwf hext C f hf
      have hfeq : f = mostowskiMap R D := by
        rw [(transitiveCollapse_unique hwf hf).1, mostowskiMap_of_wellFounded hwf]
      exact hfeq ▸ h.collapse R hR D hD hwf hext
    · intro B hB f hf f' hf' T hT Y hY
      have : Y = decodeSet B f f' T :=
        mem_ext fun b ↦ (hY b).trans (mem_decodeSet_iff B f f' T b).symm
      exact this ▸ h.decode B hB f hf f' hf' T hT

instance groundLikeFormula_defined : ℒₛₑₜ-relation₃[V] IsGroundLike via groundLikeFormula :=
  ⟨fun v ↦ by
    simp [groundLikeFormula, IsGroundLike, CardLE, MBounded, InterClosed, HasSmallCover,
      HasApproximation, USmall, MSmall, IsInternallyWellFounded, IsExtensionalOn,
      IsTransitiveCollapse, isNonempty_def]⟩

theorem eval_groundLikeFormula (M δ θ : V) :
    groundLikeFormula.Evalb ![M, δ, θ] ↔ GroundLike M δ θ := by
  have h := (groundLikeFormula_defined (V := V)).iff ![M, δ, θ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  exact isGroundLike_iff M δ θ

end ZFVP
