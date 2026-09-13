import ZFVP.SetTheory.GroundUniqueness
import ZFVP.SetTheory.SetCodes
import ZFVP.SetTheory.HartogsBound

/-! Laver's ground-model uniqueness lemma (Reitz, "The ground axiom", Lemma 6.2), steps 2 and 3.

Two sets `M` and `M'` that behave like rank stages of a ground model, agree on subsets of `δ` and
on subsets of `δ ×ˢ δ`, and have the `δ`-cover and `δ`-approximation properties for subsets of an
ordinal `θ`, contain the same subsets of `θ`.

Step 2 codes a set `A ⊆ B` of size at most `δ` by a pair of Mostowski collapses computed inside
`M'`: an injection `g ∈ M` of `B` into `δ` transports membership on `B` to a relation on a subset
of `δ`, and the two collapses agree along `g`, so `A` is recovered from data both models share.
Step 3 removes the size restriction with the approximation property and simultaneous covers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The image of `B` under the function `g`. -/
noncomputable def imageSet (g B : V) : V := range (g ↾ B)

instance imageSet_definable : ℒₛₑₜ-function₂[V] imageSet := by
  unfold imageSet
  definability

theorem mem_imageSet_iff {g B : V} [IsFunction g] (hB : B ⊆ domain g) (z : V) :
    z ∈ imageSet g B ↔ ∃ b ∈ B, g ‘ b = z := by
  rw [imageSet, mem_range_iff]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hbg, hbB⟩ := kpair_mem_restrict_iff.mp hb
    exact ⟨b, hbB, value_eq_of_kpair_mem hbg⟩
  · rintro ⟨b, hbB, rfl⟩
    exact ⟨b, kpair_mem_restrict_iff.mpr ⟨kpair_value_mem (hB b hbB), hbB⟩⟩

instance inducedImagePredicate_definable (g B : V) :
    ℒₛₑₜ-predicate[V] (fun p ↦ ∃ b ∈ B, ∃ b' ∈ B, b ∈ b' ∧ p = ⟨g ‘ b, g ‘ b'⟩ₖ) := by
  definability

/-- Membership on `B` transported to the image of `B` under `g`. -/
noncomputable def inducedImageRelation (g B : V) : V :=
  {p ∈ imageSet g B ×ˢ imageSet g B ; ∃ b ∈ B, ∃ b' ∈ B, b ∈ b' ∧ p = ⟨g ‘ b, g ‘ b'⟩ₖ}

theorem inducedImageRelation_subset (g B : V) :
    inducedImageRelation g B ⊆ imageSet g B ×ˢ imageSet g B := fun _ hp ↦ (mem_sep_iff.mp hp).1

theorem pair_mem_inducedImageRelation (g B u v : V) :
    ⟨u, v⟩ₖ ∈ inducedImageRelation g B ↔
      u ∈ imageSet g B ∧ v ∈ imageSet g B ∧
        ∃ b ∈ B, ∃ b' ∈ B, b ∈ b' ∧ u = g ‘ b ∧ v = g ‘ b' := by
  rw [inducedImageRelation, mem_sep_iff, kpair_mem_iff]
  constructor
  · rintro ⟨⟨hu, hv⟩, b, hb, b', hb', hbb', heq⟩
    obtain ⟨h1, h2⟩ := kpair_inj heq
    exact ⟨hu, hv, b, hb, b', hb', hbb', h1, h2⟩
  · rintro ⟨hu, hv, b, hb, b', hb', hbb', rfl, rfl⟩
    exact ⟨⟨hu, hv⟩, b, hb, b', hb', hbb', rfl⟩

instance decodePredicate_definable (f f' T : V) :
    ℒₛₑₜ-predicate[V] (fun b ↦ ∃ t ∈ T, f ‘ t = f' ‘ b) := by
  definability

/-- The members of `B` whose collapse value under `f'` is a collapse value under `f` of a member
of `T`. -/
noncomputable def decodeSet (B f f' T : V) : V := {b ∈ B ; ∃ t ∈ T, f ‘ t = f' ‘ b}

theorem mem_decodeSet_iff (B f f' T b : V) :
    b ∈ decodeSet B f f' T ↔ b ∈ B ∧ ∃ t ∈ T, f ‘ t = f' ‘ b := mem_sep_iff

/-- Composing two value operations stays definable. -/
instance valueCompEq_definable (f f' g : V) :
    ℒₛₑₜ-predicate[V] (fun b ↦ f ‘ (g ‘ b) = f' ‘ b) := by
  have h : ℒₛₑₜ-predicate[V] (fun b ↦ ∃ u, u = g ‘ b ∧ f ‘ u = f' ‘ b) := by definability
  apply Language.Definable.of_iff h
  intro v
  change (f ‘ (g ‘ (v 0)) = f' ‘ (v 0)) ↔ _
  constructor
  · intro hh
    exact ⟨g ‘ (v 0), rfl, hh⟩
  · rintro ⟨u, rfl, hh⟩
    exact hh

/-- Membership is a well order on any set of ordinals. -/
theorem membershipRelation_wellOrder_of_subset {θ B : V} [IsOrdinal θ] (hB : B ⊆ θ) :
    IsInternalWellOrder (membershipRelation B) B := by
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, membershipRelation_wellFounded B, ?_, ?_⟩
  · intro x hx y _ z hz hxy hyz
    have : IsOrdinal z := IsOrdinal.of_mem (hB z hz)
    exact (pair_mem_membershipRelation B x z).mpr ⟨hx, hz,
      IsOrdinal.toIsTransitive.mem_trans ((pair_mem_membershipRelation B x y).mp hxy).2.2
        ((pair_mem_membershipRelation B y z).mp hyz).2.2⟩
  · intro x hx y hy
    rcases (inferInstance : IsOrdinal θ).trichotomy x (hB x hx) y (hB y hy) with hxy | heq | hyx
    · exact Or.inl ((pair_mem_membershipRelation B x y).mpr ⟨hx, hy, hxy⟩)
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr ((pair_mem_membershipRelation B y x).mpr ⟨hy, hx, hyx⟩))

/-- The properties of a set that looks like a rank stage of a ground model, relative to the
regular cardinal `δ` and the ordinal `θ`: transitivity, closure under intersections and under the
definable operations used in the coding argument, and the `δ`-cover and `δ`-approximation
properties for subsets of `θ`. -/
structure GroundLike (M δ θ : V) : Prop where
  /-- `M` is transitive. -/
  transitive : ∀ x ∈ M, x ⊆ M
  /-- `M` is closed under intersections. -/
  inter : InterClosed M
  /-- Every small subset of `θ` is covered by a small member of `M`. -/
  cover : HasSmallCover M δ θ
  /-- A subset of `θ` all of whose small pieces lie in `M` lies in `M`. -/
  approx : HasApproximation M δ θ
  /-- Every subset of `θ` of size at most `δ` is covered by a member of `M` that `M` injects
  into `δ`. -/
  boundedCover : ∀ A, A ⊆ θ → A ≤# δ → ∃ C ∈ M, A ⊆ C ∧ C ⊆ θ ∧ MBounded M δ C
  /-- `M` is closed under images. -/
  image : ∀ g ∈ M, ∀ B ∈ M, imageSet g B ∈ M
  /-- `M` is closed under transporting membership along a function. -/
  inducedRelation : ∀ g ∈ M, ∀ B ∈ M, inducedImageRelation g B ∈ M
  /-- `M` contains the membership relation of each of its members. -/
  membershipRelation_mem : ∀ B ∈ M, membershipRelation B ∈ M
  /-- `M` is closed under Mostowski collapses of its well-founded extensional members. -/
  collapse : ∀ R ∈ M, ∀ D ∈ M, IsInternallyWellFounded R D → IsExtensionalOn R D →
    mostowskiMap R D ∈ M
  /-- `M` is closed under reading a subset back off two collapses. -/
  decode : ∀ B ∈ M, ∀ f ∈ M, ∀ f' ∈ M, ∀ T ∈ M, decodeSet B f f' T ∈ M

section

variable {M M' δ θ : V} [IsOrdinal θ]

/-- Step 2 of Lemma 6.2: a subset of a shared set of size at most `δ` that lies in `M` also lies
in `M'`. -/
theorem mem_of_subset_of_bounded (hM : GroundLike M δ θ) (hM' : GroundLike M' δ θ)
    (hpar : ∀ X, X ⊆ δ ×ˢ δ → (X ∈ M ↔ X ∈ M')) (hpar1 : ∀ X, X ⊆ δ → (X ∈ M ↔ X ∈ M'))
    {A B : V} (hBM : B ∈ M) (hBM' : B ∈ M') (hBθ : B ⊆ θ) (hBδ : B ≤# δ)
    (hAM : A ∈ M) (hAB : A ⊆ B) : A ∈ M' := by
  -- an injection `g ∈ M` of a set `D ⊇ B` into `δ`
  obtain ⟨C, hCM, hBC, -, hCb⟩ := hM.boundedCover B hBθ hBδ
  obtain ⟨D, hDM, hCD, g, hgM, hg, hginj⟩ := hCb
  have hgfun : IsFunction g := IsFunction.of_mem hg
  have hgdom : domain g = D := domain_eq_of_mem_function hg
  have hBD : B ⊆ D := fun x hx ↦ hCD x (hBC x hx)
  have hAD : A ⊆ D := fun x hx ↦ hBD x (hAB x hx)
  have hBdom : B ⊆ domain g := by rw [hgdom]; exact hBD
  have hAdom : A ⊆ domain g := by rw [hgdom]; exact hAD
  -- the image of `B`, the transported membership relation, and the image of `A`
  have hIM : imageSet g B ∈ M := hM.image g hgM B hBM
  have hTM : imageSet g A ∈ M := hM.image g hgM A hAM
  have hwM : inducedImageRelation g B ∈ M := hM.inducedRelation g hgM B hBM
  have hIδ : imageSet g B ⊆ δ := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := (mem_imageSet_iff hBdom z).mp hz
    exact function_value_mem hg (hBD b hb)
  have hTδ : imageSet g A ⊆ δ := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := (mem_imageSet_iff hAdom z).mp hz
    exact function_value_mem hg (hAD a ha)
  have hwδ : inducedImageRelation g B ⊆ δ ×ˢ δ := fun p hp ↦
    prod_subset_prod_of_subset hIδ hIδ p (inducedImageRelation_subset g B p hp)
  have hIM' : imageSet g B ∈ M' := (hpar1 _ hIδ).mp hIM
  have hTM' : imageSet g A ∈ M' := (hpar1 _ hTδ).mp hTM
  have hwM' : inducedImageRelation g B ∈ M' := (hpar _ hwδ).mp hwM
  -- the inverse of `g` on `B`
  have hgB : g ↾ B ∈ δ ^ B :=
    restrict_mem_function_of_values hBdom (fun x hx ↦ function_value_mem hg (hBD x hx))
  have hgBinj : Injective (g ↾ B) := fun x₁ x₂ y h1 h2 ↦
    hginj x₁ x₂ y (restrict_subset g B _ h1) (restrict_subset g B _ h2)
  have hgBval : ∀ b ∈ B, (g ↾ B) ‘ b = g ‘ b := fun b hb ↦ value_restrict (hBdom b hb) hb
  have hgi : converseGraph (g ↾ B) ∈ B ^ imageSet g B := converseGraph_mem_function hgB hgBinj
  have hgiinj : Injective (converseGraph (g ↾ B)) := converseGraph_injective (g ↾ B)
  have hgival : ∀ b ∈ B, (converseGraph (g ↾ B)) ‘ (g ‘ b) = b := by
    intro b hb
    rw [← hgBval b hb]
    exact converseGraph_value_value hgB hgBinj hb
  have hgiθ : converseGraph (g ↾ B) ∈ θ ^ imageSet g B :=
    mem_function_of_mem_function_of_subset hgi hBθ
  -- the transported relation is the pulled-back membership relation of the inverse
  have hweq : inducedImageRelation g B = pulledMembership (imageSet g B) (converseGraph (g ↾ B)) := by
    apply mem_ext
    intro p
    constructor
    · intro hp
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp (inducedImageRelation_subset g B p hp)
      obtain ⟨-, -, b, hb, b', hb', hbb', rfl, rfl⟩ := (pair_mem_inducedImageRelation g B u v).mp hp
      rw [pair_mem_pulledMembership, hgival b hb, hgival b' hb']
      exact ⟨hu, hv, hbb'⟩
    · intro hp
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp ((mem_sep_iff.mp hp).1)
      obtain ⟨-, -, hmem⟩ := (pair_mem_pulledMembership _ _ u v).mp hp
      obtain ⟨b, hb, rfl⟩ := (mem_imageSet_iff hBdom u).mp hu
      obtain ⟨b', hb', rfl⟩ := (mem_imageSet_iff hBdom v).mp hv
      rw [hgival b hb, hgival b' hb'] at hmem
      exact (pair_mem_inducedImageRelation g B _ _).mpr ⟨hu, hv, b, hb, b', hb', hmem, rfl, rfl⟩
  have hword : IsInternalWellOrder (inducedImageRelation g B) (imageSet g B) := by
    rw [hweq]
    exact pulledMembership_wellOrder hgiθ hgiinj
  have hwwf := hword.2.1
  have hwext := internalWellOrder_extensional hword
  -- membership on `B` is a well order
  have hBword : IsInternalWellOrder (membershipRelation B) B :=
    membershipRelation_wellOrder_of_subset hBθ
  have hBwf := hBword.2.1
  have hBext := internalWellOrder_extensional hBword
  -- both collapses lie in `M'`
  obtain ⟨f, hfdef⟩ : ∃ f, f = mostowskiMap (inducedImageRelation g B) (imageSet g B) := ⟨_, rfl⟩
  obtain ⟨f', hf'def⟩ : ∃ f', f' = mostowskiMap (membershipRelation B) B := ⟨_, rfl⟩
  have hfM' : f ∈ M' := hfdef ▸ hM'.collapse _ hwM' _ hIM' hwwf hwext
  have hf'M' : f' ∈ M' := hf'def ▸ hM'.collapse _ (hM'.membershipRelation_mem B hBM') _ hBM' hBwf hBext
  have hfval : ∀ u ∈ imageSet g B, ∀ z, z ∈ f ‘ u ↔
      ∃ v ∈ imageSet g B, ⟨v, u⟩ₖ ∈ inducedImageRelation g B ∧ f ‘ v = z := by
    intro u hu z
    rw [hfdef, mostowskiMap_of_wellFounded hwwf]
    exact mem_collapseGraph_value hwwf hu
  have hf'val : ∀ b ∈ B, ∀ z, z ∈ f' ‘ b ↔
      ∃ c ∈ B, ⟨c, b⟩ₖ ∈ membershipRelation B ∧ f' ‘ c = z := by
    intro b hb z
    rw [hf'def, mostowskiMap_of_wellFounded hBwf]
    exact mem_collapseGraph_value hBwf hb
  have hf'inj : ∀ x ∈ B, ∀ y ∈ B, f' ‘ x = f' ‘ y → x = y := by
    have hc := mostowskiMap_isTransitiveCollapse hBwf hBext
    rw [← hf'def] at hc
    exact hc.2.2.2.1
  -- the collapses agree along `g`
  have key : ∀ b ∈ B, f ‘ (g ‘ b) = f' ‘ b := by
    apply internalWellFounded_induction hBwf (fun b ↦ f ‘ (g ‘ b) = f' ‘ b)
      (valueCompEq_definable f f' g)
    intro b hb ih
    have hgbI : g ‘ b ∈ imageSet g B := (mem_imageSet_iff hBdom _).mpr ⟨b, hb, rfl⟩
    apply mem_ext
    intro z
    rw [hfval _ hgbI z, hf'val b hb z]
    constructor
    · rintro ⟨v, hv, hvw, rfl⟩
      obtain ⟨-, -, c, hc, c', hc', hcc', rfl, heq⟩ :=
        (pair_mem_inducedImageRelation g B v (g ‘ b)).mp hvw
      have hcb : c' = b := injective_value_eq hg hginj (hBD c' hc') (hBD b hb) heq.symm
      rw [hcb] at hcc'
      refine ⟨c, hc, (pair_mem_membershipRelation B c b).mpr ⟨hc, hb, hcc'⟩, ?_⟩
      exact (ih c hc ((pair_mem_membershipRelation B c b).mpr ⟨hc, hb, hcc'⟩)).symm
    · rintro ⟨c, hc, hcb, rfl⟩
      have hcmem := ((pair_mem_membershipRelation B c b).mp hcb).2.2
      have hcI : g ‘ c ∈ imageSet g B := (mem_imageSet_iff hBdom _).mpr ⟨c, hc, rfl⟩
      refine ⟨g ‘ c, hcI, ?_, ih c hc hcb⟩
      exact (pair_mem_inducedImageRelation g B _ _).mpr ⟨hcI, hgbI, c, hc, b, hb, hcmem, rfl, rfl⟩
  -- `A` is read off the two collapses
  have hAeq : A = decodeSet B f f' (imageSet g A) := by
    apply mem_ext
    intro a
    rw [mem_decodeSet_iff]
    constructor
    · intro ha
      exact ⟨hAB a ha, g ‘ a, (mem_imageSet_iff hAdom _).mpr ⟨a, ha, rfl⟩, key a (hAB a ha)⟩
    · rintro ⟨hb, t, htT, hft⟩
      obtain ⟨a', ha', rfl⟩ := (mem_imageSet_iff hAdom t).mp htT
      have heq : f' ‘ a' = f' ‘ a := (key a' (hAB a' ha')).symm.trans hft
      exact hf'inj a' (hAB a' ha') a hb heq ▸ ha'
  rw [hAeq]
  exact hM'.decode B hBM' f hfM' f' hf'M' _ hTM'

variable (hAC : InternalChoice V) (hreg : IsRegularCardinal δ) (hωδ : (ω : V) ∈ δ)

include hAC hreg hωδ in
/-- Step 3 of Lemma 6.2: every subset of `θ` in `M` lies in `M'`. -/
theorem mem_of_groundLike (hM : GroundLike M δ θ) (hM' : GroundLike M' δ θ)
    (hpar : ∀ X, X ⊆ δ ×ˢ δ → (X ∈ M ↔ X ∈ M')) (hpar1 : ∀ X, X ⊆ δ → (X ∈ M ↔ X ∈ M'))
    {A : V} (hAθ : A ⊆ θ) (hAM : A ∈ M) : A ∈ M' := by
  refine hM'.approx A hAθ ?_
  intro B hBM' hBθ hBs
  obtain ⟨B₁, hB₁M, hB₁M', hBB₁, hB₁θ, hB₁δ⟩ :=
    simultaneous_cover hAC hreg hωδ hM.cover hM'.cover hM.approx hM'.approx hM.inter hM'.inter
      hBθ (uSmall_of_mSmall hBs)
  have h1 : A ∩ B₁ ∈ M := hM.inter A hAM B₁ hB₁M
  have h2 : A ∩ B₁ ∈ M' :=
    mem_of_subset_of_bounded hM hM' hpar hpar1 hB₁M hB₁M' hB₁θ hB₁δ h1
      (fun x hx ↦ (mem_inter_iff.mp hx).2)
  have h3 : A ∩ B = (A ∩ B₁) ∩ B := by
    apply mem_ext
    intro x
    rw [mem_inter_iff, mem_inter_iff, mem_inter_iff]
    exact ⟨fun h ↦ ⟨⟨h.1, hBB₁ x h.2⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩
  rw [h3]
  exact hM'.inter _ h2 B hBM'

include hAC hreg hωδ in
/-- Laver's uniqueness lemma: two ground-like sets that agree on subsets of `δ` and on subsets of
`δ ×ˢ δ` contain the same subsets of `θ`. -/
theorem ground_uniqueness (hM : GroundLike M δ θ) (hM' : GroundLike M' δ θ)
    (hpar : ∀ X, X ⊆ δ ×ˢ δ → (X ∈ M ↔ X ∈ M')) (hpar1 : ∀ X, X ⊆ δ → (X ∈ M ↔ X ∈ M')) :
    ∀ A, A ⊆ θ → (A ∈ M ↔ A ∈ M') := by
  intro A hAθ
  constructor
  · exact fun hA ↦ mem_of_groundLike hAC hreg hωδ hM hM' hpar hpar1 hAθ hA
  · exact fun hA ↦ mem_of_groundLike hAC hreg hωδ hM' hM (fun X h ↦ (hpar X h).symm)
      (fun X h ↦ (hpar1 X h).symm) hAθ hA

end

end ZFVP
