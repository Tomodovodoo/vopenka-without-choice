import ZFVP.SetTheory.SupercompactMeasure
import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.ModelTheory.DerivedUltrafilterComplete

/-! # The normal fine measure derived from a small embedding

This is the measure half of Magidor's theorem (Magidor 1971; Kanamori, *The Higher Infinite*,
22.10). A coded elementary embedding `e` of a rank stage `hierarchy lb` into a rank stage
`hierarchy gam` with critical point `ab` gives a normal fine `ab`-complete ultrafilter on
`P_ab(ξ)` for every `ξ` below `lb`, provided `lb` sits below `e ‘ ab`.

The measure is `derivedFineMeasure e ab ξ`: the subsets `X` of `P_ab(ξ)` whose image `e ‘ X`
contains the seed `embeddingImage e ξ`, the pointwise image of `ξ` under `e`.

Every step transfers a bounded set operation across the embedding. Three bounded formulas are
added here, for the fine sets `{x ∈ K ; u ∈ x}`, the regressive sets `{x ∈ K ; g ‘ x ∈ x}` and
the level sets `{x ∈ K ; g ‘ x = u}`; the formula for indexed intersections comes from
`ZFVP.ModelTheory.DerivedUltrafilterComplete`.

The hypothesis `hP : e ‘ (smallSubsetsBelow ab ξ) = smallSubsetsBelow (e ‘ ab) (e ‘ ξ)` is
proved in `ZFVP.SetTheory.SmallSubsetsStage` and taken as given here. It is used once, to place
the seed inside `e ‘ P_ab(ξ)`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `X` is the set of members of `K` that contain `u`. -/
def boundedFineSetFormula : SetTheorySemisentence 3 :=
  “X K u. ∀ z ∈ K, z ∈ X ↔ u ∈ z”

/-- `X` is the set of members of `K` on which the function `g`, with values in `R`, is
regressive. -/
def boundedRegressiveSetFormula : SetTheorySemisentence 4 :=
  “X K R g. ∀ z ∈ K, z ∈ X ↔ ∃ y ∈ R, !boundedPairMemberFormula g z y ∧ y ∈ z”

/-- `X` is the set of members of `K` on which the function `g` takes the value `u`. -/
def boundedConstantSetFormula : SetTheorySemisentence 4 :=
  “X K g u. ∀ z ∈ K, z ∈ X ↔ !boundedPairMemberFormula g z u”

theorem boundedFineSetFormula_bounded : IsBoundedSetFormula boundedFineSetFormula :=
  .all (.bvar 1) (.and (.or (.nrel _ _) (.rel _ _)) (.or (.nrel _ _) (.rel _ _)))

theorem boundedRegressiveSetFormula_bounded : IsBoundedSetFormula boundedRegressiveSetFormula :=
  .all (.bvar 1) (.and
    (.or (.nrel _ _)
      (.exs (.bvar 3) (.and (boundedPairMemberFormula_bounded.subst _) (.rel _ _))))
    (.or (IsBoundedSetFormula.exs (.bvar 3)
      (.and (boundedPairMemberFormula_bounded.subst _) (.rel _ _))).neg (.rel _ _)))

theorem boundedConstantSetFormula_bounded : IsBoundedSetFormula boundedConstantSetFormula :=
  .all (.bvar 1) (.and
    (.or (.nrel _ _) (boundedPairMemberFormula_bounded.subst _))
    (.or (boundedPairMemberFormula_bounded.subst _).neg (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem boundedFineSetFormula_holds (K u : V) :
    boundedFineSetFormula.Evalb ![fineSetOn K u, K, u] := by
  simp (config := { contextual := true }) [boundedFineSetFormula, fineSetOn]

theorem boundedRegressiveSetFormula_holds {K R g : V} (hg : g ∈ R ^ K) :
    boundedRegressiveSetFormula.Evalb ![regressiveSetOn K g, K, R, g] := by
  let := IsFunction.of_mem hg
  simp [boundedRegressiveSetFormula, regressiveSetOn]
  intro x hx
  constructor
  · rintro ⟨-, hv⟩
    exact ⟨g ‘ x, function_value_mem hg hx,
      kpair_value_mem ((domain_eq_of_mem_function hg).symm ▸ hx), hv⟩
  · rintro ⟨y, -, hp, hy⟩
    exact ⟨hx, by rw [value_eq_of_kpair_mem hp]; exact hy⟩

theorem boundedConstantSetFormula_holds {K R g u : V} (hg : g ∈ R ^ K) :
    boundedConstantSetFormula.Evalb ![constantSetOn K g u, K, g, u] := by
  let := IsFunction.of_mem hg
  simp [boundedConstantSetFormula, constantSetOn]
  intro x hx
  rw [kpair_mem_iff_value, domain_eq_of_mem_function hg]

/-- The pointwise image of `t` under the graph `e`. -/
noncomputable def embeddingImage (e t : V) : V := repl (fun z ↦ e ‘ z) (by definability) t

@[simp] theorem mem_embeddingImage_iff (e t y : V) :
    y ∈ embeddingImage e t ↔ ∃ z ∈ t, e ‘ z = y := by
  simp only [embeddingImage, repl_spec]
  exact ⟨fun ⟨z, hz, hy⟩ ↦ ⟨z, hz, hy.symm⟩, fun ⟨z, hz, hy⟩ ↦ ⟨z, hz, hy.symm⟩⟩

instance embeddingImage_definable : ℒₛₑₜ-function₂[V] embeddingImage := by
  have hd : ℒₛₑₜ-relation₃[V] (fun Y e t ↦ ∀ y, y ∈ Y ↔ ∃ z ∈ t, e ‘ z = y) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = embeddingImage (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_embeddingImage_iff]

/-- The pointwise image of a well-orderable set is no larger than that set. -/
theorem embeddingImage_cardLE {e t : V} (ht : IsWellOrderable t) : embeddingImage e t ≤# t := by
  apply cardLE_of_surjective_function ht
    (definableGraph_mem_function t (fun z ↦ e ‘ z) (by definability))
  simp only [range_definableGraph]

/-- The measure derived from the embedding `e` at the seed `embeddingImage e ξ`. -/
noncomputable def derivedFineMeasure (e ab ξ : V) : V :=
  sep (℘ (smallSubsetsBelow ab ξ)) (fun X ↦ embeddingImage e ξ ∈ e ‘ X) (by definability)

instance derivedFineMeasure_definable : ℒₛₑₜ-function₃[V] derivedFineMeasure := by
  have hd : ℒₛₑₜ-relation₄[V] (fun U e ab ξ ↦ ∀ X,
      X ∈ U ↔ X ⊆ smallSubsetsBelow ab ξ ∧ embeddingImage e ξ ∈ e ‘ X) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = derivedFineMeasure (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [derivedFineMeasure, mem_sep_iff, mem_power_iff]

@[simp] theorem mem_derivedFineMeasure_iff (e ab ξ X : V) :
    X ∈ derivedFineMeasure e ab ξ ↔
      X ⊆ smallSubsetsBelow ab ξ ∧ embeddingImage e ξ ∈ e ‘ X := by
  simp only [derivedFineMeasure, mem_sep_iff, mem_power_iff]

namespace IsCodedMembershipEmbedding

variable {A B e : V} [IsTransitive A] [IsTransitive B]

theorem value_fineSetOn_iff (h : IsCodedMembershipEmbedding A B e) {K u w : V}
    (hK : K ∈ A) (hu : u ∈ A) (hX : fineSetOn K u ∈ A) (hw : w ∈ e ‘ K) :
    w ∈ e ‘ (fineSetOn K u) ↔ e ‘ u ∈ w := by
  have hb := (h.bounded_formula_iff boundedFineSetFormula_bounded ![fineSetOn K u, K, u]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hX, hK, hu])).mp
      (boundedFineSetFormula_holds K u)
  simp only [boundedFineSetFormula] at hb
  simp at hb
  exact hb w hw

theorem value_regressiveSetOn_iff (h : IsCodedMembershipEmbedding A B e) {K R g w : V}
    (hK : K ∈ A) (hR : R ∈ A) (hg : g ∈ A) (hX : regressiveSetOn K g ∈ A)
    (hgf : g ∈ R ^ K) (hw : w ∈ e ‘ K) :
    w ∈ e ‘ (regressiveSetOn K g) ↔ ∃ y ∈ e ‘ R, ⟨w, y⟩ₖ ∈ e ‘ g ∧ y ∈ w := by
  have hb := (h.bounded_formula_iff boundedRegressiveSetFormula_bounded
    ![regressiveSetOn K g, K, R, g]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hX, hK, hR, hg])).mp
      (boundedRegressiveSetFormula_holds hgf)
  simp only [boundedRegressiveSetFormula] at hb
  simp [boundedPairMemberFormula] at hb
  exact hb w hw

theorem value_constantSetOn_iff (h : IsCodedMembershipEmbedding A B e) {K R g u w : V}
    (hK : K ∈ A) (hg : g ∈ A) (hu : u ∈ A) (hX : constantSetOn K g u ∈ A)
    (hgf : g ∈ R ^ K) (hw : w ∈ e ‘ K) :
    w ∈ e ‘ (constantSetOn K g u) ↔ ⟨w, e ‘ u⟩ₖ ∈ e ‘ g := by
  have hb := (h.bounded_formula_iff boundedConstantSetFormula_bounded
    ![constantSetOn K g u, K, g, u]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hX, hK, hg, hu])).mp
      (boundedConstantSetFormula_holds (R := R) hgf)
  simp only [boundedConstantSetFormula] at hb
  simp [boundedPairMemberFormula] at hb
  exact hb w hw

end IsCodedMembershipEmbedding

/-- Magidor's derived measure: for a coded elementary embedding of successor-closed rank stages
with critical point `ab`, and any `ξ` of the source stage, the sets whose image contains the
seed form a normal fine `ab`-complete ultrafilter on `P_ab(ξ)`. -/
theorem derived_isNormalFineMeasure {lb gam e ab ξ : V} [IsOrdinal lb] [IsOrdinal gam]
    (hlb : ∀ η ∈ lb, succ η ∈ lb)
    (he : IsCodedMembershipEmbedding (hierarchy lb) (hierarchy gam) e)
    (hc : IsCriticalPoint (hierarchy lb) e ab)
    (hξ : ξ ∈ lb) (hlbk : lb ∈ e ‘ ab)
    (hP : e ‘ (smallSubsetsBelow ab ξ) = smallSubsetsBelow (e ‘ ab) (e ‘ ξ)) :
    IsNormalFineMeasure ab ξ (derivedFineMeasure e ab ξ) := by
  classical
  let := hierarchy_transitive lb
  let := hierarchy_transitive gam
  let := hc.ordinal
  have hξo : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξA : ξ ∈ hierarchy lb := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact hξ
  have hPsub : smallSubsetsBelow ab ξ ⊆ ℘ ξ := fun x hx ↦
    mem_power_iff.mpr ((mem_smallSubsetsBelow_iff ab ξ x).mp hx).1
  have hPA : smallSubsetsBelow ab ξ ∈ hierarchy lb :=
    subset_mem_hierarchy_limit hlb (power_mem_hierarchy_limit hlb hξA) hPsub
  have hmemA : ∀ {X : V}, X ⊆ smallSubsetsBelow ab ξ → X ∈ hierarchy lb :=
    fun hX ↦ subset_mem_hierarchy_limit hlb hPA hX
  have hPPA : ℘ (smallSubsetsBelow ab ξ) ∈ hierarchy lb := power_mem_hierarchy_limit hlb hPA
  -- the seed sits inside the image of the base set
  have hseed : embeddingImage e ξ ∈ e ‘ (smallSubsetsBelow ab ξ) := by
    rw [hP, mem_smallSubsetsBelow_iff]
    refine ⟨?_, lb, hlbk, ?_⟩
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := (mem_embeddingImage_iff e ξ y).mp hy
      exact (he.value_mem_iff ((hierarchy_transitive lb).mem_trans hz hξA) hξA).mpr hz
    · exact (embeddingImage_cardLE (ordinal_wellOrderable ξ)).trans
        (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive ξ hξ))
  have hUsub : derivedFineMeasure e ab ξ ⊆ ℘ (smallSubsetsBelow ab ξ) := fun X hX ↦
    mem_power_iff.mpr ((mem_derivedFineMeasure_iff e ab ξ X).mp hX).1
  refine ⟨⟨hUsub, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  -- the base set is in the measure
  · exact (mem_derivedFineMeasure_iff _ _ _ _).mpr ⟨subset_refl _, hseed⟩
  -- the empty set is not
  · intro h0
    have hm := ((mem_derivedFineMeasure_iff _ _ _ _).mp h0).2
    rw [he.value_empty (hmemA (by simp))] at hm
    exact not_mem_empty hm
  -- upward closure
  · intro X hX Y hY hXY
    obtain ⟨hs, hm⟩ := (mem_derivedFineMeasure_iff _ _ _ _).mp hX
    exact (mem_derivedFineMeasure_iff _ _ _ _).mpr
      ⟨hY, he.value_subset (hmemA hs) (hmemA hY) hXY _ hm⟩
  -- closure under pairwise intersections
  · intro X hX Y hY
    obtain ⟨hsX, hmX⟩ := (mem_derivedFineMeasure_iff _ _ _ _).mp hX
    obtain ⟨hsY, hmY⟩ := (mem_derivedFineMeasure_iff _ _ _ _).mp hY
    have hs : X ∩ Y ⊆ smallSubsetsBelow ab ξ := fun z hz ↦ hsX z (mem_inter_iff.mp hz).1
    refine (mem_derivedFineMeasure_iff _ _ _ _).mpr ⟨hs, ?_⟩
    rw [he.value_intersection (hmemA hsX) (hmemA hsY) (hmemA hs)]
    exact mem_inter_iff.mpr ⟨hmX, hmY⟩
  -- ultra
  · intro X hX
    by_cases hm : embeddingImage e ξ ∈ e ‘ X
    · exact Or.inl ((mem_derivedFineMeasure_iff _ _ _ _).mpr ⟨hX, hm⟩)
    · have hcs : relativeComplement (smallSubsetsBelow ab ξ) X ⊆ smallSubsetsBelow ab ξ :=
        fun z hz ↦ (mem_relativeComplement_iff _ _ _).mp hz |>.1
      refine Or.inr ((mem_derivedFineMeasure_iff _ _ _ _).mpr ⟨hcs, ?_⟩)
      rw [he.value_relativeComplement hPA (hmemA hX) (hmemA hcs)]
      exact (mem_relativeComplement_iff _ _ _).mpr ⟨hseed, hm⟩
  -- completeness below the critical point
  · intro α hα g hg
    have hαA : α ∈ hierarchy lb := (hierarchy_transitive lb).mem_trans hα hc.mem_domain
    have hαo : IsOrdinal α := IsOrdinal.of_mem hα
    have hgp : g ∈ (℘ (smallSubsetsBelow ab ξ)) ^ α :=
      mem_function_of_mem_function_of_subset hg hUsub
    have hgA : g ∈ hierarchy lb := (hierarchy_transitive lb).mem_trans hgp
      (function_mem_hierarchy_limit hlb hαA hPPA)
    have hW : indexedIntersection (smallSubsetsBelow ab ξ) α g ⊆ smallSubsetsBelow ab ξ :=
      fun z hz ↦ ((mem_indexedIntersection_iff _ _ _ _).mp hz).1
    refine (mem_derivedFineMeasure_iff _ _ _ _).mpr ⟨hW, ?_⟩
    have hbf := (he.bounded_formula_iff boundedIndexedIntersectionFormula_bounded
      ![indexedIntersection (smallSubsetsBelow ab ξ) α g, smallSubsetsBelow ab ξ, α,
        ℘ (smallSubsetsBelow ab ξ), g]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hmemA hW, hPA, hαA, hPPA, hgA])).mp
        (boundedIndexedIntersectionFormula_holds (smallSubsetsBelow ab ξ) hgp)
    simp [boundedIndexedIntersectionFormula, boundedIntersectionAtFormula] at hbf
    apply (hbf _ hseed).mpr
    intro i hi
    rw [hc.fixed_below hα] at hi
    have hiab : i ∈ ab := IsOrdinal.toIsTransitive.mem_trans hi hα
    have hgiP := function_value_mem hgp hi
    have hgiA := (hierarchy_transitive lb).mem_trans hgiP hPPA
    have hmap := he.value_function hgA hαA hPPA hgp
    let := IsFunction.of_mem hmap
    have hv := he.value_apply hgA hαA (IsFunction.of_mem hgp)
      (domain_eq_of_mem_function hgp) hi
    rw [hc.fixed_below hiab] at hv
    refine ⟨e ‘ (g ‘ i), (he.value_mem_iff hgiA hPPA).mpr hgiP, ?_, ?_⟩
    · refine kpair_mem_iff_value.mpr ⟨?_, hv⟩
      rw [domain_eq_of_mem_function hmap, hc.fixed_below hα]
      exact hi
    · exact ((mem_derivedFineMeasure_iff _ _ _ _).mp (function_value_mem hg hi)).2
  -- fineness
  · intro ζ hζ
    have hζA := (hierarchy_transitive lb).mem_trans hζ hξA
    have hsub : fineSetOn (smallSubsetsBelow ab ξ) ζ ⊆ smallSubsetsBelow ab ξ :=
      fun x hx ↦ (mem_sep_iff.mp hx).1
    show fineSetOn (smallSubsetsBelow ab ξ) ζ ∈ derivedFineMeasure e ab ξ
    refine (mem_derivedFineMeasure_iff _ _ _ _).mpr ⟨hsub, ?_⟩
    rw [he.value_fineSetOn_iff hPA hζA (hmemA hsub) hseed]
    exact (mem_embeddingImage_iff e ξ (e ‘ ζ)).mpr ⟨ζ, hζ, rfl⟩
  -- normality
  · intro f hf hreg
    have hfA : f ∈ hierarchy lb := (hierarchy_transitive lb).mem_trans hf
      (function_mem_hierarchy_limit hlb hPA hξA)
    have hregsub : regressiveSetOn (smallSubsetsBelow ab ξ) f ⊆ smallSubsetsBelow ab ξ :=
      fun x hx ↦ (mem_sep_iff.mp hx).1
    have h1 : embeddingImage e ξ ∈ e ‘ (regressiveSetOn (smallSubsetsBelow ab ξ) f) :=
      ((mem_derivedFineMeasure_iff _ _ _ _).mp hreg).2
    rw [he.value_regressiveSetOn_iff hPA hξA hfA (hmemA hregsub) hf hseed] at h1
    obtain ⟨y, _, hpair, hys⟩ := h1
    obtain ⟨ζ, hζ, rfl⟩ := (mem_embeddingImage_iff e ξ y).mp hys
    have hζA := (hierarchy_transitive lb).mem_trans hζ hξA
    refine ⟨ζ, hζ, ?_⟩
    have hcsub : constantSetOn (smallSubsetsBelow ab ξ) f ζ ⊆ smallSubsetsBelow ab ξ :=
      fun x hx ↦ (mem_sep_iff.mp hx).1
    show constantSetOn (smallSubsetsBelow ab ξ) f ζ ∈ derivedFineMeasure e ab ξ
    refine (mem_derivedFineMeasure_iff _ _ _ _).mpr ⟨hcsub, ?_⟩
    rw [he.value_constantSetOn_iff hPA hfA hζA (hmemA hcsub) hf hseed]
    exact hpair

end ZFVP
