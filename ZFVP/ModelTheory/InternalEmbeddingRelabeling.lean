import ZFVP.ModelTheory.CodedBinaryIsomorphism
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.InternalWellFounded

/-! Relabel an internal extension so the image of each old element becomes
that element itself. The remaining elements receive tags outside the old carrier. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local instance] Classical.propDecidable
attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

theorem kpair_self_tag_not_mem (D y : V) : ⟨D, y⟩ₖ ∉ D := by
  intro h
  exact mem_irrefl (rank D)
    (IsOrdinal.toIsTransitive.mem_trans (rank_kpair_left_lt D y) (rank_mem h))

noncomputable def embeddingRelabelValue (D f y : V) : V :=
  if y ∈ range f then (converseGraph f) ‘ y else ⟨D, y⟩ₖ

instance embeddingRelabelValue_definable : ℒₛₑₜ-function₃[V] embeddingRelabelValue := by
  have h : ℒₛₑₜ-relation₄[V] (fun z D f y ↦
      (y ∈ range f ∧ z = (converseGraph f) ‘ y) ∨ (y ∉ range f ∧ z = ⟨D, y⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = embeddingRelabelValue (v 1) (v 2) (v 3) ↔ _
  unfold embeddingRelabelValue
  split <;> simp_all

noncomputable def embeddingRelabelCarrier (D A f : V) : V :=
  repl (embeddingRelabelValue D f) (by definability) A

@[simp] theorem mem_embeddingRelabelCarrier (D A f x : V) :
    x ∈ embeddingRelabelCarrier D A f ↔ ∃ y ∈ A, x = embeddingRelabelValue D f y := repl_spec _

instance embeddingRelabelCarrier_definable : ℒₛₑₜ-function₃[V] embeddingRelabelCarrier := by
  have h : ℒₛₑₜ-relation₄[V] (fun B D A f ↦
      ∀ x, x ∈ B ↔ ∃ y ∈ A, x = embeddingRelabelValue D f y) := by definability
  apply Language.Definable.of_iff h
  intro v
  simp only [mem_ext_iff, mem_embeddingRelabelCarrier]
  rfl

noncomputable def embeddingRelabelGraph (D A f : V) : V :=
  definableGraph A (embeddingRelabelValue D f) (by definability)

instance embeddingRelabelGraph_definable : ℒₛₑₜ-function₃[V] embeddingRelabelGraph := by
  have h : ℒₛₑₜ-relation₄[V] (fun g D A f ↦
      ∀ p, p ∈ g ↔ ∃ y ∈ A, p = ⟨y, embeddingRelabelValue D f y⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  simp only [mem_ext_iff, embeddingRelabelGraph, mem_definableGraph_iff]
  rfl

instance embeddingRelabelGraph_isFunction (D A f : V) : IsFunction (embeddingRelabelGraph D A f) := by
  unfold embeddingRelabelGraph
  infer_instance

theorem embeddingRelabelGraph_mem (D A f : V) :
    embeddingRelabelGraph D A f ∈ embeddingRelabelCarrier D A f ^ A := definableGraph_mem_function _ _ _

@[simp] theorem embeddingRelabelGraph_range (D A f : V) :
    range (embeddingRelabelGraph D A f) = embeddingRelabelCarrier D A f := range_definableGraph _ _ _

@[simp] theorem embeddingRelabelGraph_value {D A f y : V} (hy : y ∈ A) :
    (embeddingRelabelGraph D A f) ‘ y = embeddingRelabelValue D f y := value_definableGraph _ _ _ hy

theorem embeddingRelabelValue_old {D A f x : V} (hf : f ∈ A ^ D) (hi : Injective f) (hx : x ∈ D) :
    embeddingRelabelValue D f (f ‘ x) = x := by
  let : IsFunction f := IsFunction.of_mem hf
  have hr : f ‘ x ∈ range f := mem_range_of_kpair_mem
    (kpair_value_mem (by rw [domain_eq_of_mem_function hf]; exact hx))
  rw [embeddingRelabelValue, ite_eq_left hr, converseGraph_value_value hf hi hx]

theorem embeddingRelabelValue_injective {D A f x y : V} (hf : f ∈ A ^ D) (hi : Injective f)
    (h : embeddingRelabelValue D f x = embeddingRelabelValue D f y) : x = y := by
  by_cases hx : x ∈ range f <;> by_cases hy : y ∈ range f
  · simp only [embeddingRelabelValue, ite_eq_left hx, ite_eq_left hy] at h
    calc
      x = f ‘ ((converseGraph f) ‘ x) := (value_converseGraph_value hf hi hx).symm
      _ = f ‘ ((converseGraph f) ‘ y) := congrArg (fun z ↦ f ‘ z) h
      _ = y := value_converseGraph_value hf hi hy
  · simp only [embeddingRelabelValue, ite_eq_left hx, ite_eq_right hy] at h
    exact False.elim (kpair_self_tag_not_mem D y
      (h ▸ function_value_mem (converseGraph_mem_function hf hi) hx))
  · simp only [embeddingRelabelValue, ite_eq_right hx, ite_eq_left hy] at h
    exact False.elim (kpair_self_tag_not_mem D x
      (h.symm ▸ function_value_mem (converseGraph_mem_function hf hi) hy))
  · simp only [embeddingRelabelValue, ite_eq_right hx, ite_eq_right hy] at h
    exact (kpair_iff.mp h).2

theorem embeddingRelabelGraph_injective {D A f : V} (hf : f ∈ A ^ D) (hi : Injective f) :
    Injective (embeddingRelabelGraph D A f) := by
  intro x y z hx hy
  obtain ⟨_, hzx⟩ := (pair_mem_definableGraph_iff A _ (by definability) x z).mp hx
  obtain ⟨_, hzy⟩ := (pair_mem_definableGraph_iff A _ (by definability) y z).mp hy
  exact embeddingRelabelValue_injective hf hi (hzx.symm.trans hzy)

theorem embeddingRelabelCarrier_includes {D A f : V} (hf : f ∈ A ^ D) (hi : Injective f) :
    D ⊆ embeddingRelabelCarrier D A f := by
  intro x hx
  exact (mem_embeddingRelabelCarrier _ _ _ _).mpr
    ⟨f ‘ x, function_value_mem hf hx, (embeddingRelabelValue_old hf hi hx).symm⟩

theorem embeddingRelabelCarrier_countable {D A f : V} (hA : IsInternallyCountable A) :
    IsInternallyCountable (embeddingRelabelCarrier D A f) := internallyCountable_repl _ _ hA

theorem embeddingRelabelCarrier_nonempty {D A f : V} (hA : IsNonempty A) :
    IsNonempty (embeddingRelabelCarrier D A f) := by
  obtain ⟨y, hy⟩ := hA
  exact ⟨embeddingRelabelValue D f y, (mem_embeddingRelabelCarrier _ _ _ _).mpr ⟨y, hy, rfl⟩⟩

theorem embeddingRelabelGraph_comp_old {D A f : V} (hf : f ∈ A ^ D) (hi : Injective f) :
    compose f (embeddingRelabelGraph D A f) = SetTheory.identity D := by
  apply function_eq_of_values (compose_function hf (embeddingRelabelGraph_mem D A f))
    (mem_function_of_mem_function_of_subset (identity_mem_function D) (embeddingRelabelCarrier_includes hf hi))
  intro x hx
  rw [value_compose_of_mem_function hf (embeddingRelabelGraph_mem D A f) hx,
    embeddingRelabelGraph_value (function_value_mem hf hx), embeddingRelabelValue_old hf hi hx, identity_value hx]

noncomputable def embeddingRelabelEdges (D A R f : V) : V :=
  {p ∈ embeddingRelabelCarrier D A f ×ˢ embeddingRelabelCarrier D A f ;
    ⟨(converseGraph (embeddingRelabelGraph D A f)) ‘ (kpair.π₁ p),
      (converseGraph (embeddingRelabelGraph D A f)) ‘ (kpair.π₂ p)⟩ₖ ∈ R}

instance embeddingRelabelEdges_definable : ℒₛₑₜ-function₄[V] embeddingRelabelEdges := by
  have h : Language.DefinableRel₅ ℒₛₑₜ (fun S D A R f : V ↦ ∀ p,
      p ∈ S ↔ p ∈ embeddingRelabelCarrier D A f ×ˢ embeddingRelabelCarrier D A f ∧
        ⟨(converseGraph (embeddingRelabelGraph D A f)) ‘ (kpair.π₁ p),
          (converseGraph (embeddingRelabelGraph D A f)) ‘ (kpair.π₂ p)⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff h
  intro v
  simp only [mem_ext_iff, embeddingRelabelEdges, mem_sep_iff]
  rfl

theorem embeddingRelabelEdges_subset (D A R f : V) :
    embeddingRelabelEdges D A R f ⊆ embeddingRelabelCarrier D A f ×ˢ embeddingRelabelCarrier D A f :=
  fun _ h ↦ (mem_sep_iff.mp h).1

theorem embeddingRelabelEdges_iff {D A R f x y : V} (hf : f ∈ A ^ D) (hi : Injective f)
    (hx : x ∈ A) (hy : y ∈ A) :
    ⟨(embeddingRelabelGraph D A f) ‘ x, (embeddingRelabelGraph D A f) ‘ y⟩ₖ ∈ embeddingRelabelEdges D A R f ↔
      ⟨x, y⟩ₖ ∈ R := by
  have hg := embeddingRelabelGraph_mem D A f
  have hgi := embeddingRelabelGraph_injective hf hi
  simp only [embeddingRelabelEdges, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    converseGraph_value_value hg hgi hx, converseGraph_value_value hg hgi hy]
  exact and_iff_right ⟨function_value_mem hg hx, function_value_mem hg hy⟩

noncomputable def embeddingRelabelStructure (D A R f : V) : V :=
  binaryRelationStructureCode (embeddingRelabelCarrier D A f) (embeddingRelabelEdges D A R f)

instance embeddingRelabelStructure_definable : ℒₛₑₜ-function₄[V] embeddingRelabelStructure := by
  unfold embeddingRelabelStructure
  definability

@[simp] theorem embeddingRelabelStructure_domain (D A R f : V) :
    structureDomain (embeddingRelabelStructure D A R f) = embeddingRelabelCarrier D A f := by
  simp only [embeddingRelabelStructure, binaryRelationStructureCode_domain]

theorem embeddingRelabelGraph_elementary {D A R f : V} (hA : IsNonempty A)
    (hf : f ∈ A ^ D) (hi : Injective f) :
    IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode A R)
      (embeddingRelabelStructure D A R f) (embeddingRelabelGraph D A f) :=
  codedBinaryEmbedding_of_isomorphism hA (embeddingRelabelGraph_mem D A f)
    (embeddingRelabelGraph_injective hf hi) (embeddingRelabelGraph_range D A f)
    (fun _ hx _ hy ↦ embeddingRelabelEdges_iff hf hi hx hy)

theorem embeddingRelabelStructure_inclusion_elementary {D E A R f : V}
    (hf : IsCodedElementaryEmbedding membershipLanguageCode
      (binaryRelationStructureCode D E) (binaryRelationStructureCode A R) f) :
    IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E)
      (embeddingRelabelStructure D A R f) (SetTheory.identity D) := by
  have hff : f ∈ A ^ D := by simpa only [binaryRelationStructureCode_domain] using hf.function
  have hA : IsNonempty A := by simpa only [binaryRelationStructureCode_domain] using hf.target.domain_nonempty
  have hh := hf.comp (embeddingRelabelGraph_elementary hA hff hf.injective (R := R))
  rwa [embeddingRelabelGraph_comp_old hff hf.injective] at hh

end ZFVP
