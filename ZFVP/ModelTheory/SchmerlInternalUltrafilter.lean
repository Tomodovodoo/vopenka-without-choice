import ZFVP.SetTheory.MaximalAntichains
import ZFVP.SetTheory.UltrafilterFibers
import ZFVP.SetTheory.CountableSets

/-! Internal ultrafilter extension along a well-ordering of the power set.
The recursion and its resulting filter are sets in the given ZF model. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ProperSetFilter (K F : V) : Prop :=
  F ⊆ ℘ K ∧ K ∈ F ∧ (∅ : V) ∉ F ∧
    (∀ X ∈ F, ∀ Y, Y ⊆ K → X ⊆ Y → Y ∈ F) ∧
    ∀ X ∈ F, ∀ Y ∈ F, X ∩ Y ∈ F

instance properSetFilter_definable : ℒₛₑₜ-relation[V] ProperSetFilter := by
  unfold ProperSetFilter
  definability

noncomputable def adjoinFilter (K F X : V) : V :=
  F ∪ {Y ∈ ℘ K ; ∃ Z ∈ F, Z ∩ X ⊆ Y}

theorem mem_adjoinFilter (K F X Y : V) :
    Y ∈ adjoinFilter K F X ↔ Y ∈ F ∨ Y ⊆ K ∧ ∃ Z ∈ F, Z ∩ X ⊆ Y := by
  simp [adjoinFilter]

instance adjoinFilter_definable : ℒₛₑₜ-function₃[V] adjoinFilter := by
  have h : ℒₛₑₜ-relation₄[V] (fun Y K F X ↦ ∀ Z,
      Z ∈ Y ↔ Z ∈ F ∨ Z ⊆ K ∧ ∃ W ∈ F, W ∩ X ⊆ Z) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_adjoinFilter]
  rfl

theorem subset_adjoinFilter (K F X : V) : F ⊆ adjoinFilter K F X :=
  fun _ hY ↦ (mem_adjoinFilter _ _ _ _).mpr (Or.inl hY)

theorem ProperSetFilter.mem_adjoin_iff {K F : V} (hF : ProperSetFilter K F) (X Y : V) :
    Y ∈ adjoinFilter K F X ↔ Y ⊆ K ∧ ∃ Z ∈ F, Z ∩ X ⊆ Y := by
  rw [mem_adjoinFilter]
  constructor
  · rintro (hY | hY)
    · exact ⟨mem_power_iff.mp (hF.1 _ hY), Y, hY,
        fun z hz ↦ (mem_inter_iff.mp hz).1⟩
    · exact hY
  · exact Or.inr

theorem ProperSetFilter.adjoin {K F X : V} (hF : ProperSetFilter K F)
    (hcomp : relativeComplement K X ∉ F) :
    ProperSetFilter K (adjoinFilter K F X) := by
  refine ⟨fun Y hY ↦ mem_power_iff.mpr ((hF.mem_adjoin_iff X Y).mp hY).1,
    subset_adjoinFilter _ _ _ _ hF.2.1, ?_, ?_, ?_⟩
  · intro he
    obtain ⟨_, Z, hZ, hZX⟩ := (hF.mem_adjoin_iff X ∅).mp he
    apply hcomp
    apply hF.2.2.2.1 Z hZ _ (fun z hz ↦ (mem_relativeComplement_iff _ _ _).mp hz |>.1)
    intro z hz
    refine (mem_relativeComplement_iff _ _ _).mpr
      ⟨mem_power_iff.mp (hF.1 _ hZ) _ hz, fun hzX ↦ ?_⟩
    exact not_mem_empty (hZX _ (mem_inter_iff.mpr ⟨hz, hzX⟩))
  · intro Y hY W hWK hYW
    obtain ⟨_, Z, hZ, hZY⟩ := (hF.mem_adjoin_iff X Y).mp hY
    exact (hF.mem_adjoin_iff X W).mpr ⟨hWK, Z, hZ, subset_trans hZY hYW⟩
  · intro Y hY W hW
    obtain ⟨hYK, Z, hZ, hZY⟩ := (hF.mem_adjoin_iff X Y).mp hY
    obtain ⟨hWK, A, hA, hAW⟩ := (hF.mem_adjoin_iff X W).mp hW
    apply (hF.mem_adjoin_iff X (Y ∩ W)).mpr
    refine ⟨fun z hz ↦ hYK _ (mem_inter_iff.mp hz).1,
      Z ∩ A, hF.2.2.2.2 Z hZ A hA, ?_⟩
    intro z hz
    obtain ⟨hzZA, hzX⟩ := mem_inter_iff.mp hz
    obtain ⟨hzZ, hzA⟩ := mem_inter_iff.mp hzZA
    exact mem_inter_iff.mpr ⟨hZY _ (mem_inter_iff.mpr ⟨hzZ, hzX⟩),
      hAW _ (mem_inter_iff.mpr ⟨hzA, hzX⟩)⟩

theorem ProperSetFilter.adjoin_mem {K F X : V} (hF : ProperSetFilter K F)
    (hX : X ⊆ K) : X ∈ adjoinFilter K F X :=
  (hF.mem_adjoin_iff X X).mpr ⟨hX, K, hF.2.1,
    fun _ hz ↦ (mem_inter_iff.mp hz).2⟩

noncomputable def filterIndexSet (K e ξ : V) : V := ⋃ˢ {X ∈ ℘ K ; e ‘ X = ξ}

instance filterIndexSet_definable : ℒₛₑₜ-function₃[V] filterIndexSet := by
  have h : ℒₛₑₜ-relation₄[V] (fun Y K e ξ ↦ ∀ z,
      z ∈ Y ↔ ∃ X ∈ ℘ K, e ‘ X = ξ ∧ z ∈ X) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [filterIndexSet, mem_sUnion_iff, mem_sep_iff]
  aesop

theorem filterIndexSet_subset (K e ξ : V) : filterIndexSet K e ξ ⊆ K := by
  intro z hz
  obtain ⟨X, hX, hzX⟩ := mem_sUnion_iff.mp hz
  exact mem_power_iff.mp (mem_sep_iff.mp hX).1 _ hzX

theorem filterIndexSet_eq {K e X : V} (hX : X ⊆ K)
    (hinj : ∀ X ∈ ℘ K, ∀ Y ∈ ℘ K, e ‘ X = e ‘ Y → X = Y) :
    filterIndexSet K e (e ‘ X) = X := by
  ext z
  constructor
  · intro hz
    obtain ⟨Y, hY, hzY⟩ := mem_sUnion_iff.mp hz
    obtain ⟨hYK, he⟩ := mem_sep_iff.mp hY
    exact hinj Y hYK X (mem_power_iff.mpr hX) he ▸ hzY
  · intro hz
    exact mem_sUnion_iff.mpr ⟨X, mem_sep_iff.mpr ⟨mem_power_iff.mpr hX, rfl⟩, hz⟩

noncomputable def filterStep (K F e f : V) : V :=
  let B := F ∪ ⋃ˢ range f
  let X := filterIndexSet K e (domain f)
  if relativeComplement K X ∈ B then B else adjoinFilter K B X

instance filterStep_definable (K F e : V) : ℒₛₑₜ-function₁[V] (filterStep K F e) := by
  classical
  have h : ℒₛₑₜ-relation[V] (fun U f ↦
      (relativeComplement K (filterIndexSet K e (domain f)) ∈ F ∪ ⋃ˢ range f ∧
        U = F ∪ ⋃ˢ range f) ∨
      (relativeComplement K (filterIndexSet K e (domain f)) ∉ F ∪ ⋃ˢ range f ∧
        U = adjoinFilter K (F ∪ ⋃ˢ range f) (filterIndexSet K e (domain f)))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = filterStep K F e (v 1) ↔ _
  dsimp only [filterStep]
  split <;> simp_all

noncomputable def filterStage (K F e ξ : V) : V :=
  Replacement.transfiniteRec (filterStep K F e) (filterStep_definable K F e) ξ

instance filterStage_definable (K F e : V) : ℒₛₑₜ-function₁[V] (filterStage K F e) :=
  Replacement.transfiniteRec_definable (filterStep_definable K F e)

noncomputable def filterPrevious (K F e ξ : V) : V :=
  F ∪ ⋃ˢ repl (filterStage K F e) (filterStage_definable K F e) ξ

theorem mem_filterPrevious (K F e ξ X : V) :
    X ∈ filterPrevious K F e ξ ↔ X ∈ F ∨ ∃ β ∈ ξ, X ∈ filterStage K F e β := by
  simp only [filterPrevious, mem_union_iff, mem_sUnion_iff, repl_spec]
  aesop

theorem filterStage_eq (K F e ξ : V) [IsOrdinal ξ] :
    filterStage K F e ξ =
      if relativeComplement K (filterIndexSet K e ξ) ∈ filterPrevious K F e ξ
      then filterPrevious K F e ξ
      else adjoinFilter K (filterPrevious K F e ξ) (filterIndexSet K e ξ) := by
  have hspec := Replacement.transfiniteRec_spec (filterStep K F e) (filterStep_definable K F e)
    (IsOrdinal.toOrdinal ξ)
  change filterStage K F e ξ = filterStep K F e
    (repl (fun β ↦ ⟨β, filterStage K F e β⟩ₖ) (by definability) ξ) at hspec
  rw [hspec]
  dsimp only [filterStep]
  rw [domain_pairGraph]
  have hB : F ∪ ⋃ˢ range (repl (fun β ↦ ⟨β, filterStage K F e β⟩ₖ) (by definability) ξ) =
      filterPrevious K F e ξ := by
    ext X
    simp only [mem_union_iff, mem_sUnion_range_pairGraph_iff, mem_filterPrevious]
  rw [hB]

theorem filterPrevious_subset_stage (K F e ξ : V) [IsOrdinal ξ] :
    filterPrevious K F e ξ ⊆ filterStage K F e ξ := by
  rw [filterStage_eq]
  split
  · exact subset_refl _
  · exact subset_adjoinFilter _ _ _

theorem filterStage_mono {K F e β ξ : V} [IsOrdinal ξ] (hβ : β ∈ ξ) :
    filterStage K F e β ⊆ filterStage K F e ξ := by
  intro X hX
  apply filterPrevious_subset_stage _ _ _ _ _
  exact (mem_filterPrevious _ _ _ _ _).mpr (Or.inr ⟨β, hβ, hX⟩)

theorem filterStage_extends (K F e ξ : V) [IsOrdinal ξ] : F ⊆ filterStage K F e ξ := by
  intro X hX
  exact filterPrevious_subset_stage _ _ _ _ _
    ((mem_filterPrevious _ _ _ _ _).mpr (Or.inl hX))

theorem filterPrevious_proper {K F e ξ : V} [IsOrdinal ξ] (hF : ProperSetFilter K F)
    (hprev : ∀ β ∈ ξ, ProperSetFilter K (filterStage K F e β)) :
    ProperSetFilter K (filterPrevious K F e ξ) := by
  have hin (X : V) (hX : X ∈ F) : X ∈ filterPrevious K F e ξ :=
    (mem_filterPrevious _ _ _ _ _).mpr (Or.inl hX)
  have hstage (β : V) (hβ : β ∈ ξ) (X : V) (hX : X ∈ filterStage K F e β) :
      X ∈ filterPrevious K F e ξ :=
    (mem_filterPrevious _ _ _ _ _).mpr (Or.inr ⟨β, hβ, hX⟩)
  refine ⟨?_, hin K hF.2.1, ?_, ?_, ?_⟩
  · intro X hX
    rcases (mem_filterPrevious _ _ _ _ _).mp hX with hX | ⟨β, hβ, hX⟩
    · exact hF.1 _ hX
    · exact (hprev β hβ).1 _ hX
  · intro he
    rcases (mem_filterPrevious _ _ _ _ _).mp he with he | ⟨β, hβ, he⟩
    · exact hF.2.2.1 he
    · exact (hprev β hβ).2.2.1 he
  · intro X hX Y hYK hXY
    rcases (mem_filterPrevious _ _ _ _ _).mp hX with hX | ⟨β, hβ, hX⟩
    · exact hin Y (hF.2.2.2.1 X hX Y hYK hXY)
    · exact hstage β hβ Y ((hprev β hβ).2.2.2.1 X hX Y hYK hXY)
  · intro X hX Y hY
    rcases (mem_filterPrevious _ _ _ _ _).mp hX with hX | ⟨β, hβ, hX⟩ <;>
      rcases (mem_filterPrevious _ _ _ _ _).mp hY with hY | ⟨γ, hγ, hY⟩
    · exact hin _ (hF.2.2.2.2 X hX Y hY)
    · have : IsOrdinal γ := IsOrdinal.of_mem hγ
      exact hstage γ hγ _ ((hprev γ hγ).2.2.2.2 X
        (filterStage_extends _ _ _ _ _ hX) Y hY)
    · have : IsOrdinal β := IsOrdinal.of_mem hβ
      exact hstage β hβ _ ((hprev β hβ).2.2.2.2 X hX Y
        (filterStage_extends _ _ _ _ _ hY))
    · have : IsOrdinal β := IsOrdinal.of_mem hβ
      have : IsOrdinal γ := IsOrdinal.of_mem hγ
      rcases IsOrdinal.subset_or_supset (α := β) (β := γ) with h | h
      · have hX' : X ∈ filterStage K F e γ := by
          rcases IsOrdinal.subset_iff.mp h with rfl | h
          · exact hX
          · exact filterStage_mono h _ hX
        exact hstage γ hγ _ ((hprev γ hγ).2.2.2.2 X hX' Y hY)
      · have hY' : Y ∈ filterStage K F e β := by
          rcases IsOrdinal.subset_iff.mp h with rfl | h
          · exact hY
          · exact filterStage_mono h _ hY
        exact hstage β hβ _ ((hprev β hβ).2.2.2.2 X hX Y hY')

theorem filterStage_proper {K F : V} (hF : ProperSetFilter K F) (e ξ : V) [IsOrdinal ξ] :
    ProperSetFilter K (filterStage K F e ξ) := by
  have key : ∀ α : Ordinal V, ProperSetFilter K (filterStage K F e (α : V)) := by
    apply transfinite_induction (fun ξ ↦ ProperSetFilter K (filterStage K F e ξ)) (by definability)
    intro α ih
    have hB : ProperSetFilter K (filterPrevious K F e (α : V)) := by
      apply filterPrevious_proper hF
      intro β hβ
      have : IsOrdinal β := IsOrdinal.of_mem hβ
      exact ih (IsOrdinal.toOrdinal β) (Ordinal.lt_def.mpr hβ)
    rw [filterStage_eq]
    split
    · exact hB
    · next hcomp => exact hB.adjoin hcomp
  exact key (IsOrdinal.toOrdinal ξ)

theorem filterStage_ultrafilter {K F e α : V} [IsOrdinal α] (hF : ProperSetFilter K F)
    (he : ∀ X ∈ ℘ K, e ‘ X ∈ α)
    (hinj : ∀ X ∈ ℘ K, ∀ Y ∈ ℘ K, e ‘ X = e ‘ Y → X = Y) :
    IsSetUltrafilter K (filterStage K F e α) := by
  obtain ⟨hsub, hK, hempty, hup, hinter⟩ := filterStage_proper hF e α
  refine ⟨hsub, hK, hempty, hup, hinter, fun X hX ↦ ?_⟩
  have hξα := he X (mem_power_iff.mpr hX)
  have : IsOrdinal (e ‘ X) := IsOrdinal.of_mem hξα
  have hdec : X ∈ filterStage K F e (e ‘ X) ∨
      relativeComplement K X ∈ filterStage K F e (e ‘ X) := by
    rw [filterStage_eq, filterIndexSet_eq hX hinj]
    split
    · next hc => exact Or.inr hc
    · have hB := filterPrevious_proper hF
        (fun β (_ : β ∈ e ‘ X) ↦ by
          have : IsOrdinal β := IsOrdinal.of_mem ‹β ∈ e ‘ X›
          exact filterStage_proper hF e β)
      exact Or.inl (hB.adjoin_mem hX)
  exact hdec.imp (filterStage_mono hξα _) (filterStage_mono hξα _)

/-- The ultrafilter extension theorem inside the model; only the power set of
the base needs to be well-orderable. -/
theorem exists_internal_ultrafilter_extension {K F : V} (hF : ProperSetFilter K F)
    (hwo : IsWellOrderable (℘ K)) : ∃ U : V, IsSetUltrafilter K U ∧ F ⊆ U := by
  obtain ⟨α, hα, e, he, hinj⟩ := (wellOrderable_iff_cardLE_ordinal (℘ K)).mp hwo
  have := hα
  let := IsFunction.of_mem he
  have hinj' : ∀ X ∈ ℘ K, ∀ Y ∈ ℘ K, e ‘ X = e ‘ Y → X = Y := by
    intro X hX Y hY heq
    exact injective_value_eq he hinj hX hY heq
  exact ⟨filterStage K F e α,
    filterStage_ultrafilter hF (fun X hX ↦ function_value_mem he hX) hinj',
    filterStage_extends _ _ _ _⟩

noncomputable def internalCocountable (K : V) : V :=
  {X ∈ ℘ K ; IsInternallyCountable (relativeComplement K X)}

theorem mem_internalCocountable (K X : V) :
    X ∈ internalCocountable K ↔ X ⊆ K ∧ IsInternallyCountable (relativeComplement K X) := by
  simp [internalCocountable]

instance internalCocountable_definable : ℒₛₑₜ-function₁[V] internalCocountable := by
  have h : ℒₛₑₜ-relation[V] (fun F K ↦ ∀ X,
      X ∈ F ↔ X ⊆ K ∧ IsInternallyCountable (relativeComplement K X)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_internalCocountable]
  rfl

theorem internalCocountable_proper {K : V} (hK : ¬ IsInternallyCountable K) :
    ProperSetFilter K (internalCocountable K) := by
  refine ⟨fun X hX ↦ mem_power_iff.mpr ((mem_internalCocountable _ _).mp hX).1, ?_, ?_, ?_, ?_⟩
  · apply (mem_internalCocountable K K).mpr
    refine ⟨subset_refl _, ?_⟩
    have he : relativeComplement K K = ∅ := by ext z; simp
    rw [he]
    exact internallyCountable_empty
  · intro he
    have hc := (mem_internalCocountable K ∅).mp he |>.2
    have heq : relativeComplement K ∅ = K := by ext z; simp
    exact hK (heq ▸ hc)
  · intro X hX Y hYK hXY
    apply (mem_internalCocountable K Y).mpr
    refine ⟨hYK, internallyCountable_subset ((mem_internalCocountable K X).mp hX).2 ?_⟩
    intro z hz
    obtain ⟨hzK, hzY⟩ := (mem_relativeComplement_iff _ _ _).mp hz
    exact (mem_relativeComplement_iff _ _ _).mpr ⟨hzK, fun hzX ↦ hzY (hXY _ hzX)⟩
  · intro X hX Y hY
    obtain ⟨hXK, hcX⟩ := (mem_internalCocountable K X).mp hX
    obtain ⟨_, hcY⟩ := (mem_internalCocountable K Y).mp hY
    apply (mem_internalCocountable K (X ∩ Y)).mpr
    refine ⟨fun z hz ↦ hXK _ (mem_inter_iff.mp hz).1,
      internallyCountable_subset (internallyCountable_union hcX hcY) ?_⟩
    intro z hz
    obtain ⟨hzK, hzXY⟩ := (mem_relativeComplement_iff _ _ _).mp hz
    apply mem_union_iff.mpr
    by_cases hzX : z ∈ X
    · exact Or.inr ((mem_relativeComplement_iff _ _ _).mpr
        ⟨hzK, fun hzY ↦ hzXY (mem_inter_iff.mpr ⟨hzX, hzY⟩)⟩)
    · exact Or.inl ((mem_relativeComplement_iff _ _ _).mpr ⟨hzK, hzX⟩)

/-- An internally uncountable well-orderable power set admits an internal
ultrafilter containing the complement of every internally countable subset. -/
theorem exists_internal_cocountable_ultrafilter {K : V}
    (hK : ¬ IsInternallyCountable K) (hwo : IsWellOrderable (℘ K)) :
    ∃ U : V, IsSetUltrafilter K U ∧
      ∀ X, X ⊆ K → IsInternallyCountable X → relativeComplement K X ∈ U := by
  obtain ⟨U, hU, hFU⟩ := exists_internal_ultrafilter_extension (internalCocountable_proper hK) hwo
  refine ⟨U, hU, fun X _ hcX ↦ hFU _ ?_⟩
  apply (mem_internalCocountable _ _).mpr
  refine ⟨fun z hz ↦ (mem_relativeComplement_iff _ _ _).mp hz |>.1,
    internallyCountable_subset hcX ?_⟩
  intro z hz
  obtain ⟨hzK, hzC⟩ := (mem_relativeComplement_iff _ _ _).mp hz
  by_contra hzX
  exact hzC ((mem_relativeComplement_iff _ _ _).mpr ⟨hzK, hzX⟩)

end ZFVP.Schmerl
