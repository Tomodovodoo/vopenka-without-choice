import ZFVP.ModelTheory.ClassForcingGenericRefinement
import ZFVP.ModelTheory.ClassForcingBoundedReduction
import ZFVP.ModelTheory.ProjectionQuotientSequenceForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedDenseQuotientCoverFormula : SetTheorySemisentence 6 :=
  f“Q R I F E p. ∃ S, !forcingSeparativeOrderFormula S Q R ∧
    ∀ a ∈ I, ∃ d ∈ !value.dfn F a, !kpair.dfn p (!value.dfn E d) ∈ S”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def HasBoundedDenseQuotientCover (Q R I F E p : V) : Prop :=
  ∀ a ∈ I, ∃ d ∈ F ‘ a, ⟨p, E ‘ d⟩ₖ ∈ forcingSeparativeOrder Q R

instance boundedDenseQuotientCoverFormula_defined :
    Defined (fun v : Fin 6 → V ↦ HasBoundedDenseQuotientCover
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) boundedDenseQuotientCoverFormula :=
  ⟨fun v ↦ by simp [boundedDenseQuotientCoverFormula, HasBoundedDenseQuotientCover]⟩

namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

theorem boundedDenseFamily_cover_iff (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    {I i k p : V} [IsOrdinal i] [IsOrdinal k]
    {G : Set V} (hG : IsExternalForcingGeneric (T.P i) (T.R i) G) :
    let A := T.genericStageContext i hG
    HasBoundedDenseQuotientCover
      (A.projectionQuotient (T.P k) (T.projection i k))
      (A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k))
      (A.check I) (A.check (T.boundedDenseFamily D hDdef I k))
      (A.check (T.boundedReduction k)) (A.check p) ↔
    ∀ a ∈ I, ∃ d ∈ T.boundedConditions k, D a d ∧
      ⟨A.check p, A.check (T.reduceCondition k d)⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient (T.P k) (T.projection i k))
          (A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k)) := by
  let A := T.genericStageContext i hG
  let F := T.boundedDenseFamily D hDdef I k
  let E := T.boundedReduction k
  have hf : F ∈ (℘ (T.boundedConditions k)) ^ I := T.boundedDenseFamily_function D hDdef I k
  have he : E ∈ (T.P k) ^ (T.boundedConditions k) := T.boundedReduction_maps k
  let := IsFunction.of_mem hf
  let := IsFunction.of_mem he
  dsimp only
  constructor
  · intro h a ha
    obtain ⟨d, hd, hpd⟩ := h (A.check a) ((A.check_mem_iff _ _).mpr ha)
    change d ∈ (A.check F) ‘ (A.check a) at hd
    rw [A.check_value ((domain_eq_of_mem_function hf).symm ▸ ha)] at hd
    obtain ⟨c, hc, rfl⟩ := (A.mem_check_iff _ _).mp hd
    obtain ⟨hck, hDc⟩ := (T.mem_boundedDenseFamily D hDdef ha c).mp hc
    refine ⟨c, hck, hDc, ?_⟩
    change ⟨A.check p, (A.check E) ‘ (A.check c)⟩ₖ ∈ _ at hpd
    rw [A.check_value ((domain_eq_of_mem_function he).symm ▸ hck), T.boundedReduction_value hck] at hpd
    exact hpd
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := (A.mem_check_iff _ _).mp ha
    obtain ⟨d, hdk, hDd, hpd⟩ := h b hb
    refine ⟨A.check d, ?_, ?_⟩
    · change A.check d ∈ (A.check F) ‘ (A.check b)
      rw [A.check_value ((domain_eq_of_mem_function hf).symm ▸ hb), A.check_mem_iff]
      exact (T.mem_boundedDenseFamily D hDdef hb d).mpr ⟨hdk, hDd⟩
    · change ⟨A.check p, (A.check E) ‘ (A.check d)⟩ₖ ∈ _
      rw [A.check_value ((domain_eq_of_mem_function he).symm ▸ hdk), T.boundedReduction_value hdk]
      exact hpd

/-- Truth of the cover statement is captured by one forcing condition. All
family and reduction parameters are check names for ground sets. -/
theorem boundedDenseFamily_uniform_cover (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    {I i k p : V} [IsOrdinal i] [IsOrdinal k] (hik : i ⊆ k)
    {G : Set V} (hG : IsExternalForcingGeneric (T.P i) (T.R i) G)
    (hcover : let A := T.genericStageContext i hG
      HasBoundedDenseQuotientCover
        (A.projectionQuotient (T.P k) (T.projection i k))
        (A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k))
        (A.check I) (A.check (T.boundedDenseFamily D hDdef I k))
        (A.check (T.boundedReduction k)) (A.check p)) :
    ∃ u ∈ G, ∀ (H : Set V) (hH : IsExternalForcingGeneric (T.P i) (T.R i) H),
      u ∈ H → ∀ a ∈ I,
      let B := T.genericStageContext i hH
      ∃ d ∈ T.boundedConditions k, D a d ∧
        ⟨B.check p, B.check (T.reduceCondition k d)⟩ₖ ∈
          forcingSeparativeOrder (B.projectionQuotient (T.P k) (T.projection i k))
            (B.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k)) := by
  let A := T.genericStageContext i hG
  have hπ := (T.splitProjection hik).projection
  have hR := T.order k inferInstance
  let QN : ForcingName (T.P i) := ⟨projectionQuotientName (T.P k) (T.projection i k) (T.top i),
    projectionQuotientName_isName A.top.1 hπ.maps⟩
  let RN : ForcingName (T.P i) := ⟨projectionQuotientOrderName (T.R k) (T.projection i k) (T.top i),
    projectionQuotientOrderName_isName A.top.1 hπ.maps hR⟩
  let names : Fin 6 → ForcingName (T.P i) := ![QN, RN,
    ⟨checkName (T.top i) I, checkName_isName A.top.1 I⟩,
    ⟨checkName (T.top i) (T.boundedDenseFamily D hDdef I k), checkName_isName A.top.1 _⟩,
    ⟨checkName (T.top i) (T.boundedReduction k), checkName_isName A.top.1 _⟩,
    ⟨checkName (T.top i) p, checkName_isName A.top.1 p⟩]
  have ht : boundedDenseQuotientCoverFormula.Evalb (fun n ↦ A.ofName (names n)) := by
    change ForcingName A.P at QN RN
    apply (Defined.eval_iff _).mpr
    change HasBoundedDenseQuotientCover (A.ofName QN) (A.ofName RN) (A.check I)
      (A.check (T.boundedDenseFamily D hDdef I k)) (A.check (T.boundedReduction k)) (A.check p)
    have hqv : A.ofName QN = A.projectionQuotient (T.P k) (T.projection i k) :=
      A.ofName_projectionQuotient hπ.maps
    have hrv : A.ofName RN = A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k) :=
      A.ofName_projectionQuotientOrder hπ hR
    rw [hqv, hrv]
    exact hcover
  obtain ⟨u, huG, huf⟩ := (A.formula_truth boundedDenseQuotientCoverFormula names).mp ht
  refine ⟨u, huG, ?_⟩
  intro H hH huH
  let B := T.genericStageContext i hH
  have hb := (Defined.eval_iff _).mp
    ((B.formula_truth boundedDenseQuotientCoverFormula names).mpr ⟨u, huH, huf⟩)
  change ForcingName B.P at QN RN
  change HasBoundedDenseQuotientCover (B.ofName QN) (B.ofName RN) (B.check I)
    (B.check (T.boundedDenseFamily D hDdef I k)) (B.check (T.boundedReduction k)) (B.check p) at hb
  have hqv : B.ofName QN = B.projectionQuotient (T.P k) (T.projection i k) :=
    B.ofName_projectionQuotient hπ.maps
  have hrv : B.ofName RN = B.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k) :=
    B.ofName_projectionQuotientOrder hπ hR
  rw [hqv, hrv] at hb
  exact (T.boundedDenseFamily_cover_iff D hDdef hH).mp hb

/-- A cover in one base generic yields an actual ground condition and
predense refinements below it. The output still projects into that generic. -/
theorem boundedDenseFamily_refinement_of_cover [Countable V]
    (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    {I i k p : V} [IsOrdinal i] [IsOrdinal k] (hik : i ⊆ k) (hp : p ∈ T.P k)
    {G : Set V} (hG : IsExternalForcingGeneric (T.P i) (T.R i) G)
    (hpG : (T.projection i k) ‘ p ∈ G)
    (hcover : let A := T.genericStageContext i hG
      HasBoundedDenseQuotientCover
        (A.projectionQuotient (T.P k) (T.projection i k))
        (A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k))
        (A.check I) (A.check (T.boundedDenseFamily D hDdef I k))
        (A.check (T.boundedReduction k)) (A.check p)) :
    ∃ r ∈ T.P k, ⟨r, p⟩ₖ ∈ T.R k ∧ (T.projection i k) ‘ r ∈ G ∧
      T.ClassDenseRefinements D I ⟨k, r⟩ₖ (T.boundedDenseFamily D hDdef I k) := by
  obtain ⟨u, huG, hsem⟩ := T.boundedDenseFamily_uniform_cover D hDdef hik hG hcover
  obtain ⟨v, hvG, hvu, hvp⟩ := hG.1.2.2.2 u huG _ hpG
  have hu := hG.1.1 u huG
  have hv := hG.1.1 v hvG
  obtain ⟨r, hr, hrp, hrv⟩ := T.lift i k inferInstance inferInstance hik p hp v hv hvp
  have hrc : T.Condition ⟨k, r⟩ₖ := (T.condition_pair k r).mpr ⟨inferInstance, hr⟩
  have hrpt : T.LE ⟨k, r⟩ₖ ⟨k, p⟩ₖ := (T.le_sameStage_iff hr hp).mpr hrp
  have hru : T.LE ⟨k, r⟩ₖ ⟨i, u⟩ₖ := by
    apply T.le_trans ?_ (T.section_equivalent hik hu).2
    apply (T.le_sameStage_iff hr (T.section_mem hik hu)).mpr
    apply (T.below_section i k inferInstance inferInstance hik r hr u hu).mpr
    rwa [hrv]
  exact ⟨r, hr, hrp, hrv.symm ▸ hvG,
    T.boundedDenseFamily_refinement_of_generics D hDdef hik hp hu hrpt hru hsem⟩

theorem classDenseRefinements_mono {D : V → V → Prop} {I p q F : V}
    (h : T.ClassDenseRefinements D I p F) (hqp : T.LE q p) :
    T.ClassDenseRefinements D I q F := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro a ha
  obtain ⟨hD, hC, hpred⟩ := h.2.2 a ha
  exact ⟨hD, hC, fun r hr hrq ↦ hpred r hr (T.le_trans hrq hqp)⟩

/-- The final bound may initially lie below the starting condition only in
the separative quotient order. Compatibility supplies a literal stronger
class condition, and predensity persists below that condition. -/
theorem boundedDenseFamily_refinement_below_initial [Countable V]
    (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    {I i k p c : V} [IsOrdinal i] [IsOrdinal k] (hik : i ⊆ k)
    (hp : p ∈ T.P k) (hc : c ∈ T.boundedConditions k)
    {G : Set V} (hG : IsExternalForcingGeneric (T.P i) (T.R i) G)
    (hpG : (T.projection i k) ‘ p ∈ G)
    (hpc : let A := T.genericStageContext i hG
      ⟨A.check p, A.check (T.reduceCondition k c)⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient (T.P k) (T.projection i k))
          (A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k)))
    (hcover : let A := T.genericStageContext i hG
      HasBoundedDenseQuotientCover
        (A.projectionQuotient (T.P k) (T.projection i k))
        (A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k))
        (A.check I) (A.check (T.boundedDenseFamily D hDdef I k))
        (A.check (T.boundedReduction k)) (A.check p)) :
    ∃ s, T.Condition s ∧ T.LE s c ∧
      T.ClassDenseRefinements D I s (T.boundedDenseFamily D hDdef I k) := by
  obtain ⟨r, hr, hrp, hrG, hF⟩ :=
    T.boundedDenseFamily_refinement_of_cover D hDdef hik hp hG hpG hcover
  let A := T.genericStageContext i hG
  have hrc : T.Condition ⟨k, r⟩ₖ := (T.condition_pair k r).mpr ⟨inferInstance, hr⟩
  have hrpt : T.LE ⟨k, r⟩ₖ ⟨k, p⟩ₖ := (T.le_sameStage_iff hr hp).mpr hrp
  have hprG : (T.projection i k) ‘ (T.projectCondition k ⟨k, r⟩ₖ) ∈ A.G := by
    rwa [T.projectCondition_self hr]
  obtain ⟨s, hs, hsr, hsc⟩ :=
    T.classCompatible_of_quotient_separative hik A rfl hrc hp hrpt hprG hpc
  exact ⟨s, hs, T.le_trans hsc (T.reduceCondition_equivalent hc).1,
    T.classDenseRefinements_mono hF hsr⟩

end DefinableForcingTower
end ZFVP
