import ZFVP.ModelTheory.UsubaConditionalQuotientClosure
import ZFVP.ModelTheory.UsubaBoundCoordinates
import ZFVP.SetTheory.ForcingNegationCalculus

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

def ForcesUsubaDC (i p α : V) : Prop :=
  p ∈ forcingFormula ((T).P i) ((T).R i) dependentChoiceAtFormula
    (standardTuple ![checkName ((T).top i) α])

theorem forcesUsubaDC_semantics {i p α : V} [IsOrdinal i]
    (h : ForcesUsubaDC i p α) {G : Set V}
    (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G) (hpG : p ∈ G) :
    InternalDependentChoiceAt ((usubaStageContext i hG).check α) :=
  (Defined.eval_iff _).mp
    (((usubaStageContext i hG).checked_unary_truth dependentChoiceAtFormula α).mpr ⟨p, hpG, h⟩)

theorem usubaQuotientClosureAt_of_canonical_bounds [Countable V] {i j : V}
    [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j)
    (hbound : ∀ α : V, IsOrdinal α → ∀ p ∈ (T).P i, ∀ f : ForcingName ((T).P i),
      ForcesUsubaQuotientSequence j i p f.val α → ForcesUsubaDC i p α →
      IsUsubaQuotientBoundAt j i p f.val α j) : UsubaQuotientClosureAt i j := by
  apply usubaQuotientClosureAt_of_generics hij
  intro G hG α hα hDC
  let := hα
  let A := usubaStageContext i hG
  have hπ := ((T).splitProjection hij).projection
  have hR := (T).order i inferInstance
  have hS := (T).order j inferInstance
  dsimp only
  intro β hβ hβα z hz
  let := hβ
  have hβmem : β ∈ A.check (succ α) := by
    rw [A.check_succ]
    exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hβα)
  obtain ⟨γ, hγα, rfl⟩ := (A.mem_check_iff _ _).mp hβmem
  let := IsOrdinal.of_mem hγα
  have hdcγ := hDC.downward hβα
  obtain ⟨f, rfl⟩ := A.ofName_surjective z
  change ForcingName ((T).P i) at f
  let QN : ForcingName A.P := ⟨projectionQuotientName ((T).P j) ((T).projection i j) A.one,
    projectionQuotientName_isName A.top.1 hπ.maps⟩
  let SN : ForcingName A.P := ⟨projectionQuotientOrderName ((T).R j) ((T).projection i j) A.one,
    projectionQuotientOrderName_isName A.top.1 hπ.maps hS⟩
  have ht : forcingSeparativeDescendingFormula.Evalb
      (fun k ↦ A.ofName ((![QN, SN, ⟨checkName A.one γ, checkName_isName A.top.1 γ⟩, f] :
        Fin 4 → ForcingName A.P) k)) := by
    apply (Defined.eval_iff _).mpr
    change IsForcingDescending (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN))
      (A.check γ) (A.ofName f)
    rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS]
    exact hz
  obtain ⟨r, hrG, hrf⟩ := (A.formula_truth forcingSeparativeDescendingFormula
    ![QN, SN, ⟨checkName A.one γ, checkName_isName A.top.1 γ⟩, f]).mp ht
  obtain ⟨s, hsG, hsd⟩ := (A.checked_unary_truth dependentChoiceAtFormula γ).mp
    ((Defined.eval_iff _).mpr hdcγ)
  obtain ⟨p, hpG, hpr, hps⟩ := hG.1.2.2.2 r hrG s hsG
  have hp : p ∈ (T).P i := hG.1.1 p hpG
  have hpf : ForcesUsubaQuotientSequence j i p f.val γ := forcingFormula_mono hR hrf hp hpr
  have hpd : ForcesUsubaDC i p γ := forcingFormula_mono hR hsd hp hps
  have hb := ((usubaQuotientBoundAt_iff_generics hij hp f).mp
    (hbound γ inferInstance p hp f hpf hpd)).2 G hG hpG
  have he := usubaBoundCoordinate_self hG f (mem_function_of_mem_function_of_subset hz.1 sep_subset)
  refine ⟨A.check (usubaQuotientBoundRec j i p f.val j), hb.1, ?_⟩
  intro a ha
  exact (congrArg (fun z : A.Model ↦
    ⟨A.check (usubaQuotientBoundRec j i p f.val j), z ‘ a⟩ₖ ∈
      forcingSeparativeOrder (A.projectionQuotient ((T).P j) ((T).projection i j))
        (A.projectionQuotientOrder ((T).P j) ((T).R j) ((T).projection i j))) he).mp (hb.2 a ha)

end ZFVP
