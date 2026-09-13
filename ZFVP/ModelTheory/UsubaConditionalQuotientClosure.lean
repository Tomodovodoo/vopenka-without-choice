import ZFVP.ModelTheory.UsubaBoundInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def conditionalSeparativeClosureFormula : SetTheorySemisentence 3 :=
  f“P R α. !dependentChoiceAtFormula α →
    ∃ S, !forcingSeparativeOrderFormula S P R ∧ !forcingClosedThroughFormula P S α”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

instance conditionalSeparativeClosureFormula_defined :
    Defined (fun v : Fin 3 → V ↦ InternalDependentChoiceAt (v 2) →
      IsForcingClosedThrough (v 0) (forcingSeparativeOrder (v 0) (v 1)) (v 2))
      conditionalSeparativeClosureFormula :=
  ⟨fun v ↦ by simp [conditionalSeparativeClosureFormula]⟩

def UsubaQuotientClosureAt (i j : V) : Prop :=
  ∀ α : V, IsOrdinal α → ∀ p ∈ (T).P i,
    p ∈ forcingFormula ((T).P i) ((T).R i) conditionalSeparativeClosureFormula
      (standardTuple ![projectionQuotientName ((T).P j) ((T).projection i j) ((T).top i),
        projectionQuotientOrderName ((T).R j) ((T).projection i j) ((T).top i), checkName ((T).top i) α])

attribute [local instance] DefinableForcingTower.P_definable DefinableForcingTower.R_definable
  DefinableForcingTower.top_definable DefinableForcingTower.projection_definable

instance usubaQuotientClosureAt_definable : ℒₛₑₜ-relation[V] (UsubaQuotientClosureAt (V := V)) := by
  unfold UsubaQuotientClosureAt
  apply Language.Definable.all
  apply Language.Definable.imp
  · definability
  · apply Language.Definable.all
    apply Language.Definable.imp
    · definability
    · apply Language.DefinableRel₄.comp
        (P := fun p P R v ↦ p ∈ forcingFormula P R conditionalSeparativeClosureFormula v)
      · definability
      · definability
      · definability
      · simp only [standardTuple]
        definability

theorem usubaQuotientClosureAt_semantics {i j α : V} [IsOrdinal i] [IsOrdinal j] [IsOrdinal α]
    (hij : i ⊆ j) (h : UsubaQuotientClosureAt i j)
    {G : Set V} (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G)
    (hDC : InternalDependentChoiceAt ((usubaStageContext i hG).check α)) :
    let A := usubaStageContext i hG
    IsForcingClosedThrough (A.projectionQuotient ((T).P j) ((T).projection i j))
      (forcingSeparativeOrder (A.projectionQuotient ((T).P j) ((T).projection i j))
        (A.projectionQuotientOrder ((T).P j) ((T).R j) ((T).projection i j))) (A.check α) := by
  let A := usubaStageContext i hG
  have hπ := ((T).splitProjection hij).projection
  have hS := (T).order j inferInstance
  let QN : ForcingName A.P := ⟨projectionQuotientName ((T).P j) ((T).projection i j) A.one,
    projectionQuotientName_isName A.top.1 hπ.maps⟩
  let SN : ForcingName A.P := ⟨projectionQuotientOrderName ((T).R j) ((T).projection i j) A.one,
    projectionQuotientOrderName_isName A.top.1 hπ.maps hS⟩
  obtain ⟨p, hp⟩ := hG.1.2.1
  have ht := (conditionalSeparativeClosureFormula_defined.iff _).mp
    ((A.formula_truth conditionalSeparativeClosureFormula
      ![QN, SN, ⟨checkName A.one α, checkName_isName A.top.1 α⟩]).mpr
        ⟨p, hp, h α inferInstance p (hG.1.1 p hp)⟩)
  change (InternalDependentChoiceAt (A.check α) →
    IsForcingClosedThrough (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN)) (A.check α)) at ht
  have hh := ht hDC
  rwa [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS] at hh

theorem usubaQuotientClosureAt_of_generics [Countable V] {i j : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j)
    (hc : ∀ (G : Set V) (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G)
      (α : V), IsOrdinal α → InternalDependentChoiceAt ((usubaStageContext i hG).check α) →
      let A := usubaStageContext i hG
      IsForcingClosedThrough (A.projectionQuotient ((T).P j) ((T).projection i j))
        (forcingSeparativeOrder (A.projectionQuotient ((T).P j) ((T).projection i j))
          (A.projectionQuotientOrder ((T).P j) ((T).R j) ((T).projection i j))) (A.check α)) :
    UsubaQuotientClosureAt i j := by
  have hπ := ((T).splitProjection hij).projection
  have hS := (T).order j inferInstance
  have ho := (T).top_spec i inferInstance
  let QN : ForcingName ((T).P i) := ⟨projectionQuotientName ((T).P j) ((T).projection i j) ((T).top i),
    projectionQuotientName_isName ho.1 hπ.maps⟩
  let SN : ForcingName ((T).P i) := ⟨projectionQuotientOrderName ((T).R j) ((T).projection i j) ((T).top i),
    projectionQuotientOrderName_isName ho.1 hπ.maps hS⟩
  intro α hα
  apply (all_forces_iff_all_generics ((T).order i inferInstance) ho conditionalSeparativeClosureFormula
    ![QN, SN, ⟨checkName ((T).top i) α, checkName_isName ho.1 α⟩]).mpr
  intro G hG
  let A := usubaStageContext i hG
  change ForcingName A.P at QN SN
  apply (conditionalSeparativeClosureFormula_defined.iff _).mpr
  change InternalDependentChoiceAt (A.check α) →
    IsForcingClosedThrough (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN)) (A.check α)
  have hqv : A.ofName QN = A.projectionQuotient ((T).P j) ((T).projection i j) :=
    A.ofName_projectionQuotient hπ.maps
  have hsv : A.ofName SN = A.projectionQuotientOrder ((T).P j) ((T).R j) ((T).projection i j) :=
    A.ofName_projectionQuotientOrder hπ hS
  rw [hqv, hsv]
  exact hc G hG α hα

end ZFVP
