import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.ModelTheory.ForcingLowRankAssignments
import ZFVP.ModelTheory.ReflectedPairWitnessTable
import ZFVP.SetTheory.TwoStepForcing

/-! A ground witness table puts names for function values inside an elementary hull. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingFunctionValueTable (P R F B C : V) : V :=
  {w ∈ (P ×ˢ B) ×ˢ C ; kpair.π₁ (kpair.π₁ w) ∈ forcingFormula P R functionValueFormula
    (standardTuple ![F, kpair.π₂ (kpair.π₁ w), kpair.π₂ w])}

instance forcingFunctionValueTable_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingFunctionValueTable (V := V)) := by
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 6 → V ↦ ∀ w,
      w ∈ v 0 ↔ w ∈ (v 1 ×ˢ v 4) ×ˢ v 5 ∧ kpair.π₁ (kpair.π₁ w) ∈
        forcingFormula (v 1) (v 2) functionValueFormula
          (standardTuple ![v 3, kpair.π₂ (kpair.π₁ w), kpair.π₂ w])) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional
    · definability
    · apply Language.Definable.and
      · definability
      · apply Language.DefinableRel₄.comp
          (P := fun p P R v ↦ p ∈ forcingFormula P R functionValueFormula v)
        · definability
        · definability
        · definability
        · simp only [standardTuple]
          definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingFunctionValueTable (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [forcingFunctionValueTable, mem_sep_iff]

theorem pair_mem_forcingFunctionValueTable (P R F B C p b a : V) :
    ⟨⟨p, b⟩ₖ, a⟩ₖ ∈ forcingFunctionValueTable P R F B C ↔
      p ∈ P ∧ b ∈ B ∧ a ∈ C ∧
        p ∈ forcingFormula P R functionValueFormula (standardTuple ![F, b, a]) := by
  simp [forcingFunctionValueTable, and_assoc]

theorem ForcingContext.range_subset_hull_evaluation (A : ForcingContext V)
    (F : ForcingName A.P) {B C Z U : V}
    (hB : ∀ b ∈ B, IsForcingName A.P b) (hC : ∀ a ∈ C, IsForcingName A.P a)
    [IsTransitive U] (hZ : IsElementaryInclusion Z U)
    (htable : forcingFunctionValueTable A.P A.R F.val B C ∈ Z)
    (hPZ : A.P ⊆ Z) (hBZ : B ⊆ Z)
    [IsFunction (A.ofName F)]
    (hdom : domain (A.ofName F) ⊆ range (A.evaluationGraph B hB))
    (hran : range (A.ofName F) ⊆ range (A.evaluationGraph C hC)) :
    range (A.ofName F) ⊆ range (A.evaluationGraph (Z ∩ C)
      (fun a ha ↦ hC a (mem_inter_iff.mp ha).2)) := by
  intro y hy
  obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
  obtain ⟨b, hb, hxb⟩ := (A.mem_range_evaluationGraph_iff B hB x).mp
    (hdom x (mem_domain_of_kpair_mem hxy))
  obtain ⟨a, ha, hya⟩ := (A.mem_range_evaluationGraph_iff C hC y).mp (hran y hy)
  let bN : ForcingName A.P := ⟨b, hB b hb⟩
  let aN : ForcingName A.P := ⟨a, hC a ha⟩
  have hvalue : (A.ofName F) ‘ (A.ofName bN) = A.ofName aN := by
    simpa only [hxb, hya] using value_eq_of_kpair_mem hxy
  have htruth : functionValueFormula.Evalb
      (fun j ↦ A.ofName ((![F, bN, aN] : Fin 3 → ForcingName A.P) j)) :=
    (eval_functionValueFormula _).mpr ⟨(show IsFunction (A.ofName F) from inferInstance), hvalue⟩
  obtain ⟨p, hpG, hp⟩ := (A.formula_truth functionValueFormula ![F, bN, aN]).mp htruth
  have hpP := A.generic.1.1 p hpG
  have hentry : ⟨⟨p, b⟩ₖ, a⟩ₖ ∈ forcingFunctionValueTable A.P A.R F.val B C := by
    apply (pair_mem_forcingFunctionValueTable _ _ _ _ _ _ _ _).mpr
    exact ⟨hpP, hb, ha, hp⟩
  have hkeyU : ⟨p, b⟩ₖ ∈ U :=
    (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hentry
      (hZ.subset _ htable))).1
  have hkeyZ := hZ.kpair_mem (hPZ p hpP) (hBZ b hb) hkeyU
  obtain ⟨a', ha'Z, ha'T⟩ := hZ.table_fiber_witness htable hkeyZ ⟨a, hentry⟩
  have ha' := (pair_mem_forcingFunctionValueTable _ _ _ _ _ _ _ _).mp ha'T
  let a'N : ForcingName A.P := ⟨a', hC a' ha'.2.2.1⟩
  have htruth' : functionValueFormula.Evalb
      (fun j ↦ A.ofName ((![F, bN, a'N] : Fin 3 → ForcingName A.P) j)) :=
    (A.formula_truth functionValueFormula ![F, bN, a'N]).mpr ⟨p, hpG, ha'.2.2.2⟩
  have hvalue' : (A.ofName F) ‘ (A.ofName bN) = A.ofName a'N :=
    ((eval_functionValueFormula _).mp htruth').2
  apply (A.mem_range_evaluationGraph_iff (Z ∩ C) _ y).mpr
  exact ⟨a', mem_inter_iff.mpr ⟨ha'Z, ha'.2.2.1⟩,
    hya.trans (hvalue.symm.trans hvalue')⟩

end ZFVP
