import ZFVP.ModelTheory.WoodinSuccessorBounds
import ZFVP.SetTheory.ForcingRelativeClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forces_dependentChoiceAt_of_below {P R one p κ α : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (hα : α ∈ κ)
    (hDC : p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one κ])) :
    p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName one α]) := by
  let cκ : ForcingName P := ⟨checkName one κ, checkName_isName htop.1 _⟩
  let cα : ForcingName P := ⟨checkName one α, checkName_isName htop.1 _⟩
  let φ : SetTheorySemisentence 2 :=
    (dependentChoiceBelowFormula.subst (fun _ ↦ .bvar 0)).and
      (nameMemberFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 2) i)))
  let ψ : SetTheorySemisentence 2 := dependentChoiceAtFormula.subst (fun _ ↦ .bvar 1)
  have hf : p ∈ forcingFormula P R φ (standardTuple ![cκ.val, cα.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_rename, forcingFormula_rename]
    refine ⟨hDC, ?_⟩
    have he : (fun i ↦ ![cκ.val, cα.val] ((![1, 0] : Fin 2 → Fin 2) i)) = ![cα.val, cκ.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    rw [he, forcingFormula_nameMember]
    exact (mem_atomicMembership_checkName_iff hR htop _ _ _).mpr ⟨hp, hα⟩
  have hh := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change (dependentChoiceBelowFormula.subst (fun _ ↦ .bvar (0 : Fin 2))).Evalb v ∧
      (nameMemberFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 2) i))).Evalb v at hv
    have h : (∀ a ∈ v 0, InternalDependentChoiceAt a) ∧ v 1 ∈ v 0 := by
      simpa [φ, Semiformula.eval_substs, nameMemberFormula] using hv
    simpa [ψ, Semiformula.eval_substs] using h.1 (v 1) h.2) hR htop hp ![cκ, cα] hf
  change p ∈ forcingFormula P R (dependentChoiceAtFormula.subst (fun _ ↦ .bvar (1 : Fin 2)))
    (standardTuple ![cκ.val, cα.val]) at hh
  rw [forcingFormula_rename] at hh
  exact hh

theorem woodinSuccessorAt_union_bound {P R one κ δ α p f : V}
    (hs : IsWoodinStage (woodinStageCode P R one κ))
    (hδ : IsWoodinPrefixCutoff P R one κ δ) (hp : p ∈ P) (hα : α ∈ κ)
    (hf : IsForcingDirectedFamily (woodinStagePoset (woodinSuccessorAt P R one κ δ))
      (woodinStageOrder (woodinSuccessorAt P R one κ δ)) α f)
    (hb : ∀ i ∈ α, ⟨p, kpair.π₁ (f ‘ i)⟩ₖ ∈ R) :
    twoStepUnionBound α p f ∈ woodinStagePoset (woodinSuccessorAt P R one κ δ) ∧
      ∀ i ∈ α, ⟨twoStepUnionBound α p f, f ‘ i⟩ₖ ∈
        woodinStageOrder (woodinSuccessorAt P R one κ δ) := by
  simp only [IsWoodinStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] at hs
  simp only [woodinSuccessorAt, woodinStagePoset_code, woodinStageOrder_code] at hf ⊢
  let := hδ.2.1.1
  have hcf : α ∈ internalCofinality δ := by
    rw [hδ.2.1.regular.2.2]
    exact IsOrdinal.toIsTransitive.mem_trans hα hδ.1
  exact saturatedWoodinPrefix_union_bound hs.1 hs.2.1 hp hα hcf
    (hδ.2.1.regular.2.1 ∅ (by simp)) (hs.2.2.2.1 p hp)
    (forces_dependentChoiceAt_of_below hs.1 hs.2.1 hp hα (hs.2.2.2.2 p hp)) hf hb

theorem woodinSuccessorAt_relativeDirectedClosedAt {P R one κ δ α : V}
    (hs : IsWoodinStage (woodinStageCode P R one κ))
    (hδ : IsWoodinPrefixCutoff P R one κ δ) (hα : α ∈ κ) :
    IsForcingRelativeDirectedClosedAt P R
      (woodinStagePoset (woodinSuccessorAt P R one κ δ))
      (woodinStageOrder (woodinSuccessorAt P R one κ δ))
      (twoStepProjection P R (saturatedWoodinPrefixPosetName P R one κ δ) ∅) α := by
  intro f hf p hp hb
  have hpb : ∀ i ∈ α, ⟨p, kpair.π₁ (f ‘ i)⟩ₖ ∈ R := by
    intro i hi
    have hfi := function_value_mem hf.1 hi
    simp only [woodinSuccessorAt, woodinStagePoset_code] at hfi
    simpa only [twoStepProjection_value hfi] using hb i hi
  obtain ⟨hq, hqb⟩ := woodinSuccessorAt_union_bound hs hδ hp hα hf hpb
  refine ⟨twoStepUnionBound α p f, hq, hqb, ?_⟩
  simp only [woodinSuccessorAt, woodinStagePoset_code] at hq
  rw [twoStepProjection_value hq]
  simp [twoStepUnionBound]

end ZFVP
