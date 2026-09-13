import ZFVP.SetTheory.ClassForcingTower
import ZFVP.SetTheory.ForcingIterationRecursion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Compatible coded successor prefixes, as produced by the internal
transfinite recursion. -/
structure DefinableForcingCodeSequence where
  code : V → V
  definable : ℒₛₑₜ-function₁ code
  valid : ∀ i : V, IsOrdinal i → IsForcingIterationCode (succ i) (code i)
  coherence : ∀ i j : V, IsOrdinal i → IsOrdinal j → i ⊆ j →
    ForcingCodeExtends (code i) (code j)

namespace DefinableForcingCodeSequence

variable {V} (C : DefinableForcingCodeSequence V)

private theorem mem_succ_of_subset {i j : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) : i ∈ succ j :=
  mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)

private theorem table_value {A B f g x : V} (hf : IsIterationTable A f)
    (hg : IsIterationTable B g) (hfg : f ⊆ g) (hx : x ∈ A) : g ‘ x = f ‘ x := by
  have : IsFunction f := hf.function
  have : IsFunction g := hg.function
  exact value_eq_of_kpair_mem (hfg _ (kpair_value_mem (hf.domain_eq.symm ▸ hx)))

theorem P_at {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) :
    (forcingCodeP (C.code j)) ‘ i = (forcingCodeP (C.code i)) ‘ i :=
  table_value (C.valid i inferInstance).tableP (C.valid j inferInstance).tableP
    (C.coherence i j inferInstance inferInstance hij).subP (mem_succ_self i)

theorem R_at {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) :
    (forcingCodeR (C.code j)) ‘ i = (forcingCodeR (C.code i)) ‘ i :=
  table_value (C.valid i inferInstance).tableR (C.valid j inferInstance).tableR
    (C.coherence i j inferInstance inferInstance hij).subR (mem_succ_self i)

theorem top_at {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) :
    (forcingCodet (C.code j)) ‘ i = (forcingCodet (C.code i)) ‘ i :=
  table_value (C.valid i inferInstance).tablet (C.valid j inferInstance).tablet
    (C.coherence i j inferInstance inferInstance hij).subt (mem_succ_self i)

theorem section_at {i j k : V} [IsOrdinal i] [IsOrdinal j] [IsOrdinal k]
    (hij : i ⊆ j) (hjk : j ⊆ k) :
    (forcingCodeE (C.code k)) ‘ ⟨i, j⟩ₖ = (forcingCodeE (C.code j)) ‘ ⟨i, j⟩ₖ :=
  table_value (C.valid j inferInstance).tableE (C.valid k inferInstance).tableE
    (C.coherence j k inferInstance inferInstance hjk).subE
    (kpair_mem_iff.mpr ⟨mem_succ_of_subset hij, mem_succ_self j⟩)

theorem projection_at {i j k : V} [IsOrdinal i] [IsOrdinal j] [IsOrdinal k]
    (hij : i ⊆ j) (hjk : j ⊆ k) :
    (forcingCodeπ (C.code k)) ‘ ⟨i, j⟩ₖ = (forcingCodeπ (C.code j)) ‘ ⟨i, j⟩ₖ :=
  table_value (C.valid j inferInstance).tableπ (C.valid k inferInstance).tableπ
    (C.coherence j k inferInstance inferInstance hjk).subπ
    (kpair_mem_iff.mpr ⟨mem_succ_of_subset hij, mem_succ_self j⟩)

/-- The actual class tower read from the stable entries of the coded
iteration. All global laws follow from one sufficiently long prefix. -/
noncomputable def tower : DefinableForcingTower V where
  P := (fun i ↦ (forcingCodeP (C.code i)) ‘ i)
  R := (fun i ↦ (forcingCodeR (C.code i)) ‘ i)
  sectionMap := (fun i j ↦ (forcingCodeE (C.code j)) ‘ ⟨i, j⟩ₖ)
  projection := (fun i j ↦ (forcingCodeπ (C.code j)) ‘ ⟨i, j⟩ₖ)
  top := (fun i ↦ (forcingCodet (C.code i)) ‘ i)
  P_definable := by have := C.definable; definability
  R_definable := by have := C.definable; definability
  section_definable := by have := C.definable; definability
  projection_definable := by have := C.definable; definability
  top_definable := by have := C.definable; definability
  order := (fun i hi ↦ (C.valid i hi).system.order.preorder i (mem_succ_self i))
  top_spec := (fun i hi ↦ (C.valid i hi).system.tops.top i (mem_succ_self i))
  section_function := by
    intro i j hi hj hij
    have := hi
    have := hj
    simpa only [C.P_at hij] using
      (C.valid j hj).system.functions.sectionMap i (mem_succ_of_subset hij) j
        (mem_succ_self j) hij
  projection_function := by
    intro i j hi hj hij
    have := hi
    have := hj
    simpa only [C.P_at hij] using
      (C.valid j hj).system.functions.projection i (mem_succ_of_subset hij) j
        (mem_succ_self j) hij
  section_self := by
    intro i hi p hp
    exact (C.valid i hi).system.split.secId i (mem_succ_self i) p hp
  projection_self := by
    intro i hi p hp
    exact (C.valid i hi).system.split.projId (mem_succ_self i) hp
  section_comp := by
    intro i j k hi hj hk hij hjk p hp
    have := hi
    have := hj
    have := hk
    have hik : i ⊆ k := fun x hx ↦ hjk x (hij x hx)
    simpa only [C.P_at hik, C.section_at hij hjk] using
      (C.valid k hk).system.split.secComp i (mem_succ_of_subset hik) j
        (mem_succ_of_subset hjk) k (mem_succ_self k) hij hjk p ((C.P_at hik).symm ▸ hp)
  projection_comp := by
    intro i j k hi hj hk hij hjk p hp
    have := hi
    have := hj
    have := hk
    have hik : i ⊆ k := fun x hx ↦ hjk x (hij x hx)
    simpa only [C.projection_at hij hjk] using
      (C.valid k hk).system.split.projComp i (mem_succ_of_subset hik) j
        (mem_succ_of_subset hjk) k (mem_succ_self k) hij hjk p hp
  projection_section := by
    intro i j hi hj hij p hp
    have := hi
    have := hj
    exact (C.valid j hj).system.split.retraction i (mem_succ_of_subset hij) j
      (mem_succ_self j) hij p ((C.P_at hij).symm ▸ hp)
  projection_mono := by
    intro i j hi hj hij p hp q hq hpq
    have := hi
    have := hj
    simpa only [C.R_at hij] using
      (C.valid j hj).system.order.projMono i (mem_succ_of_subset hij) j
        (mem_succ_self j) hij p hp q hq hpq
  below_section := by
    intro i j hi hj hij p hp q hq
    have := hi
    have := hj
    simpa only [C.R_at hij] using
      (C.valid j hj).system.order.below i (mem_succ_of_subset hij) j
        (mem_succ_self j) hij p hp q ((C.P_at hij).symm ▸ hq)
  section_top := by
    intro i j hi hj hij
    have := hi
    have := hj
    simpa only [C.top_at hij] using
      (C.valid j hj).system.tops.secTop i (mem_succ_of_subset hij) j
        (mem_succ_self j) hij
  lift := by
    intro i j hi hj hij p hp q hq hqp
    have := hi
    have := hj
    obtain ⟨hr, hrp, he⟩ :=
      (C.valid j hj).system.lifts.lift i (mem_succ_of_subset hij) j
        (mem_succ_self j) hij p hp q ((C.P_at hij).symm ▸ hq) ((C.R_at hij).symm ▸ hqp)
    exact ⟨_, hr, hrp, he⟩

noncomputable def ofRecursion (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hstep : ∀ θ : V, IsOrdinal θ → ∀ H, IsForcingIterationHistory θ H →
      IsForcingIterationCode (succ θ) (F H) ∧
      ForcingCodeExtends (forcingIterationCodeUnion θ H) (F H)) :
    DefinableForcingCodeSequence V where
  code := Replacement.transfiniteRec F hF
  definable := Replacement.transfiniteRec_definable hF
  valid := by
    intro i hi
    have := hi
    exact (forcingIteration_recursion_invariant F hF hstep i).1
  coherence := by
    intro i j hi hj hij
    have := hi
    have := hj
    rcases IsOrdinal.subset_iff.mp hij with rfl | hij
    · exact ForcingCodeExtends.refl _
    · exact (forcingIteration_recursion_invariant F hF hstep j).2 i hij

end DefinableForcingCodeSequence
end ZFVP
