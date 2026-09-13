import ZFVP.ModelTheory.ScottFunctionNames
import ZFVP.ModelTheory.ForcingExtensionZF
import ZFVP.ModelTheory.ForcingModelNameValue
import ZFVP.SetTheory.BoundedDomainRelativization
import ZFVP.SetTheory.DeltaOneForcingNames
import ZFVP.SetTheory.EndExtensionLevy
import ZFVP.ModelTheory.ForcingHierarchyCover
import ZFVP.SetTheory.FunctionComposition
import ZFVP.SetTheory.FunctionRestrictionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem TransitiveZF.functionRestrictionClosed (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : IsFunctionRestrictionClosed U := by
  intro D _ f hf hft d hd hsub
  let f' : SetDomain U := ⟨f, hf⟩
  let d' : SetDomain U := ⟨d, hd⟩
  have he := TransitiveZF.restrict_val U f' d'
  have hrU : f ↾ d ∈ U := he ▸ (f' ↾ d').property
  exact ⟨f ↾ d, hrU, function_restrict_mem hft hsub, restrict_subset _ _⟩

theorem TransitiveZF.rankFunctionClosed_on {U α D : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hc : U ^ hierarchy α ⊆ U) (hα : hierarchy α ∈ U) (hD : D ∈ U)
    (hsub : D ⊆ hierarchy α) : U ^ D ⊆ U := by
  intro f hf
  exact (TransitiveZF.functionRestrictionClosed U).function_mem hc hα hD hsub ⟨D, hD⟩ hf

theorem TransitiveZF.function_mem_of_cover {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    {D B E f : V} (hE : E ∈ B ^ D) (hr : range E = B) (hf : f ∈ U ^ B)
    (hEU : E ∈ U) (hhU : compose E f ∈ U) : f ∈ U := by
  let E' : SetDomain U := ⟨E, hEU⟩
  let h' : SetDomain U := ⟨compose E f, hhU⟩
  let F : SetDomain U := repl (fun x ↦ ⟨E' ‘ x, h' ‘ x⟩ₖ) (by definability) (domain E')
  have he : F.val = repl (fun x ↦ ⟨E ‘ x, (compose E f) ‘ x⟩ₖ) (by definability) (domain E) := by
    have hv := TransitiveZF.repl_val U (domain E') (fun x ↦ ⟨E' ‘ x, h' ‘ x⟩ₖ)
      (by definability) (fun x ↦ ⟨E ‘ x, (compose E f) ‘ x⟩ₖ) (by definability)
      (by intro x _; simp only [TransitiveZF.kpair_val U, TransitiveZF.value_val_total U]; rfl)
    simpa only [TransitiveZF.domain_val U] using hv
  have heq : F.val = f := by
    rw [he]
    let := IsFunction.of_mem hE
    let := IsFunction.of_mem hf
    apply mem_ext
    intro z
    rw [repl_spec]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxD : x ∈ D := (domain_eq_of_mem_function hE) ▸ hx
      rw [value_compose_of_mem_function hE hf hxD]
      exact kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ function_value_mem hE hxD)
    · intro hz
      obtain ⟨y, w, rfl⟩ := IsFunction.mem_eq_kpair hz
      have hy : y ∈ B := (mem_of_mem_functions hf hz).1
      obtain ⟨x, hxy⟩ := mem_range_iff.mp (hr.symm ▸ hy)
      have hxD := (mem_of_mem_functions hE hxy).1
      refine ⟨x, (domain_eq_of_mem_function hE).symm ▸ hxD, ?_⟩
      rw [value_compose_of_mem_function hE hf hxD, value_eq_of_kpair_mem hxy,
        value_eq_of_kpair_mem hz]
  exact heq ▸ F.property

namespace ForcingContext
variable (A : ForcingContext V)

instance checkDomain_nonempty (U : V) [Nonempty (SetDomain U)] :
    Nonempty (SetDomain (A.check U)) := by
  obtain ⟨x⟩ := ‹Nonempty (SetDomain U)›
  exact ⟨⟨A.check x.val, (A.check_mem_iff _ _).mpr x.property⟩⟩

theorem checkDomain_models_zf (U : V) [Nonempty (SetDomain U)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : (SetDomain (A.check U))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  let := A.checkDomain_nonempty U
  refine ⟨?_⟩
  intro φ hφ
  have hm := Theory.models (SetDomain U) 𝗭𝗙 hφ
  change φ.Evalb (![] : Fin 0 → SetDomain U) at hm
  have hb := (eval_boundedDomainSentenceFormula φ U).mpr hm
  have ht := (A.check_bounded (boundedDomainSentenceFormula_bounded φ) ![U]).mp hb
  have hv : (fun i ↦ A.check (![U] i)) = ![A.check U] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at ht
  exact (eval_boundedDomainSentenceFormula φ (A.check U)).mp ht

theorem check_transitive (U : V) [hU : IsTransitive U] : IsTransitive (A.check U) := by
  constructor
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := (A.mem_check_iff U x).mp hx
  obtain ⟨b, hb, rfl⟩ := (A.mem_check_iff a y).mp hy
  exact (A.check_mem_iff _ _).mpr (hU.mem_trans hb ha)

theorem checked_forcingName_iff (P τ : V) :
    IsForcingName (A.check P) (A.check τ) ↔ IsForcingName P τ := by
  exact (A.checkEmbedding.deltaOne_defined sigmaOneForcingNameFormula_sigmaOne
    piOneForcingNameFormula_piOne (fun v ↦ IsForcingName (v 0) (v 1))
    (fun v ↦ IsForcingName (v 0) (v 1)) ![P, τ]).symm

theorem genericSet_groundGeneric (U : V) :
    IsGroundForcingGeneric (A.check U) (A.check A.P) (A.check A.R) A.genericSet := by
  refine ⟨A.realization.filter, ?_⟩
  intro D hD hd
  obtain ⟨E, _, rfl⟩ := (A.mem_check_iff U D).mp hD
  have hE : ForcingDense A.P A.R E := by
    refine ⟨(A.checkEmbedding.subset_iff E A.P).mp hd.1, ?_⟩
    intro p hp
    obtain ⟨q, hq, hqp⟩ := hd.2 (A.check p) ((A.check_mem_iff _ _).mpr hp)
    obtain ⟨r, hr, rfl⟩ := (A.mem_check_iff E q).mp hq
    refine ⟨r, hr, ?_⟩
    rwa [← A.check_kpair, A.check_mem_iff] at hqp
  obtain ⟨p, hp, hpE⟩ := A.generic.2 E hE
  exact ⟨A.check p, (A.check_mem_genericSet_iff p).mpr hp, (A.check_mem_iff _ _).mpr hpE⟩

noncomputable def closedModelDomain (U : V) : A.Model :=
  forcingExtensionDomain (A.check U) (A.check A.P) A.genericSet

theorem mem_closedModelDomain (U : V) (x : A.Model) :
    x ∈ A.closedModelDomain U ↔ ∃ τ : ForcingName A.P, τ.val ∈ U ∧ x = A.ofName τ := by
  rw [closedModelDomain, mem_forcingExtensionDomain_iff]
  constructor
  · rintro ⟨σ, hσ, hn, he⟩
    obtain ⟨τ, hτ, rfl⟩ := (A.mem_check_iff U σ).mp hσ
    have hn' := (A.checked_forcingName_iff A.P τ).mp hn
    exact ⟨⟨τ, hn'⟩, hτ, he.trans (A.nameValue_genericSet_check ⟨τ, hn'⟩)⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨A.check τ.val, (A.check_mem_iff _ _).mpr hτ,
      (A.checked_forcingName_iff A.P τ.val).mpr τ.property, (A.nameValue_genericSet_check τ).symm⟩

theorem closedModelDomain_transitive (U : V) [IsTransitive U] :
    IsTransitive (A.closedModelDomain U) := by
  let := A.check_transitive U
  exact forcingExtensionDomain_transitive _ _ _

instance closedModelDomain_nonempty (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    Nonempty (SetDomain (A.closedModelDomain U)) := by
  have hzero : (∅ : V) ∈ U := TransitiveZF.empty_val U ▸ (∅ : SetDomain U).property
  exact ⟨⟨A.ofName ⟨∅, empty_forcingName A.P⟩,
    (A.mem_closedModelDomain U _).mpr ⟨⟨∅, empty_forcingName A.P⟩, hzero, rfl⟩⟩⟩

theorem closedModelDomain_models_zf {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hP : A.P ∈ U) (hR : A.R ∈ U) (hone : A.one ∈ U) :
    (SetDomain (A.closedModelDomain U))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  let := A.checkDomain_models_zf U
  let := A.check_transitive U
  have ht : IsForcingTop (A.check A.P) (A.check A.R) (A.check A.one) := by
    refine ⟨(A.check_mem_iff _ _).mpr A.top.1, ?_⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := (A.mem_check_iff A.P p).mp hp
    rw [← A.check_kpair, A.check_mem_iff]
    exact A.top.2 q hq
  exact TransitiveZF.forcingExtensionDomain_models_zf (A.check U)
    ⟨A.check A.P, (A.check_mem_iff _ _).mpr hP⟩
    ⟨A.check A.R, (A.check_mem_iff _ _).mpr hR⟩
    ⟨A.check A.one, (A.check_mem_iff _ _).mpr hone⟩ A.genericSet
    (A.checkEmbedding.map_forcingPreorder A.order) ht (A.genericSet_groundGeneric U)

theorem check_mem_closedModelDomain {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hone : A.one ∈ U) (x : SetDomain U) : A.check x.val ∈ A.closedModelDomain U := by
  have he := TransitiveZF.checkName_val U ⟨A.one, hone⟩ x
  let σ : SetDomain U := checkName ⟨A.one, hone⟩ x
  have hσ : checkName A.one x.val ∈ U := he ▸ σ.property
  exact (A.mem_closedModelDomain U _).mpr
    ⟨⟨checkName A.one x.val, checkName_isName A.top.1 x.val⟩, hσ, rfl⟩

theorem closedModelDomain_checkedFunctionClosed {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hP : A.P ∈ U) (hR : A.R ∈ U) (hone : A.one ∈ U) (X : SetDomain U)
    (hclosed : U ^ (X.val ×ˢ A.P) ⊆ U) :
    (A.closedModelDomain U) ^ (A.check X.val) ⊆ A.closedModelDomain U := by
  intro f hf
  obtain ⟨τ, rfl⟩ := A.ofName_surjective f
  obtain ⟨ν, hν, he⟩ := A.function_name_in_closed_model hP hR hone X hclosed τ
    (IsFunction.of_mem hf) (domain_eq_of_mem_function hf) (by
      intro a ha
      exact (A.mem_closedModelDomain U _).mp (function_value_mem hf ((A.check_mem_iff _ _).mpr ha)))
  exact (A.mem_closedModelDomain U _).mpr ⟨ν, hν, he.symm⟩

theorem evaluationGraph_mem_closedModelDomain {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hone : A.one ∈ U) (C : SetDomain U) (hC : ∀ σ ∈ C.val, IsForcingName A.P σ) :
    A.evaluationGraph C.val hC ∈ A.closedModelDomain U := by
  let o : SetDomain U := ⟨A.one, hone⟩
  let ν : SetDomain U := nameEvaluationGraph o C
  have he : ν.val = nameEvaluationGraph A.one C.val := by
    unfold nameEvaluationGraph
    apply TransitiveZF.repl_val U
    intro σ _
    simp only [TransitiveZF.kpair_val U, TransitiveZF.orderedPairName_val U,
      TransitiveZF.checkName_val U]
    rfl
  have hν : nameEvaluationGraph A.one C.val ∈ U := by rw [← he]; exact ν.property
  exact (A.mem_closedModelDomain U _).mpr
    ⟨⟨nameEvaluationGraph A.one C.val, nameEvaluationGraph_isName A.top.1 hC⟩, hν, rfl⟩

theorem closedModelDomain_rankFunctionClosed {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hP : A.P ∈ U) (hR : A.R ∈ U) (hone : A.one ∈ U)
    (α : V) [IsOrdinal α] (hH : forcingNameHierarchy A.P α ∈ U)
    (hclosed : U ^ (forcingNameHierarchy A.P α ×ˢ A.P) ⊆ U) :
    (A.closedModelDomain U) ^ hierarchy (A.check α) ⊆ A.closedModelDomain U := by
  let := A.closedModelDomain_transitive U
  let := A.closedModelDomain_models_zf hP hR hone
  intro f hf
  have hE := A.hierarchyEvaluation_function α
  have hh := compose_function hE hf
  have hhU := A.closedModelDomain_checkedFunctionClosed hP hR hone
    ⟨forcingNameHierarchy A.P α, hH⟩ hclosed _ hh
  exact TransitiveZF.function_mem_of_cover hE (A.hierarchyEvaluation_range α) hf
    (A.evaluationGraph_mem_closedModelDomain hone ⟨forcingNameHierarchy A.P α, hH⟩
      (forcingNameHierarchy_names A.P α)) hhU

theorem hierarchy_mem_closedModelDomain {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hP : A.P ∈ U) (hR : A.R ∈ U) (hone : A.one ∈ U)
    (α : V) [IsOrdinal α] (hH : forcingNameHierarchy A.P α ∈ U) :
    hierarchy (A.check α) ∈ A.closedModelDomain U := by
  let := A.closedModelDomain_transitive U
  let := A.closedModelDomain_models_zf hP hR hone
  let E : SetDomain (A.closedModelDomain U) := ⟨A.hierarchyEvaluation α,
    A.evaluationGraph_mem_closedModelDomain hone ⟨forcingNameHierarchy A.P α, hH⟩
      (forcingNameHierarchy_names A.P α)⟩
  have he := TransitiveZF.range_val (A.closedModelDomain U) E
  have hm := (range E).property
  rw [he] at hm
  exact (A.hierarchyEvaluation_range α) ▸ hm

end ForcingContext
end ZFVP
