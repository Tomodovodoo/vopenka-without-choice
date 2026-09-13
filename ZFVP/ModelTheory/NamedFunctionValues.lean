import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.SetTheory.AtomicForcingDictionary
import ZFVP.ModelTheory.ForcingScottSets

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def namedFunctionValueDecisionFormula : SetTheorySemisentence 7 :=
  f“P R o t p a x. !(ordinaryForcingTranslation functionValueFormula) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 2))
      (!assignmentPrependFormula (!(numeralFormula 1))
        (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) x)
        (!checkNameFormula o a)) t)”

def namedFunctionValueUniqueFormula : SetTheorySemisentence 8 :=
  f“P R o t p a x y. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P t ∧ !forcingNameFormula P x ∧ !forcingNameFormula P y ∧
    !namedFunctionValueDecisionFormula P R o t p a x ∧
    !namedFunctionValueDecisionFormula P R o t p a y → p ∈ !atomicEqualityFormula P R x y”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ForcesNamedFunctionValue (P R one τ p a σ : V) : Prop :=
  p ∈ forcingFormula P R functionValueFormula (standardTuple ![τ, checkName one a, σ])

instance forcesNamedFunctionValue_definable (P R one τ : V) :
    ℒₛₑₜ-relation₃[V] (ForcesNamedFunctionValue P R one τ) := by
  unfold ForcesNamedFunctionValue
  simp only [standardTuple]
  definability

instance namedFunctionValueDecisionFormula_defined :
    Defined (fun v : Fin 7 → V ↦ ForcesNamedFunctionValue (v 0) (v 1) (v 2)
      (v 3) (v 4) (v 5) (v 6)) namedFunctionValueDecisionFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [namedFunctionValueDecisionFormula, ForcesNamedFunctionValue, standardTuple,
    Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h
    exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
    exact h

theorem eval_namedFunctionValueUniqueFormula (v : Fin 8 → V) :
    namedFunctionValueUniqueFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsForcingName (v 0) (v 3) → IsForcingName (v 0) (v 6) → IsForcingName (v 0) (v 7) →
        ForcesNamedFunctionValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) →
        ForcesNamedFunctionValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 7) →
          v 4 ∈ atomicEquality (v 0) (v 1) (v 6) (v 7)) := by
  simp [namedFunctionValueUniqueFormula]

theorem ForcingContext.namedFunctionValue_truth (A : ForcingContext V)
    (τ σ : ForcingName A.P) (a : V) :
    (∃ p ∈ A.G, ForcesNamedFunctionValue A.P A.R A.one τ.val p a σ.val) ↔
      IsFunction (A.ofName τ) ∧ (A.ofName τ) ‘ (A.check a) = A.ofName σ := by
  let ν : ForcingName A.P := ⟨checkName A.one a, checkName_isName A.top.1 a⟩
  exact (A.formula_truth functionValueFormula ![τ, ν, σ]).symm.trans (eval_functionValueFormula _)

theorem forcesNamedFunctionValue_unique_countable [Countable V] {P R one τ p a σ ν : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hσ : IsForcingName P σ) (hν : IsForcingName P ν)
    (hs : ForcesNamedFunctionValue P R one τ p a σ)
    (hn : ForcesNamedFunctionValue P R one τ p a ν) : p ∈ atomicEquality P R σ ν := by
  have hp : p ∈ P := (forcingFormula_regular hR functionValueFormula _).1 p hs
  apply (atomicEquality_regular hR σ ν).2.2 p hp
  intro q hq hqp
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  have hpG := hG.1.2.2.1 q hqG p hp hqp
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hvs := (A.namedFunctionValue_truth ⟨τ, hτ⟩ ⟨σ, hσ⟩ a).mp ⟨p, hpG, hs⟩
  have hvn := (A.namedFunctionValue_truth ⟨τ, hτ⟩ ⟨ν, hν⟩ a).mp ⟨p, hpG, hn⟩
  have heq : A.ofName ⟨σ, hσ⟩ = A.ofName ⟨ν, hν⟩ := hvs.2.symm.trans hvn.2
  obtain ⟨r, hrG, hr⟩ := (forcingQuotientMk_eq_iff P R G hR hG.1 ⟨σ, hσ⟩ ⟨ν, hν⟩).mp heq
  obtain ⟨s, hsG, hsr, hsq⟩ := hG.1.2.2.2 r hrG q hqG
  exact ⟨s, atomicEquality_mono hR hr (hG.1.1 s hsG) hsr, hsq⟩

theorem namedFunctionValueUniqueFormula_countable [Countable V] (v : Fin 8 → V) :
    namedFunctionValueUniqueFormula.Evalb v := by
  apply (eval_namedFunctionValueUniqueFormula v).mpr
  exact fun hR ht hτ hσ hν hs hn ↦ forcesNamedFunctionValue_unique_countable
    (P := v 0) (R := v 1) (one := v 2) (τ := v 3) (p := v 4) (a := v 5)
    (σ := v 6) (ν := v 7) hR ht hτ hσ hν hs hn

theorem forcesNamedFunctionValue_unique {P R one τ p a σ ν : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hσ : IsForcingName P σ) (hν : IsForcingName P ν)
    (hs : ForcesNamedFunctionValue P R one τ p a σ)
    (hn : ForcesNamedFunctionValue P R one τ p a ν) : p ∈ atomicEquality P R σ ν := by
  have hh : namedFunctionValueUniqueFormula.Evalb ![P, R, one, τ, p, a, σ, ν] :=
    eval_of_countable_zf namedFunctionValueUniqueFormula (by
    intro W _ _ _ _ v
    exact namedFunctionValueUniqueFormula_countable v)
    ![P, R, one, τ, p, a, σ, ν]
  exact (eval_namedFunctionValueUniqueFormula ![P, R, one, τ, p, a, σ, ν]).mp hh hR htop hτ hσ hν hs hn

def IsNamedValueScottSet (U P R one τ p a X : V) : Prop :=
  ∃ σ ∈ U, IsForcingName P σ ∧ ForcesNamedFunctionValue P R one τ p a σ ∧
    IsLocalScottSet U (ForcingScottRelated P R p) σ X

instance isNamedValueScottSet_definable (U P R one τ : V) :
    ℒₛₑₜ-relation₃[V] (IsNamedValueScottSet U P R one τ) := by
  unfold IsNamedValueScottSet IsLocalScottSet ForcingScottRelated ForcesNamedFunctionValue
  simp only [standardTuple]
  definability

theorem IsNamedValueScottSet.unique {U P R one τ p a X Y : V} [IsTransitive U]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ)
    (hX : IsNamedValueScottSet U P R one τ p a X)
    (hY : IsNamedValueScottSet U P R one τ p a Y) : X = Y := by
  obtain ⟨σ, _, hσ, hs, hX⟩ := hX
  obtain ⟨ν, _, hν, hn, hY⟩ := hY
  exact forcingScottSet_eq hR (forcesNamedFunctionValue_unique hR htop hτ hσ hν hs hn) hX hY

theorem namedValueScottSet_exists {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (P R p : SetDomain U) (one τ a : V) (hR : IsForcingPreorder P.val R.val)
    (hex : ∃ σ ∈ U, IsForcingName P.val σ ∧
      ForcesNamedFunctionValue P.val R.val one τ p.val a σ) :
    ∃ X, IsNamedValueScottSet U P.val R.val one τ p.val a X := by
  obtain ⟨σ, hσU, hσ, hs⟩ := hex
  have hp : p.val ∈ P.val := (forcingFormula_regular hR functionValueFormula _).1 p.val hs
  obtain ⟨X, hX⟩ := forcingScottSet_exists P R p ⟨σ, hσU⟩ hR hp hσ
  exact ⟨X, σ, hσU, hσ, hs, hX⟩

theorem IsNamedValueScottSet.union {U P R one τ p a X : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hX : IsNamedValueScottSet U P R one τ p a X) :
    X ∈ U ∧ IsNonempty X ∧ (⋃ˢ X) ∈ U ∧ IsForcingName P (⋃ˢ X) ∧
      ∃ σ ∈ U, IsForcingName P σ ∧ ForcesNamedFunctionValue P R one τ p a σ ∧
        p ∈ atomicEquality P R σ (⋃ˢ X) := by
  obtain ⟨σ, hσU, hσ, hs, hX⟩ := hX
  obtain ⟨hu, hn, he⟩ := forcingScottSet_union hX
  exact ⟨hX.1, hX.2.1, hu, hn, σ, hσU, hσ, hs, he⟩

def NamedValueScottSlot (U P R one τ s X : V) : Prop :=
  IsNamedValueScottSet U P R one τ (kpair.π₂ s) (kpair.π₁ s) X ∨
    (¬ ∃ Y, IsNamedValueScottSet U P R one τ (kpair.π₂ s) (kpair.π₁ s) Y) ∧ X = ∅

instance namedValueScottSlot_definable (U P R one τ : V) :
    ℒₛₑₜ-relation[V] (NamedValueScottSlot U P R one τ) := by
  unfold NamedValueScottSlot
  definability

theorem namedValueScottSlot_existsUnique {U P R one τ : V} [IsTransitive U]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (s : V) : ∃! X, NamedValueScottSlot U P R one τ s X := by
  classical
  by_cases hex : ∃ X, IsNamedValueScottSet U P R one τ (kpair.π₂ s) (kpair.π₁ s) X
  · obtain ⟨X, hX⟩ := hex
    refine ⟨X, Or.inl hX, ?_⟩
    intro Y hY
    rcases hY with hY | ⟨hn, _⟩
    · exact hY.unique hR htop hτ hX
    · exact (hn ⟨X, hX⟩).elim
  · exact ⟨∅, Or.inr ⟨hex, rfl⟩, fun Y hY ↦ hY.elim
      (fun h ↦ (hex ⟨Y, h⟩).elim) And.right⟩

noncomputable def namedValueScottGraph (U P R one τ D : V) : V :=
  {z ∈ D ×ˢ U ; NamedValueScottSlot U P R one τ (kpair.π₁ z) (kpair.π₂ z)}

theorem pair_mem_namedValueScottGraph (U P R one τ D s X : V) :
    ⟨s, X⟩ₖ ∈ namedValueScottGraph U P R one τ D ↔
      s ∈ D ∧ X ∈ U ∧ NamedValueScottSlot U P R one τ s X := by
  simp only [namedValueScottGraph, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem namedValueScottGraph_function {U P R one τ : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (D : V) : namedValueScottGraph U P R one τ D ∈ U ^ D := by
  apply mem_function.intro (fun z hz ↦ (mem_sep_iff.mp hz).1)
  intro s hs
  obtain ⟨X, hX, hu⟩ := namedValueScottSlot_existsUnique (U := U) hR htop hτ s
  have hXU : X ∈ U := by
    rcases hX with ⟨σ, _, _, _, hX⟩ | ⟨_, rfl⟩
    · exact hX.1
    · have he := TransitiveZF.empty_val U
      have hm := (∅ : SetDomain U).property
      rwa [he] at hm
  refine ⟨X, (pair_mem_namedValueScottGraph _ _ _ _ _ _ _ _).mpr ⟨hs, hXU, hX⟩, ?_⟩
  intro Y hY
  exact hu Y ((pair_mem_namedValueScottGraph _ _ _ _ _ _ _ _).mp hY).2.2

theorem namedValueScottGraph_value {U P R one τ D s X : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hs : s ∈ D)
    (hX : IsNamedValueScottSet U P R one τ (kpair.π₂ s) (kpair.π₁ s) X) :
    (namedValueScottGraph U P R one τ D) ‘ s = X := by
  let := IsFunction.of_mem (namedValueScottGraph_function (U := U) hR htop hτ D)
  have hXU : X ∈ U := by obtain ⟨_, _, _, _, h⟩ := hX; exact h.1
  exact value_eq_of_kpair_mem
    ((pair_mem_namedValueScottGraph _ _ _ _ _ _ _ _).mpr ⟨hs, hXU, Or.inl hX⟩)

theorem namedValueScottGraph_mem {U P R one τ D : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hclosed : U ^ D ⊆ U) :
    namedValueScottGraph U P R one τ D ∈ U :=
  hclosed _ (namedValueScottGraph_function hR htop hτ D)

theorem ForcingContext.namedValueScottSet_eval (A : ForcingContext V)
    {U p a X : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (τ : ForcingName A.P) (hp : p ∈ A.G)
    (hX : IsNamedValueScottSet U A.P A.R A.one τ.val p a X) :
    ∃ ν : ForcingName A.P, ν.val = ⋃ˢ X ∧ ν.val ∈ U ∧
      IsFunction (A.ofName τ) ∧ (A.ofName τ) ‘ (A.check a) = A.ofName ν := by
  obtain ⟨_, _, hu, hn, σ, _, hσ, hs, he⟩ := hX.union
  let ν : ForcingName A.P := ⟨⋃ˢ X, hn⟩
  have hv := (A.namedFunctionValue_truth τ ⟨σ, hσ⟩ a).mp ⟨p, hp, hs⟩
  have heq : A.ofName ⟨σ, hσ⟩ = A.ofName ν :=
    (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1 ⟨σ, hσ⟩ ν).mpr ⟨p, hp, he⟩
  exact ⟨ν, rfl, hu, hv.1, hv.2.trans heq⟩

end ZFVP
