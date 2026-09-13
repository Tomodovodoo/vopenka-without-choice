import ZFVP.ModelTheory.DeltaOneMembershipEmbedding
import ZFVP.ModelTheory.EmbeddingCriticalPointImage

/-! Absolute dictionaries between a transitive set model of ZF and its ambient model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

theorem bounded_defined_absolute (U : V) [IsTransitive U] {n : ℕ}
    {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    (R : (Fin n → V) → Prop) (S : (Fin n → SetDomain U) → Prop)
    [Defined R φ] [Defined S φ] (b : Fin n → SetDomain U) :
    S b ↔ R (fun i ↦ (b i).val) :=
  (Defined.eval_iff b).symm.trans ((bounded_formula_absolute U hφ b).trans (Defined.eval_iff _))

theorem deltaOne_defined_absolute (U : V) [IsTransitive U] {n : ℕ}
    {σ π : SetTheorySemisentence n} (hσ : IsSigmaFormula 1 σ) (hπ : IsPiFormula 1 π)
    (R : (Fin n → V) → Prop) (S : (Fin n → SetDomain U) → Prop)
    [Defined R σ] [Defined R π] [Defined S σ] [Defined S π] (b : Fin n → SetDomain U) :
    S b ↔ R (fun i ↦ (b i).val) := by
  constructor
  · intro hs
    exact (show σ.Evalb (fun i ↦ (b i).val) ↔ R (fun i ↦ (b i).val) from Defined.eval_iff _).mp
      (sigma_one_upward U hσ b ((show σ.Evalb b ↔ S b from Defined.eval_iff _).mpr hs))
  · intro hr
    exact (show π.Evalb b ↔ S b from Defined.eval_iff _).mp
      (pi_one_downward U hπ b ((show π.Evalb (fun i ↦ (b i).val) ↔ R (fun i ↦ (b i).val)
        from Defined.eval_iff _).mpr hr))

variable [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem ordinal_iff (α : SetDomain U) : IsOrdinal α ↔ IsOrdinal α.val :=
  bounded_defined_absolute U isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
    (fun v ↦ IsOrdinal (v 0)) ![α]

theorem function_iff (f X Y : SetDomain U) : f ∈ Y ^ X ↔ f.val ∈ Y.val ^ X.val :=
  bounded_defined_absolute U boundedFunctionFormula_bounded (fun v ↦ v 0 ∈ v 2 ^ v 1)
    (fun v ↦ v 0 ∈ v 2 ^ v 1) ![f, X, Y]

theorem omega_val : (ω : SetDomain U).val = (ω : V) := by
  exact (bounded_defined_absolute U boundedOmegaFormula_bounded (fun v ↦ v 0 = (ω : V))
    (fun v ↦ v 0 = (ω : SetDomain U)) ![ω]).mp rfl

theorem empty_val : (∅ : SetDomain U).val = (∅ : V) := by
  exact (bounded_defined_absolute U boundedEmptyFormula_bounded (fun v ↦ v 0 = (∅ : V))
    (fun v ↦ v 0 = (∅ : SetDomain U)) ![∅]).mp rfl

theorem succ_val (x : SetDomain U) : (succ x).val = succ x.val :=
  (bounded_defined_absolute U boundedSuccFormula_bounded (fun v ↦ v 0 = succ (v 1))
    (fun v ↦ v 0 = succ (v 1)) ![succ x, x]).mp rfl

theorem rank_val (x : SetDomain U) : (rank x).val = rank x.val :=
  (deltaOne_defined_absolute U sigmaOneRankFormula_sigmaOne piOneRankFormula_piOne
    (fun v ↦ v 0 = rank (v 1)) (fun v ↦ v 0 = rank (v 1)) ![rank x, x]).mp rfl

theorem satisfies_iff (A n φ b : SetDomain U) :
    MembershipSatisfies A n φ b ↔ MembershipSatisfies A.val n.val φ.val b.val :=
  deltaOne_defined_absolute U (sigmaOneMembershipModelTruthFormula_sigmaOne true) piOneMembershipTruthFormula_piOne
    (fun v ↦ MembershipSatisfies (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ MembershipSatisfies (v 0) (v 1) (v 2) (v 3)) ![A, n, φ, b]

theorem levyCode_iff (p : LevyPolarity) (k : ℕ) (n φ : SetDomain U) :
    IsLevyFormulaCode p k n φ ↔ IsLevyFormulaCode p k n.val φ.val :=
  deltaOne_defined_absolute U (sigmaOneLevyCodeFormula_sigmaOne p k) (piOneLevyCodeFormula_piOne p k)
    (fun v ↦ IsLevyFormulaCode p k (v 0) (v 1)) (fun v ↦ IsLevyFormulaCode p k (v 0) (v 1)) ![n, φ]

theorem hierarchy_mem_iff (α x : SetDomain U) (hα : IsOrdinal α) :
    x ∈ hierarchy α ↔ x.val ∈ hierarchy α.val := by
  let := hα
  let := (ordinal_iff U α).mp hα
  rw [mem_hierarchy_iff_rank_mem, mem_hierarchy_iff_rank_mem]
  change (rank x).val ∈ α.val ↔ rank x.val ∈ α.val
  rw [rank_val U x]

theorem hierarchy_val (α : SetDomain U) (hα : IsOrdinal α) (hsub : hierarchy α.val ⊆ U) :
    (hierarchy α).val = hierarchy α.val := by
  apply mem_ext
  intro x
  constructor
  · intro hx
    have hxU := (inferInstance : IsTransitive U).mem_trans hx (hierarchy α).property
    exact (hierarchy_mem_iff U α ⟨x, hxU⟩ hα).mp hx
  · intro hx
    exact (hierarchy_mem_iff U α ⟨x, hsub x hx⟩ hα).mpr hx

end TransitiveZF

end ZFVP
