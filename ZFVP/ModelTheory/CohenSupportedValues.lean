import ZFVP.ModelTheory.CohenInfiniteSet
import ZFVP.SetTheory.CohenNameSupport

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def cohenFunctionValueFormula : SetTheorySemisentence 3 := f“f n x. !IsFunction.dfn f ∧ !value.dfn x f n”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_cohenFunctionValueFormula (f n x : V) :
    cohenFunctionValueFormula.Evalb ![f, n, x] ↔ IsFunction f ∧ f ‘ n = x := by
  simp [cohenFunctionValueFormula, eq_comm]

theorem eval_cohenFunctionValueFormula_assignment (v : Fin 3 → V) :
    cohenFunctionValueFormula.Evalb v ↔ IsFunction (v 0) ∧ (v 0) ‘ (v 1) = v 2 := by
  simp [cohenFunctionValueFormula, eq_comm]

namespace CohenModel

variable [Countable V] {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

theorem function_value_supported (τ : (cohenContext (ω : V) G hG).Name)
    {E : V} (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    (hE : ∀ π, IsInternalPermutation (ω : V) π → (∀ i ∈ E, π ‘ i = i) →
      nameAction (cohenPermutation (ω : V) π) τ.val = τ.val)
    (hf : IsFunction ((cohenContext (ω : V) G hG).ofName τ))
    {n i : V} (hi : i ∈ (ω : V))
    (hvalue : ((cohenContext (ω : V) G hG).ofName τ) ‘ ((cohenContext (ω : V) G hG).check n) = real hG i hi) :
    i ∈ E := by
  classical
  let S := cohenContext (ω : V) G hG
  let ν : S.Name := ⟨checkName ∅ n, hereditarilySymmetric_checkName S.poset S.group S.normal S.top n⟩
  let σ : S.Name := ⟨cohenRealName (ω : V) i, cohenRealName_hereditarilySymmetric hi⟩
  let v : Fin 3 → S.Name := ![τ, ν, σ]
  have heval : cohenFunctionValueFormula.Evalb (fun k ↦ S.ofName (v k)) := by
    exact (eval_cohenFunctionValueFormula_assignment _).mpr ⟨hf, hvalue⟩
  obtain ⟨q, hqG, hqforce⟩ := (S.formula_truth cohenFunctionValueFormula v).mp heval
  have hq : q ∈ cohenConditions (ω : V) := hG.1.1 q hqG
  by_contra hiE
  obtain ⟨j, hj, hji, hjq, _, hjfix⟩ := cohen_fresh_transposition hq hEf hiE
  let π := internalTransposition (ω : V) i j
  have hπ : IsInternalPermutation (ω : V) π := internalTransposition_permutation hi hj
  let a := cohenPermutation (ω : V) π
  have ha : IsForcingAutomorphism S.P S.R a := cohenPermutation_automorphism hπ
  have haG : a ∈ S.Γ := (mem_cohenGroup (ω : V) a).mpr ⟨π, hπ, rfl⟩
  have hτfix : nameAction a τ.val = τ.val := hE π hπ (fun k hk ↦ hjfix k hk (hEω k hk))
  have hνfix : nameAction a ν.val = ν.val :=
    nameAction_checkName S.top.1 (forcingAutomorphism_top S.poset S.top ha) n
  have hσmove : nameAction a σ.val = cohenRealName (ω : V) j := by
    change nameAction (cohenPermutation (ω : V) π) (cohenRealName (ω : V) i) = _
    rw [nameAction_cohenRealName hπ hi, internalTransposition_left hi]
  let σj : S.Name := ⟨cohenRealName (ω : V) j, cohenRealName_hereditarilySymmetric hj⟩
  let w : Fin 3 → S.Name := ![τ, ν, σj]
  have hnames : (fun k ↦ nameAction a (v k).val) = fun k ↦ (w k).val := by
    funext k
    refine Fin.cases hτfix ?_ k
    intro k
    refine Fin.cases hνfix ?_ k
    intro k
    exact Fin.cases hσmove (fun l ↦ Fin.elim0 l) k
  have haqforce : a ‘ q ∈ symmetricForcingFormula S.P S.R S.Γ S.F cohenFunctionValueFormula
      (standardTuple (fun k ↦ (w k).val)) := by
    have hh := (symmetricForcingFormula_nameAction_iff S.order S.group S.normal haG
      cohenFunctionValueFormula (fun k ↦ (v k).val) (fun k ↦ (v k).property) hq).mpr hqforce
    simpa only [hnames] using hh
  have hcompat := cohen_transposition_compatible hq hi hj hjq
  obtain ⟨r, hr, hrq, hra⟩ := hcompat
  have hra' : ⟨r, a ‘ q⟩ₖ ∈ S.R := by
    change ⟨r, (cohenPermutation (ω : V) π) ‘ q⟩ₖ ∈ cohenOrder (ω : V)
    rw [cohenPermutation_value hq]
    exact hra
  obtain ⟨H, hH, hrH⟩ := exists_externalForcingGeneric S.order hr
  have hqH : q ∈ H := hH.1.2.2.1 r hrH q hq hrq
  have haqH : a ‘ q ∈ H := hH.1.2.2.1 r hrH (a ‘ q) (function_value_mem ha.1 hq) hra'
  let T := cohenContext (ω : V) H hH
  have hevali : cohenFunctionValueFormula.Evalb (fun k ↦ T.ofName (v k)) := by
    exact (T.formula_truth cohenFunctionValueFormula v).mpr ⟨q, hqH, hqforce⟩
  have hevalj : cohenFunctionValueFormula.Evalb (fun k ↦ T.ofName (w k)) := by
    exact (T.formula_truth cohenFunctionValueFormula w).mpr ⟨a ‘ q, haqH, haqforce⟩
  have hfi := (eval_cohenFunctionValueFormula_assignment _).mp hevali
  have hfj := (eval_cohenFunctionValueFormula_assignment _).mp hevalj
  exact real_ne hH hi hj hji.symm (hfi.2.symm.trans hfj.2)

end CohenModel
end ZFVP
