import ZFVP.ModelTheory.TransitiveZFConstructors
import ZFVP.Syntax.PartialTruthAtoms

/-! The partial-truth predicates evaluated inside a specified set domain. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

def LocalDomainTruth (U : V) (p : LevyPolarity) (k : ℕ) (n φ b : V) : Prop :=
  (relativize (domainTruthFormula p k)).Eval ![n, φ, b]
    (fun i ↦ i.elim U (fun j ↦ (Empty.elim j : SetDomain U).val))

instance localDomainTruth_definable (U : V) (p : LevyPolarity) (k : ℕ) :
    ℒₛₑₜ-relation₃ (LocalDomainTruth U p k) := by
  have hd := relativizedEvaluation_definable U (domainTruthFormula p k) Empty.elim
  apply Language.Definable.of_iff hd
  intro v
  have hv : ![v 0, v 1, v 2] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.cases rfl (fun q ↦ Fin.elim0 q) l) j) i
  change (relativize (domainTruthFormula p k)).Eval ![v 0, v 1, v 2] _ ↔ _
  rw [hv]

variable [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem localDomainTruth_iff (U : V) [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (p : LevyPolarity) (k : ℕ) (n φ b : SetDomain U) :
    LocalDomainTruth U p k n.val φ.val b.val ↔ DomainTruth p k n φ b := by
  have he := eval_relativize U (domainTruthFormula p k) ![n, φ, b] Empty.elim
  have hv : (fun i ↦ (![n, φ, b] i).val) = ![n.val, φ.val, b.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.cases rfl (fun q ↦ Fin.elim0 q) l) j) i
  rw [hv] at he
  exact he.trans (eval_domainTruthFormula p k n φ b)

namespace LocalDomainTruth

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem bounded {p : LevyPolarity} {k : ℕ} {n φ b : V}
    (hφ : IsBoundedFormulaCode n φ) (hb : b ∈ U ^ n) :
    LocalDomainTruth U p k n φ b ↔ MembershipSatisfies U n φ b := by
  let := TransitiveZF.sequenceSupport U
  have hc : IsLevyFormulaCode p 0 n φ := hφ
  have hnU := IsCodingSupport.natural_mem (U := U) hc.context
  have hφU := (kpair_components_mem_transitive (levyFormulaFamily_subset_support 0 p U _ hc)).2
  have hbU := function_mem_sequenceSupport (subset_refl U) hc.context hb
  let n' : SetDomain U := ⟨n, hnU⟩
  let φ' : SetDomain U := ⟨φ, hφU⟩
  let b' : SetDomain U := ⟨b, hbU⟩
  have hc' := (TransitiveZF.levyCode_iff U p 0 n' φ').mpr hc
  have hb' := (TransitiveZF.function_on_iff U b' n').mpr ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩
  obtain ⟨D, hD, hbD⟩ := correctDomain_assignment (k + 1) hb'
  have hφ' : IsLevyFormulaCode p (k + 1) n' φ' := IsLevyFormulaCode.bounded hc'
  have he := hD.truth_iff hφ' hbD
  rw [← localDomainTruth_iff U p k n' φ' b', TransitiveZF.satisfies_iff U D n' φ' b'] at he
  have hDs : IsSequenceSupport D.val := (bounded_defined_absolute U sequenceSupportFormula_bounded
    (fun v ↦ IsSequenceSupport (v 0)) (fun v ↦ IsSequenceSupport (v 0)) ![D]).mp hD.support
  let := hDs
  exact he.trans (membershipSatisfies_bounded_absolute hφ
    (show IsNonempty D.val from ⟨ω, hDs.omega_mem⟩)
    (show IsNonempty U from ⟨ω, IsCodingSupport.omega_mem⟩)
    ((TransitiveZF.function_iff U b' n' D).mp hbD) hb)

theorem and_iff {p : LevyPolarity} {k : ℕ} {n φ ψ b : V}
    (hφ : IsLevyFormulaCode p (k + 1) n φ) (hψ : IsLevyFormulaCode p (k + 1) n ψ)
    (hb : b ∈ U ^ n) :
    LocalDomainTruth U p k n (andCode φ ψ) b ↔
      LocalDomainTruth U p k n φ b ∧ LocalDomainTruth U p k n ψ b := by
  let := TransitiveZF.sequenceSupport U
  let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hφ.context⟩
  let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) p U _ hφ)).2⟩
  let ψ' : SetDomain U := ⟨ψ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) p U _ hψ)).2⟩
  let b' : SetDomain U := ⟨b, function_mem_sequenceSupport (subset_refl U) hφ.context hb⟩
  have hc := domainTruth_and ((TransitiveZF.levyCode_iff U p (k + 1) n' φ').mpr hφ)
    ((TransitiveZF.levyCode_iff U p (k + 1) n' ψ').mpr hψ)
    ((TransitiveZF.function_on_iff U b' n').mpr ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩)
  rw [← localDomainTruth_iff U p k n' (andCode φ' ψ') b', ← localDomainTruth_iff U p k n' φ' b',
    ← localDomainTruth_iff U p k n' ψ' b', TransitiveZF.andCode_val U] at hc
  exact hc

theorem or_iff {p : LevyPolarity} {k : ℕ} {n φ ψ b : V}
    (hφ : IsLevyFormulaCode p (k + 1) n φ) (hψ : IsLevyFormulaCode p (k + 1) n ψ)
    (hb : b ∈ U ^ n) :
    LocalDomainTruth U p k n (orCode φ ψ) b ↔
      LocalDomainTruth U p k n φ b ∨ LocalDomainTruth U p k n ψ b := by
  let := TransitiveZF.sequenceSupport U
  let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hφ.context⟩
  let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) p U _ hφ)).2⟩
  let ψ' : SetDomain U := ⟨ψ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) p U _ hψ)).2⟩
  let b' : SetDomain U := ⟨b, function_mem_sequenceSupport (subset_refl U) hφ.context hb⟩
  have hc := domainTruth_or ((TransitiveZF.levyCode_iff U p (k + 1) n' φ').mpr hφ)
    ((TransitiveZF.levyCode_iff U p (k + 1) n' ψ').mpr hψ)
    ((TransitiveZF.function_on_iff U b' n').mpr ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩)
  rw [← localDomainTruth_iff U p k n' (orCode φ' ψ') b', ← localDomainTruth_iff U p k n' φ' b',
    ← localDomainTruth_iff U p k n' ψ' b', TransitiveZF.orCode_val U] at hc
  exact hc

theorem raise_iff {p q : LevyPolarity} {k : ℕ} {n φ b : V}
    (hφ : IsLevyFormulaCode q (k + 1) n φ) (hb : b ∈ U ^ n) :
    LocalDomainTruth U p (k + 1) n φ b ↔ LocalDomainTruth U q k n φ b := by
  let := TransitiveZF.sequenceSupport U
  let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hφ.context⟩
  let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) q U _ hφ)).2⟩
  let b' : SetDomain U := ⟨b, function_mem_sequenceSupport (subset_refl U) hφ.context hb⟩
  have hc := domainTruth_raise (q := p) ((TransitiveZF.levyCode_iff U q (k + 1) n' φ').mpr hφ)
    ((TransitiveZF.function_on_iff U b' n').mpr ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩)
  rw [← localDomainTruth_iff U p (k + 1) n' φ' b', ← localDomainTruth_iff U q k n' φ' b'] at hc
  exact hc

end LocalDomainTruth

end ZFVP
