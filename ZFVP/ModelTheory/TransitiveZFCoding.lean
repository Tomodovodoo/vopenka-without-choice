import ZFVP.ModelTheory.TransitiveZFAbsoluteness
import ZFVP.Syntax.PartialTruthConnectives

/-! Internal finite coding in a transitive ZF model agrees with ambient coding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem kpair_val (x y : SetDomain U) : (⟨x, y⟩ₖ : SetDomain U).val = ⟨x.val, y.val⟩ₖ :=
  (bounded_defined_absolute U boundedKpairFormula_bounded (fun v ↦ v 0 = ⟨v 1, v 2⟩ₖ)
    (fun v ↦ v 0 = ⟨v 1, v 2⟩ₖ) ![⟨x, y⟩ₖ, x, y]).mp rfl

theorem doubleton_val (x y : SetDomain U) : (doubleton x y).val = doubleton x.val y.val :=
  (bounded_defined_absolute U boundedDoubletonFormula_bounded (fun v ↦ v 0 = doubleton (v 1) (v 2))
    (fun v ↦ v 0 = doubleton (v 1) (v 2)) ![doubleton x y, x, y]).mp rfl

theorem union_val (x y : SetDomain U) : (x ∪ y).val = x.val ∪ y.val :=
  (bounded_defined_absolute U boundedUnionFormula_bounded (fun v ↦ v 0 = v 1 ∪ v 2)
    (fun v ↦ v 0 = v 1 ∪ v 2) ![x ∪ y, x, y]).mp rfl

theorem numeral_val (n : ℕ) : (n : SetDomain U).val = (n : V) := by
  induction n with
  | zero => exact empty_val U
  | succ n ih => rw [num_succ_def, succ_val U, ih, num_succ_def]

theorem sequenceSupport : IsSequenceSupport U where
  toIsTransitive := inferInstance
  omega_mem := by simpa only [omega_val U] using (ω : SetDomain U).property
  kpair_closed x hx y hy := by
    let a : SetDomain U := ⟨x, hx⟩
    let b : SetDomain U := ⟨y, hy⟩
    exact (congrArg (fun z : V ↦ z ∈ U) (kpair_val U a b)).mp (⟨a, b⟩ₖ : SetDomain U).property
  doubleton_closed x hx y hy := by
    let a : SetDomain U := ⟨x, hx⟩
    let b : SetDomain U := ⟨y, hy⟩
    exact (congrArg (fun z : V ↦ z ∈ U) (doubleton_val U a b)).mp (doubleton a b).property
  succ_closed x hx := by
    let a : SetDomain U := ⟨x, hx⟩
    exact (congrArg (fun z : V ↦ z ∈ U) (succ_val U a)).mp (succ a).property
  union_closed x hx y hy := by
    let a : SetDomain U := ⟨x, hx⟩
    let b : SetDomain U := ⟨y, hy⟩
    exact (congrArg (fun z : V ↦ z ∈ U) (union_val U a b)).mp (a ∪ b).property

theorem natural_iff (n : SetDomain U) : n ∈ (ω : SetDomain U) ↔ n.val ∈ (ω : V) := by
  change n.val ∈ (ω : SetDomain U).val ↔ _
  rw [omega_val U]

theorem function_domain (f : SetDomain U) [IsFunction f] :
    IsFunction f.val ∧ domain f.val = (domain f).val :=
  (bounded_defined_absolute U boundedFunctionDomainFormula_bounded
    (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1)
    (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1) ![f, domain f]).mp
      (by change IsFunction f ∧ domain f = domain f; exact ⟨inferInstance, rfl⟩)

theorem function_on_iff (f n : SetDomain U) :
    (IsFunction f ∧ domain f = n) ↔ (IsFunction f.val ∧ domain f.val = n.val) :=
  bounded_defined_absolute U boundedFunctionDomainFormula_bounded
    (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1)
    (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1) ![f, n]

theorem value_val (f x : SetDomain U) [IsFunction f] (hx : x ∈ domain f) :
    (f ‘ x).val = f.val ‘ x.val := by
  let := (function_domain U f).1
  have hp := kpair_value_mem hx
  change (⟨x, f ‘ x⟩ₖ : SetDomain U).val ∈ f.val at hp
  rw [kpair_val U] at hp
  exact (value_eq_of_kpair_mem hp).symm

theorem assignmentPrepend_val {n b : SetDomain U} (hn : n ∈ (ω : SetDomain U))
    (hb : IsFunction b ∧ domain b = n) (x : SetDomain U) :
    (assignmentPrepend n b x).val = assignmentPrepend n.val b.val x.val := by
  obtain ⟨D, _, hbD, hxD⟩ := correctDomain_assignment_with 0 hb x
  have hs := (eval_boundedAssignmentPrependFormula hn hbD hxD (assignmentPrepend n b x)).mpr rfl
  have he := (bounded_formula_absolute U boundedAssignmentPrependFormula_bounded
    ![D, ω, assignmentPrepend n b x, n, b, x]).mp hs
  have htuple : (fun i ↦ (![D, ω, assignmentPrepend n b x, n, b, x] i).val) =
      ![D.val, (ω : V), (assignmentPrepend n b x).val, n.val, b.val, x.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases (omega_val U) (fun l ↦ Fin.cases rfl
      (fun m ↦ Fin.cases rfl (fun q ↦ Fin.cases rfl (fun r ↦ Fin.cases rfl
        (fun z ↦ Fin.elim0 z) r) q) m) l) j) i
  rw [htuple] at he
  exact (eval_boundedAssignmentPrependFormula ((natural_iff U n).mp hn)
    ((function_iff U b n D).mp hbD) hxD _).mp he

theorem membershipFamily_val :
    (formulaFamily (membershipLanguageCode : SetDomain U) ∅).val =
      (formulaFamily (membershipLanguageCode : V) ∅) := by
  have hs := (eval_sigmaOneMembershipFamilyFormula
    (formulaFamily (membershipLanguageCode : SetDomain U) ∅)).mpr rfl
  have he := sigma_one_upward U sigmaOneMembershipFamilyFormula_sigmaOne
    ![formulaFamily (membershipLanguageCode : SetDomain U) ∅] hs
  exact (Defined.eval_iff _).mp he

theorem membershipCode_iff (n φ : SetDomain U) :
    IsMembershipFormulaCode n φ ↔ IsMembershipFormulaCode n.val φ.val := by
  change (⟨n, φ⟩ₖ : SetDomain U).val ∈ (formulaFamily (membershipLanguageCode : SetDomain U) ∅).val ↔
    ⟨n.val, φ.val⟩ₖ ∈ (formulaFamily (membershipLanguageCode : V) ∅)
  rw [kpair_val U, membershipFamily_val U]

end TransitiveZF

end ZFVP
