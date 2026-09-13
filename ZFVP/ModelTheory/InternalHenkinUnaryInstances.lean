import ZFVP.ModelTheory.InternalHenkinImplication

/-! Actual unary instances and finite permutations of Henkin name contexts. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def unaryCodedInstance (n i ψ : V) : V :=
  renameMembershipFormula 1 n (constantGraph 1 i) ψ

instance unaryCodedInstance_definable : ℒₛₑₜ-function₃[V] unaryCodedInstance := by
  unfold unaryCodedInstance
  exact Language.DefinableFunction₄.comp (by definability) (by definability)
    (by definability) (by definability)

theorem unaryCodedInstance_valid {n i ψ : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hψ : ψ ∈ formulaSet (membershipLanguageCode : V) ∅ 1) :
    unaryCodedInstance n i ψ ∈ formulaSet membershipLanguageCode ∅ n :=
  renameMembershipFormula_mem (by simp) hn (constantGraph_mem_function 1 n i hi) hψ

theorem constantGraph_compose {A B D i r : V} (hi : i ∈ B) (hr : r ∈ D ^ B) :
    compose (constantGraph A i) r = constantGraph A (r ‘ i) := by
  have hc := constantGraph_mem_function A B i hi
  apply function_eq_of_values (compose_function hc hr)
    (constantGraph_mem_function A D (r ‘ i) (function_value_mem hr hi))
  intro x hx
  rw [value_compose_of_mem_function hc hr hx, value_constantGraph A i hx, value_constantGraph A (r ‘ i) hx]

theorem unaryCodedInstance_rename {n m i r ψ : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hi : i ∈ n) (hr : r ∈ m ^ n)
    (hψ : ψ ∈ formulaSet (membershipLanguageCode : V) ∅ 1) :
    renameMembershipFormula n m r (unaryCodedInstance n i ψ) = unaryCodedInstance m (r ‘ i) ψ := by
  rw [unaryCodedInstance, renameMembershipFormula_compose (by simp) hn hm
    (constantGraph_mem_function 1 n i hi) hr hψ, constantGraph_compose hi hr]
  rfl

theorem unaryCodedInstance_shift {n i ψ : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hψ : ψ ∈ formulaSet (membershipLanguageCode : V) ∅ 1) :
    henkinShiftFormula n (unaryCodedInstance n i ψ) = unaryCodedInstance (succ n) (succ i) ψ := by
  rw [henkinShiftFormula, unaryCodedInstance_rename hn (ω_succ_closed hn) hi (successorIndices_function hn) hψ]
  rw [show (successorIndices n) ‘ i = succ i from value_definableGraph _ _ _ hi]

theorem unaryCodedInstance_zero {ψ : V} (hψ : ψ ∈ formulaSet (membershipLanguageCode : V) ∅ 1) :
    unaryCodedInstance 1 0 ψ = ψ := by
  have he : (constantGraph 1 0 : V) = SetTheory.identity 1 := by
    apply function_eq_of_values (constantGraph_mem_function (1 : V) 1 0 (by simp)) (identity_mem_function 1)
    intro x hx
    have hx0 : x = 0 := by simpa [one_def] using hx
    rw [value_constantGraph 1 0 hx, identity_value hx, hx0]
  rw [unaryCodedInstance, he, renameMembershipFormula_identity (by simp) hψ]

noncomputable def swapCodedIndex (i j x : V) : V := by
  classical
  exact if x = i then j else if x = j then i else x

instance swapCodedIndex_definable : ℒₛₑₜ-function₃[V] swapCodedIndex := by
  have h : ℒₛₑₜ-relation₄[V] (fun y i j x ↦
      (x = i ∧ y = j) ∨ (x ≠ i ∧ x = j ∧ y = i) ∨ (x ≠ i ∧ x ≠ j ∧ y = x)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = swapCodedIndex (v 1) (v 2) (v 3) ↔ _
  unfold swapCodedIndex
  split_ifs <;> simp_all

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem swapCodedIndex_involutive (i j x : V) : swapCodedIndex i j (swapCodedIndex i j x) = x := by
  classical
  by_cases hxi : x = i
  · subst x
    by_cases hij : i = j <;> simp [swapCodedIndex, hij]
  · by_cases hxj : x = j
    · subst x
      simp [swapCodedIndex, hxi]
    · simp [swapCodedIndex, hxi, hxj]

noncomputable def swapCodedIndices (n i j : V) : V :=
  definableGraph n (swapCodedIndex i j) (by definability)

theorem swapCodedIndices_value {n i j x : V} (hx : x ∈ n) :
    (swapCodedIndices n i j) ‘ x = swapCodedIndex i j x := value_definableGraph _ _ _ hx

theorem swapCodedIndices_function {n i j : V} (hi : i ∈ n) (hj : j ∈ n) :
    swapCodedIndices n i j ∈ n ^ n := by
  apply definableGraph_mem_function_of_mapsTo
  intro x hx
  unfold swapCodedIndex
  split_ifs <;> assumption

theorem swapCodedIndices_compose {n i j : V} (hi : i ∈ n) (hj : j ∈ n) :
    compose (swapCodedIndices n i j) (swapCodedIndices n i j) = SetTheory.identity n := by
  have hr := swapCodedIndices_function hi hj
  apply function_eq_of_values (compose_function hr hr) (identity_mem_function n)
  intro x hx
  rw [value_compose_of_mem_function hr hr hx, swapCodedIndices_value (function_value_mem hr hx),
    swapCodedIndices_value hx, swapCodedIndex_involutive, identity_value hx]

theorem StandardCodedProvable.rename_singleton {T n m r φ : V}
    (hp : StandardCodedProvable T n ({φ} : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    StandardCodedProvable T m ({renameMembershipFormula n m r φ} : V) := by
  have he : renameCodedSequent n m r ({φ} : V) = ({renameMembershipFormula n m r φ} : V) := by
    ext x
    simp [mem_renameCodedSequent_iff]
  have hv := isCodedSequent_singleton hm (renameMembershipFormula_mem hp.valid.1 hm hr hφ)
  exact he ▸ hp.rename (he.symm ▸ hv) hr

theorem IsConsistentCodedFormula.of_renamed (hω : Schmerl.HasStandardOmega V) {T n m r φ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (h : IsConsistentCodedFormula T m (renameMembershipFormula n m r φ)) :
    IsConsistentCodedFormula T n φ := by
  refine ⟨hφ, ?_⟩
  rintro ⟨p, hp⟩
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hproof := (hp.to_standard hω).rename_singleton hm hr hnf
  rw [renameMembershipFormula_negate hn hm hr hφ] at hproof
  exact h.2 hproof.to_internal

theorem IsConsistentCodedFormula.permute (hω : Schmerl.HasStandardOmega V) {T n r φ : V}
    (h : IsConsistentCodedFormula T n φ) (hr : r ∈ n ^ n)
    (hinv : compose r r = SetTheory.identity n) :
    IsConsistentCodedFormula T n (renameMembershipFormula n n r φ) := by
  have hv := renameMembershipFormula_mem h.context h.context hr h.1
  apply IsConsistentCodedFormula.of_renamed hω hv h.context hr
  rw [renameMembershipFormula_compose h.context h.context h.context hr hr h.1,
    hinv, renameMembershipFormula_identity h.context h.1]
  exact h

end ZFVP
