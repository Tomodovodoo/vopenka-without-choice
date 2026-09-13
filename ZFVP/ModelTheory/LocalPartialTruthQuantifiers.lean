import ZFVP.ModelTheory.LocalPartialTruth

/-! Quantifier equations for partial truth interpreted inside a transitive ZF set model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem localDomainTruth_prepend_iff (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (p : LevyPolarity) (k : ℕ) (n φ b : SetDomain U)
    (hn : n ∈ (ω : SetDomain U)) (hb : IsFunction b ∧ domain b = n) (x : SetDomain U) :
    LocalDomainTruth U p k (succ n.val) φ.val (assignmentPrepend n.val b.val x.val) ↔
      DomainTruth p k (succ n) φ (assignmentPrepend n b x) := by
  have he := localDomainTruth_iff U p k (succ n) φ (assignmentPrepend n b x)
  rw [TransitiveZF.succ_val U, TransitiveZF.assignmentPrepend_val U hn hb x] at he
  exact he

namespace LocalDomainTruth

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_iff {k : ℕ} {n φ b : V} (hn : n ∈ (ω : V))
    (hφ : IsLevyFormulaCode .sigma (k + 1) (succ n) φ) (hb : b ∈ U ^ n) :
    LocalDomainTruth U .sigma k n (existsCode φ) b ↔
      ∃ x ∈ U, LocalDomainTruth U .sigma k (succ n) φ (assignmentPrepend n b x) := by
  let := TransitiveZF.sequenceSupport U
  let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hn⟩
  let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) .sigma U _ hφ)).2⟩
  let b' : SetDomain U := ⟨b, function_mem_sequenceSupport (subset_refl U) hn hb⟩
  have hn' := (TransitiveZF.natural_iff U n').mpr hn
  have hb' := (TransitiveZF.function_on_iff U b' n').mpr ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩
  have hφ' := (TransitiveZF.levyCode_iff U .sigma (k + 1) (succ n') φ').mpr
    (by simpa only [TransitiveZF.succ_val U] using hφ)
  have he := domainSigmaTruth_exists hn' hφ' hb'
  change DomainTruth .sigma k n' (existsCode φ') b' ↔
    ∃ x : SetDomain U, DomainTruth .sigma k (succ n') φ' (assignmentPrepend n' b' x) at he
  rw [← localDomainTruth_iff U .sigma k n' (existsCode φ') b', TransitiveZF.existsCode_val U] at he
  simp only [← localDomainTruth_prepend_iff U .sigma k n' φ' b' hn' hb'] at he
  exact he.trans ⟨fun ⟨x, hx⟩ ↦ ⟨x.val, x.property, hx⟩, fun ⟨x, hx, hs⟩ ↦ ⟨⟨x, hx⟩, hs⟩⟩

theorem all_iff {k : ℕ} {n φ b : V} (hn : n ∈ (ω : V))
    (hφ : IsLevyFormulaCode .pi (k + 1) (succ n) φ) (hb : b ∈ U ^ n) :
    LocalDomainTruth U .pi k n (allCode φ) b ↔
      ∀ x ∈ U, LocalDomainTruth U .pi k (succ n) φ (assignmentPrepend n b x) := by
  let := TransitiveZF.sequenceSupport U
  let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hn⟩
  let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) .pi U _ hφ)).2⟩
  let b' : SetDomain U := ⟨b, function_mem_sequenceSupport (subset_refl U) hn hb⟩
  have hn' := (TransitiveZF.natural_iff U n').mpr hn
  have hb' := (TransitiveZF.function_on_iff U b' n').mpr ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩
  have hφ' := (TransitiveZF.levyCode_iff U .pi (k + 1) (succ n') φ').mpr
    (by simpa only [TransitiveZF.succ_val U] using hφ)
  have he := domainPiTruth_all hn' hφ' hb'
  change DomainTruth .pi k n' (allCode φ') b' ↔
    ∀ x : SetDomain U, DomainTruth .pi k (succ n') φ' (assignmentPrepend n' b' x) at he
  rw [← localDomainTruth_iff U .pi k n' (allCode φ') b', TransitiveZF.allCode_val U] at he
  simp only [← localDomainTruth_prepend_iff U .pi k n' φ' b' hn' hb'] at he
  exact he.trans ⟨fun h x hx ↦ h ⟨x, hx⟩, fun h x ↦ h x.val x.property⟩

theorem boundedAll_iff {p : LevyPolarity} {k : ℕ} {n i φ b : V}
    (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hφ : IsLevyFormulaCode p (k + 1) (succ n) φ) (hb : b ∈ U ^ n) :
    LocalDomainTruth U p k n (boundedAllCode i φ) b ↔
      ∀ x ∈ b ‘ i, LocalDomainTruth U p k (succ n) φ (assignmentPrepend n b x) := by
  let := TransitiveZF.sequenceSupport U
  let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hn⟩
  let i' : SetDomain U := ⟨i, (inferInstance : IsTransitive U).mem_trans hi n'.property⟩
  let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) p U _ hφ)).2⟩
  let b' : SetDomain U := ⟨b, function_mem_sequenceSupport (subset_refl U) hn hb⟩
  have hn' := (TransitiveZF.natural_iff U n').mpr hn
  have hb' := (TransitiveZF.function_on_iff U b' n').mpr ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩
  have hφ' := (TransitiveZF.levyCode_iff U p (k + 1) (succ n') φ').mpr
    (by simpa only [TransitiveZF.succ_val U] using hφ)
  have hi' : i' ∈ n' := hi
  have he := domainTruth_boundedAll hn' hi' hφ' hb'
  rw [← localDomainTruth_iff U p k n' (boundedAllCode i' φ') b', TransitiveZF.boundedAllCode_val U] at he
  simp only [← localDomainTruth_prepend_iff U p k n' φ' b' hn' hb'] at he
  let := hb'.1
  have hv := TransitiveZF.value_val U b' i' (by rw [hb'.2]; exact hi')
  apply he.trans
  constructor
  · intro h x hx
    have hxU := (inferInstance : IsTransitive U).mem_trans hx (function_value_mem hb hi)
    apply h ⟨x, hxU⟩
    change x ∈ (b' ‘ i').val
    rw [hv]
    exact hx
  · intro h x hx
    apply h x.val
    change x.val ∈ (b' ‘ i').val at hx
    rw [hv] at hx
    exact hx

theorem boundedExists_iff {p : LevyPolarity} {k : ℕ} {n i φ b : V}
    (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hφ : IsLevyFormulaCode p (k + 1) (succ n) φ) (hb : b ∈ U ^ n) :
    LocalDomainTruth U p k n (boundedExistsCode i φ) b ↔
      ∃ x ∈ b ‘ i, LocalDomainTruth U p k (succ n) φ (assignmentPrepend n b x) := by
  let := TransitiveZF.sequenceSupport U
  let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hn⟩
  let i' : SetDomain U := ⟨i, (inferInstance : IsTransitive U).mem_trans hi n'.property⟩
  let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) p U _ hφ)).2⟩
  let b' : SetDomain U := ⟨b, function_mem_sequenceSupport (subset_refl U) hn hb⟩
  have hn' := (TransitiveZF.natural_iff U n').mpr hn
  have hb' := (TransitiveZF.function_on_iff U b' n').mpr ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩
  have hφ' := (TransitiveZF.levyCode_iff U p (k + 1) (succ n') φ').mpr
    (by simpa only [TransitiveZF.succ_val U] using hφ)
  have hi' : i' ∈ n' := hi
  have he := domainTruth_boundedExists hn' hi' hφ' hb'
  rw [← localDomainTruth_iff U p k n' (boundedExistsCode i' φ') b', TransitiveZF.boundedExistsCode_val U] at he
  simp only [← localDomainTruth_prepend_iff U p k n' φ' b' hn' hb'] at he
  let := hb'.1
  have hv := TransitiveZF.value_val U b' i' (by rw [hb'.2]; exact hi')
  apply he.trans
  constructor
  · rintro ⟨x, hx, hs⟩
    refine ⟨x.val, ?_, hs⟩
    change x.val ∈ (b' ‘ i').val at hx
    rw [hv] at hx
    exact hx
  · rintro ⟨x, hx, hs⟩
    have hxU := (inferInstance : IsTransitive U).mem_trans hx (function_value_mem hb hi)
    refine ⟨⟨x, hxU⟩, ?_, hs⟩
    change x ∈ (b' ‘ i').val
    rw [hv]
    exact hx

end LocalDomainTruth

end ZFVP
