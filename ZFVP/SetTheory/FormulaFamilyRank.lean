import ZFVP.Syntax.Formulas
import ZFVP.ModelTheory.MembershipStructure

/-! Rank bound for the internal formula family of the membership language.

Modules that use `formulaFamily membershipLanguageCode ∅` often need to know that this set
appears at a specific stage of the cumulative hierarchy, and so far they carried that as a
hypothesis. The bound proved here is the sharp one: every code in the family is hereditarily
finite, so the family is a subset of `hierarchy ω` and a member of `hierarchy (succ ω)`, which
is well below `hierarchy (ordinalAdd ω ω)`.

The argument is by minimality. `formulaFamily L Γ` is contained in every set satisfying
`IsFormulaClosed L Γ`, so it is enough to check that `hierarchy ω` is formula closed for
`L = membershipLanguageCode` and `Γ = ∅`. Two features of that language make this work without
any internal induction on finite functions: there are no function symbols and no free variables,
so terms are just bound-variable codes, and every relation symbol has arity `2`, so an argument
tuple is the explicit pair `{⟨0, t₀⟩ₖ, ⟨1, t₁⟩ₖ}`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem omega_stage_succ_closed : ∀ β ∈ (ω : V), succ β ∈ (ω : V) := fun _ h ↦ ω_succ_closed h

theorem mem_hierarchy_omega_of_mem_omega {n : V} (hn : n ∈ (ω : V)) : n ∈ hierarchy (ω : V) :=
  ordinal_subset_hierarchy (ω : V) n hn

theorem kpair_mem_hierarchy_omega {x y : V} (hx : x ∈ hierarchy (ω : V))
    (hy : y ∈ hierarchy (ω : V)) : ⟨x, y⟩ₖ ∈ hierarchy (ω : V) :=
  kpair_mem_hierarchy_limit omega_stage_succ_closed hx hy

/-- A function with domain `2` is the pair of its two value pairs. -/
theorem function_two_eq_pair {B f : V} (hf : f ∈ B ^ (2 : V)) :
    f = ({⟨(0 : V), f ‘ (0 : V)⟩ₖ, ⟨(1 : V), f ‘ (1 : V)⟩ₖ} : V) := by
  have hfun : IsFunction f := IsFunction.of_mem hf
  have hdom : domain f = (2 : V) := domain_eq_of_mem_function hf
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf p hp)
    have hv : f ‘ x = y := value_eq_of_kpair_mem hp
    rcases (mem_two_iff x).mp hx with rfl | rfl
    · simp [hv]
    · simp [hv]
  · intro hp
    have h0 : (0 : V) ∈ domain f := by rw [hdom]; simp
    have h1 : (1 : V) ∈ domain f := by rw [hdom]; simp
    rcases (show p = ⟨(0 : V), f ‘ (0 : V)⟩ₖ ∨ p = ⟨(1 : V), f ‘ (1 : V)⟩ₖ by simpa using hp)
      with rfl | rfl
    · exact kpair_value_mem h0
    · exact kpair_value_mem h1

/-- A function with domain `2` and values in `hierarchy ω` lies in `hierarchy ω`. -/
theorem function_two_mem_hierarchy_omega {B f : V} (hf : f ∈ B ^ (2 : V))
    (hB : B ⊆ hierarchy (ω : V)) : f ∈ hierarchy (ω : V) := by
  rw [function_two_eq_pair hf]
  refine pair_mem_hierarchy_limit omega_stage_succ_closed
    (kpair_mem_hierarchy_omega (mem_hierarchy_omega_of_mem_omega zero_mem_ω)
      (hB _ (function_value_mem hf (by simp))))
    (kpair_mem_hierarchy_omega (mem_hierarchy_omega_of_mem_omega one_mem_ω)
      (hB _ (function_value_mem hf (by simp))))

theorem functionSymbols_membershipLanguageCode :
    functionSymbols (membershipLanguageCode : V) = ∅ := by simp [membershipLanguageCode]

theorem relationSymbols_membershipLanguageCode :
    relationSymbols (membershipLanguageCode : V) = (2 : V) := by simp [membershipLanguageCode]

theorem relationArity_membershipLanguageCode {s : V}
    (hs : s ∈ relationSymbols (membershipLanguageCode : V)) :
    (relationArities (membershipLanguageCode : V)) ‘ s = (2 : V) := by
  rw [show relationArities (membershipLanguageCode : V) = constantGraph (2 : V) (2 : V) by
    simp [membershipLanguageCode]]
  exact value_constantGraph _ _ (by simpa [relationSymbols_membershipLanguageCode] using hs)

/-- With no function symbols and no free variables, terms are bound-variable codes. -/
theorem membership_termSet_subset_hierarchy_omega {n : V} (hn : n ∈ (ω : V)) :
    termSet (membershipLanguageCode : V) ∅ n ⊆ hierarchy (ω : V) := by
  apply termSet_minimal
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [boundVarCode]
    exact kpair_mem_hierarchy_omega (mem_hierarchy_omega_of_mem_omega zero_mem_ω)
      (mem_hierarchy_omega_of_mem_omega (IsTransitive.ω.mem_trans hi hn))
  · intro x hx
    exact (not_mem_empty hx).elim
  · intro f hf
    rw [functionSymbols_membershipLanguageCode] at hf
    exact (not_mem_empty hf).elim

theorem membership_atomicArguments_mem_hierarchy_omega {n r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments (membershipLanguageCode : V) ∅ n r args) :
    r ∈ hierarchy (ω : V) ∧ args ∈ hierarchy (ω : V) := by
  have hterm := membership_termSet_subset_hierarchy_omega hn
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · refine ⟨?_, function_two_mem_hierarchy_omega ha hterm⟩
    simp only [equalityToken]
    exact mem_hierarchy_omega_of_mem_omega empty_mem_ω
  · rw [relationArity_membershipLanguageCode hs] at ha
    refine ⟨?_, function_two_mem_hierarchy_omega ha hterm⟩
    simp only [relationToken]
    refine kpair_mem_hierarchy_omega (mem_hierarchy_omega_of_mem_omega one_mem_ω)
      (mem_hierarchy_omega_of_mem_omega ?_)
    have hs2 : s ∈ (2 : V) := by
      simpa [relationSymbols_membershipLanguageCode] using hs
    exact IsTransitive.ω.mem_trans hs2 two_mem_ω

/-- `hierarchy ω` is closed under all eight formula constructors for the membership language. -/
theorem hierarchy_omega_formulaClosed :
    IsFormulaClosed (membershipLanguageCode : V) ∅ (hierarchy (ω : V)) := by
  intro n hn
  have : IsTransitive (hierarchy (ω : V)) := hierarchy_transitive _
  have hnU : n ∈ hierarchy (ω : V) := mem_hierarchy_omega_of_mem_omega hn
  have hzero : (0 : V) ∈ hierarchy (ω : V) := mem_hierarchy_omega_of_mem_omega zero_mem_ω
  have hempty : (∅ : V) ∈ hierarchy (ω : V) := mem_hierarchy_omega_of_mem_omega empty_mem_ω
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact kpair_mem_hierarchy_omega hnU
      (by simp only [truthCode]; exact kpair_mem_hierarchy_omega hzero hempty)
  · exact kpair_mem_hierarchy_omega hnU
      (by simp only [falsityCode]
          exact kpair_mem_hierarchy_omega
            (mem_hierarchy_omega_of_mem_omega one_mem_ω) hempty)
  · intro r args harg
    obtain ⟨hr, hargs⟩ := membership_atomicArguments_mem_hierarchy_omega hn harg
    refine ⟨kpair_mem_hierarchy_omega hnU ?_, kpair_mem_hierarchy_omega hnU ?_⟩
    · simp only [atomCode]
      exact kpair_mem_hierarchy_omega
        (mem_hierarchy_omega_of_mem_omega (ofNat_mem_ω 2)) (kpair_mem_hierarchy_omega hr hargs)
    · simp only [negAtomCode]
      exact kpair_mem_hierarchy_omega
        (mem_hierarchy_omega_of_mem_omega (ofNat_mem_ω 3)) (kpair_mem_hierarchy_omega hr hargs)
  · intro φ ψ hφ hψ
    have hφ' : φ ∈ hierarchy (ω : V) :=
      (kpair_components_mem_transitive (U := hierarchy (ω : V)) hφ).2
    have hψ' : ψ ∈ hierarchy (ω : V) :=
      (kpair_components_mem_transitive (U := hierarchy (ω : V)) hψ).2
    refine ⟨kpair_mem_hierarchy_omega hnU ?_, kpair_mem_hierarchy_omega hnU ?_⟩
    · simp only [andCode]
      exact kpair_mem_hierarchy_omega
        (mem_hierarchy_omega_of_mem_omega (ofNat_mem_ω 4)) (kpair_mem_hierarchy_omega hφ' hψ')
    · simp only [orCode]
      exact kpair_mem_hierarchy_omega
        (mem_hierarchy_omega_of_mem_omega (ofNat_mem_ω 5)) (kpair_mem_hierarchy_omega hφ' hψ')
  · intro φ hφ
    have hφ' : φ ∈ hierarchy (ω : V) :=
      (kpair_components_mem_transitive (U := hierarchy (ω : V)) hφ).2
    refine ⟨kpair_mem_hierarchy_omega hnU ?_, kpair_mem_hierarchy_omega hnU ?_⟩
    · simp only [allCode]
      exact kpair_mem_hierarchy_omega (mem_hierarchy_omega_of_mem_omega (ofNat_mem_ω 6)) hφ'
    · simp only [existsCode]
      exact kpair_mem_hierarchy_omega (mem_hierarchy_omega_of_mem_omega (ofNat_mem_ω 7)) hφ'

/-- Every code in the membership formula family is hereditarily finite. -/
theorem formulaFamily_subset_hierarchy_omega :
    (formulaFamily membershipLanguageCode ∅ : V) ⊆ hierarchy (ω : V) :=
  formulaFamily_minimal hierarchy_omega_formulaClosed

/-- The sharp stage: the family itself appears one step above `hierarchy ω`. -/
theorem formulaFamily_mem_hierarchy_succ_omega :
    (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (succ (ω : V)) := by
  rw [hierarchy_succ]
  exact mem_power_iff.mpr formulaFamily_subset_hierarchy_omega

/-- Form for callers: any stage past `ω` contains the family. -/
theorem formulaFamily_mem_hierarchy_of_mem_omega {γ : V} [IsOrdinal γ] (h : (ω : V) ∈ γ) :
    (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy γ := by
  refine hierarchy_mono (α := succ (ω : V)) ?_ _ formulaFamily_mem_hierarchy_succ_omega
  intro z hz
  rcases mem_succ_iff.mp hz with rfl | hzω
  · exact h
  · exact IsOrdinal.toIsTransitive.mem_trans hzω h

/-- Form requested by callers that carry an explicit bound `δ = succ ω`. -/
theorem formulaFamily_mem_hierarchy_of_subset {γ : V} [IsOrdinal γ] (h : succ (ω : V) ∈ γ) :
    (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy γ :=
  formulaFamily_mem_hierarchy_of_mem_omega (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (ω : V)) h)

/-- The stage the rest of the development asks for. -/
theorem formulaFamily_mem_hierarchy_omega_two :
    (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)) :=
  formulaFamily_mem_hierarchy_of_mem_omega (ordinalAdd_omega_gt (ω : V))

end ZFVP
