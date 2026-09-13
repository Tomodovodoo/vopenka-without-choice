import ZFVP.SetTheory.AtomicMembership
import ZFVP.SetTheory.ForcingQuantifiers
import ZFVP.SetTheory.ClassFormulaForcingAction
import ZFVP.SetTheory.FormulaForcing
import ZFVP.ModelTheory.ForcingIsomorphismTransport

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingIsomorphism.surjective {P R Q S f : V}
    (h : IsForcingIsomorphism P R Q S f) (q : V) (hq : q ∈ Q) :
    ∃ p ∈ P, f ‘ p = q :=
  ⟨(converseGraph f) ‘ q, function_value_mem h.inverse_maps hq, h.value_inverse hq⟩

theorem atomicEquality_isomorphism_forward {P R Q S π σ τ p : V}
    (hπ : IsForcingIsomorphism P R Q S π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ atomicEquality P R σ τ) :
    π ‘ p ∈ atomicEquality Q S (nameAction π σ) (nameAction π τ) := by
  have h := forcingName_induction P
    (fun σ ↦ ∀ τ, IsForcingName P τ → ∀ p, p ∈ atomicEquality P R σ τ →
      π ‘ p ∈ atomicEquality Q S (nameAction π σ) (nameAction π τ)) (by definability) ?_ σ hσ
  · exact h τ hτ p hp
  intro σ hσ ih τ hτ p hp
  obtain ⟨hpP, hl, hr⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp hp
  apply (mem_atomicEquality_iff _ _ _ _ _).mpr
  refine ⟨function_value_mem hπ.1 hpP, ?_, ?_⟩
  · intro υ' s' hs' q' hq' hq'p hq's
    obtain ⟨υ, s, hs, he⟩ := (mem_nameAction_iff hσ π _).mp hs'
    obtain ⟨hυ, hs'⟩ := kpair_iff.mp he
    subst υ'
    subst s'
    obtain ⟨q, hq, hqq'⟩ := hπ.surjective q' hq'
    subst q'
    obtain ⟨r, hrP, hrq, ν, t, ht, hrt, hE⟩ := hl υ s hs q hq
      ((hπ.2.2.2 q hq p hpP).mpr hq'p)
      ((hπ.2.2.2 q hq s (forcingName_condition hσ hs)).mpr hq's)
    exact ⟨π ‘ r, function_value_mem hπ.1 hrP, (hπ.2.2.2 r hrP q hq).mp hrq,
      nameAction π ν, π ‘ t, (mem_nameAction_iff hτ π _).mpr ⟨ν, t, ht, rfl⟩,
      (hπ.2.2.2 r hrP t (forcingName_condition hτ ht)).mp hrt,
      ih υ s hs ν (forcingName_subname hτ ht) r hE⟩
  · intro ν' t' ht' q' hq' hq'p hq't
    obtain ⟨ν, t, ht, he⟩ := (mem_nameAction_iff hτ π _).mp ht'
    obtain ⟨hν, ht'⟩ := kpair_iff.mp he
    subst ν'
    subst t'
    obtain ⟨q, hq, hqq'⟩ := hπ.surjective q' hq'
    subst q'
    obtain ⟨r, hrP, hrq, υ, s, hs, hrs, hE⟩ := hr ν t ht q hq
      ((hπ.2.2.2 q hq p hpP).mpr hq'p)
      ((hπ.2.2.2 q hq t (forcingName_condition hτ ht)).mpr hq't)
    exact ⟨π ‘ r, function_value_mem hπ.1 hrP, (hπ.2.2.2 r hrP q hq).mp hrq,
      nameAction π υ, π ‘ s, (mem_nameAction_iff hσ π _).mpr ⟨υ, s, hs, rfl⟩,
      (hπ.2.2.2 r hrP s (forcingName_condition hσ hs)).mp hrs,
      ih υ s hs ν (forcingName_subname hτ ht) r hE⟩

theorem atomicEquality_isomorphism_iff {P R Q S π σ τ p : V}
    (hπ : IsForcingIsomorphism P R Q S π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ P) :
    π ‘ p ∈ atomicEquality Q S (nameAction π σ) (nameAction π τ) ↔ p ∈ atomicEquality P R σ τ := by
  constructor
  · intro hE
    have he := atomicEquality_isomorphism_forward hπ.inverse
      (nameAction_isName hπ.1 hσ) (nameAction_isName hπ.1 hτ) hE
    simpa only [hπ.name_inverse_cancel hσ, hπ.name_inverse_cancel hτ,
      converseGraph_value_value hπ.1 hπ.2.1 hp] using he
  · exact atomicEquality_isomorphism_forward hπ hσ hτ

theorem atomicMembership_isomorphism_forward {P R Q S π σ τ p : V}
    (hπ : IsForcingIsomorphism P R Q S π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ atomicMembership P R σ τ) :
    π ‘ p ∈ atomicMembership Q S (nameAction π σ) (nameAction π τ) := by
  obtain ⟨hpP, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hp
  apply (mem_atomicMembership_iff _ _ _ _ _).mpr
  refine ⟨function_value_mem hπ.1 hpP, ?_⟩
  intro q' hq' hq'p
  obtain ⟨q, hq, hqq'⟩ := hπ.surjective q' hq'
  subst q'
  obtain ⟨r, hr, hrq, ν, s, hνs, hrs, hE⟩ := hh q hq ((hπ.2.2.2 q hq p hpP).mpr hq'p)
  exact ⟨π ‘ r, function_value_mem hπ.1 hr, (hπ.2.2.2 r hr q hq).mp hrq,
    nameAction π ν, π ‘ s, (mem_nameAction_iff hτ π _).mpr ⟨ν, s, hνs, rfl⟩,
    (hπ.2.2.2 r hr s (forcingName_condition hτ hνs)).mp hrs,
    atomicEquality_isomorphism_forward hπ hσ (forcingName_subname hτ hνs) hE⟩

theorem atomicMembership_isomorphism_iff {P R Q S π σ τ p : V}
    (hπ : IsForcingIsomorphism P R Q S π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ P) :
    π ‘ p ∈ atomicMembership Q S (nameAction π σ) (nameAction π τ) ↔ p ∈ atomicMembership P R σ τ := by
  constructor
  · intro hM
    have hm := atomicMembership_isomorphism_forward hπ.inverse
      (nameAction_isName hπ.1 hσ) (nameAction_isName hπ.1 hτ) hM
    simpa only [hπ.name_inverse_cancel hσ, hπ.name_inverse_cancel hτ,
      converseGraph_value_value hπ.1 hπ.2.1 hp] using hm
  · exact atomicMembership_isomorphism_forward hπ hσ hτ

theorem forcingNegation_isomorphism_iff {P R Q S π A B p : V} (hπ : IsForcingIsomorphism P R Q S π)
    (hAB : ∀ q ∈ P, π ‘ q ∈ B ↔ q ∈ A) (hp : p ∈ P) :
    π ‘ p ∈ forcingNegation Q S B ↔ p ∈ forcingNegation P R A := by
  rw [mem_forcingNegation_iff, mem_forcingNegation_iff]
  constructor
  · rintro ⟨_, hh⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp hqA
    exact hh (π ‘ q) (function_value_mem hπ.1 hq) ((hπ.2.2.2 q hq p hp).mp hqp) ((hAB q hq).mpr hqA)
  · rintro ⟨_, hh⟩
    refine ⟨function_value_mem hπ.1 hp, ?_⟩
    intro q' hq' hq'p hq'B
    obtain ⟨q, hq, he⟩ := hπ.surjective q' hq'
    subst q'
    exact hh q hq ((hπ.2.2.2 q hq p hp).mpr hq'p) ((hAB q hq).mp hq'B)

theorem forcingClosure_isomorphism_iff {P R Q S π A B p : V} (hπ : IsForcingIsomorphism P R Q S π)
    (hA : A ⊆ P) (hB : B ⊆ Q) (hAB : ∀ q ∈ P, π ‘ q ∈ B ↔ q ∈ A) (hp : p ∈ P) :
    π ‘ p ∈ forcingClosure Q S B ↔ p ∈ forcingClosure P R A := by
  rw [mem_forcingClosure_iff, mem_forcingClosure_iff]
  constructor
  · rintro ⟨_, hh⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp
    obtain ⟨r', hr'B, hr'q⟩ := hh (π ‘ q) (function_value_mem hπ.1 hq) ((hπ.2.2.2 q hq p hp).mp hqp)
    obtain ⟨r, hr, he⟩ := hπ.surjective r' (hB r' hr'B)
    subst r'
    exact ⟨r, (hAB r hr).mp hr'B, (hπ.2.2.2 r hr q hq).mpr hr'q⟩
  · rintro ⟨_, hh⟩
    refine ⟨function_value_mem hπ.1 hp, ?_⟩
    intro q' hq' hq'p
    obtain ⟨q, hq, he⟩ := hπ.surjective q' hq'
    subst q'
    obtain ⟨r, hrA, hrq⟩ := hh q hq ((hπ.2.2.2 q hq p hp).mpr hq'p)
    exact ⟨π ‘ r, (hAB r (hA r hrA)).mpr hrA, (hπ.2.2.2 r (hA r hrA) q hq).mp hrq⟩

theorem forcingClassIntersection_isomorphism_iff {P R Q S π p : V} (hπ : IsForcingIsomorphism P R Q S π)
    (N M : V → Prop) (hN : ℒₛₑₜ-predicate N) (hM : ℒₛₑₜ-predicate M) (T : V → V)
    (hT : ∀ x, N x → M (T x)) (hsurj : ∀ y, M y → ∃ x, N x ∧ T x = y)
    (A B : V → V) (hA : ℒₛₑₜ-function₁ A) (hB : ℒₛₑₜ-function₁ B)
    (hAB : ∀ x, N x → ∀ q ∈ P, π ‘ q ∈ B (T x) ↔ q ∈ A x) (hp : p ∈ P) :
    π ‘ p ∈ forcingClassIntersection Q M hM B hB ↔ p ∈ forcingClassIntersection P N hN A hA := by
  rw [mem_forcingClassIntersection_iff, mem_forcingClassIntersection_iff]
  constructor
  · rintro ⟨_, hh⟩
    exact ⟨hp, fun x hx ↦ (hAB x hx p hp).mp (hh (T x) (hT x hx))⟩
  · rintro ⟨_, hh⟩
    refine ⟨function_value_mem hπ.1 hp, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact (hAB x hx p hp).mpr (hh x hx)

theorem forcingClassUnion_isomorphism_iff {P R Q S π p : V} (hπ : IsForcingIsomorphism P R Q S π)
    (N M : V → Prop) (hN : ℒₛₑₜ-predicate N) (hM : ℒₛₑₜ-predicate M) (T : V → V)
    (hT : ∀ x, N x → M (T x)) (hsurj : ∀ y, M y → ∃ x, N x ∧ T x = y)
    (A B : V → V) (hA : ℒₛₑₜ-function₁ A) (hB : ℒₛₑₜ-function₁ B)
    (hAB : ∀ x, N x → ∀ q ∈ P, π ‘ q ∈ B (T x) ↔ q ∈ A x) (hp : p ∈ P) :
    π ‘ p ∈ forcingClassUnion Q M hM B hB ↔ p ∈ forcingClassUnion P N hN A hA := by
  rw [mem_forcingClassUnion_iff, mem_forcingClassUnion_iff]
  constructor
  · rintro ⟨_, y, hy, hpB⟩
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact ⟨hp, x, hx, (hAB x hx p hp).mp hpB⟩
  · rintro ⟨_, x, hx, hpA⟩
    exact ⟨function_value_mem hπ.1 hp, T x, hT x hx, (hAB x hx p hp).mpr hpA⟩

theorem forcingAtomic_isomorphism_iff {P R Q S π p : V} (hπ : IsForcingIsomorphism P R Q S π)
    {n k : ℕ} (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ Empty n)
    (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i)) (hp : p ∈ P) :
    π ‘ p ∈ forcingAtomic Q S r ts (standardTuple (fun i ↦ nameAction π (v i))) ↔
      p ∈ forcingAtomic P R r ts (standardTuple v) := by
  cases r <;> simp only [forcingAtomic, forcingTermValue_nameAction]
  · exact atomicEquality_isomorphism_iff hπ (forcingTermValue_isName _ v hv) (forcingTermValue_isName _ v hv) hp
  · exact atomicMembership_isomorphism_iff hπ (forcingTermValue_isName _ v hv) (forcingTermValue_isName _ v hv) hp

theorem forcingFormula_isomorphism_iff {P R Q S π : V} (hR : IsForcingPreorder P R)
    (hS : IsForcingPreorder Q S) (hπ : IsForcingIsomorphism P R Q S π)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i))
    {p : V} (hp : p ∈ P) :
    π ‘ p ∈ forcingFormula Q S φ (standardTuple (fun i ↦ nameAction π (v i))) ↔
      p ∈ forcingFormula P R φ (standardTuple v) := by
  have hclosed : ∀ x, IsForcingName P x → IsForcingName Q (nameAction π x) :=
    fun _ hx ↦ nameAction_isName hπ.1 hx
  have hsurj : ∀ y, IsForcingName Q y → ∃ x, IsForcingName P x ∧ nameAction π x = y :=
    fun y hy ↦ ⟨nameAction (converseGraph π) y, nameAction_isName hπ.inverse_maps hy,
      hπ.name_cancel_inverse hy⟩
  induction φ generalizing p with
  | verum => exact iff_of_true (function_value_mem hπ.1 hp) hp
  | falsum => simp only [forcingFormula_falsum, not_mem_empty]
  | rel r ts => exact forcingAtomic_isomorphism_iff hπ r ts v hv hp
  | nrel r ts =>
    rw [forcingFormula_nrel, forcingFormula_nrel]
    exact forcingNegation_isomorphism_iff hπ
      (fun q hq ↦ forcingAtomic_isomorphism_iff hπ r ts v hv hq) hp
  | and φ ψ ihφ ihψ =>
    rw [forcingFormula_and, forcingFormula_and, mem_inter_iff, mem_inter_iff]
    exact and_congr (ihφ v hv hp) (ihψ v hv hp)
  | or φ ψ ihφ ihψ =>
    rw [forcingFormula_or, forcingFormula_or]
    apply forcingClosure_isomorphism_iff hπ
    · intro q hq
      rcases mem_union_iff.mp hq with hh | hh
      · exact (forcingFormula_regular hR φ _).1 q hh
      · exact (forcingFormula_regular hR ψ _).1 q hh
    · intro q hq
      rcases mem_union_iff.mp hq with hh | hh
      · exact (forcingFormula_regular hS φ _).1 q hh
      · exact (forcingFormula_regular hS ψ _).1 q hh
    · intro q hq
      rw [mem_union_iff, mem_union_iff]
      exact or_congr (ihφ v hv hq) (ihψ v hv hq)
    · exact hp
  | @all n φ ih =>
    rw [forcingFormula_all, forcingFormula_all]
    apply forcingClassIntersection_isomorphism_iff hπ (IsForcingName P) (IsForcingName Q)
      (by definability) (by definability) (nameAction π) hclosed hsurj
    · intro x hx q hq
      exact ih (x :> v) (fun i ↦ Fin.cases hx (fun j ↦ hv j) i) hq
    · exact hp
  | @exs n φ ih =>
    rw [forcingFormula_exs, forcingFormula_exs]
    unfold forcingExistential
    apply forcingClosure_isomorphism_iff hπ (forcingClassUnion_subset _ _ _ _ _) (forcingClassUnion_subset _ _ _ _ _)
    · intro q hq
      apply forcingClassUnion_isomorphism_iff hπ (IsForcingName P) (IsForcingName Q)
        (by definability) (by definability) (nameAction π) hclosed hsurj
      · intro x hx r hr
        exact ih (x :> v) (fun i ↦ Fin.cases hx (fun j ↦ hv j) i) hr
      · exact hq
    · exact hp

end ZFVP
