import ZFVP.SetTheory.ForcingConjugation
import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.AtomicForcingAction
import ZFVP.SetTheory.AtomicEqualityTransitivity
import ZFVP.SetTheory.ForcingFormulaNameAction

/-! Stabilizers of names up to forced equality (Karagila–Schilhan's `res(ẋ)`), and the normal
filter they generate on the names satisfying a fixed formula `φ`: the Solovay-style symmetric
system `O(P, {ẋ : ⊩ φ(ẋ)})`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Every condition forces `σ = τ`. -/
def ForcedEqual (P R σ τ : V) : Prop := ∀ p ∈ P, p ∈ atomicEquality P R σ τ

instance forcedEqual_definable (P R : V) : ℒₛₑₜ-relation[V] (ForcedEqual P R) := by
  unfold ForcedEqual
  definability

theorem forcedEqual_refl {P R : V} (hR : IsForcingPreorder P R) (σ : V) : ForcedEqual P R σ σ := by
  intro p hp
  rw [atomicEquality_refl hR]
  exact hp

theorem forcedEqual_symm {P R σ τ : V} (h : ForcedEqual P R σ τ) : ForcedEqual P R τ σ := by
  intro p hp
  rw [atomicEquality_symm]
  exact h p hp

theorem forcedEqual_trans {P R σ τ υ : V} (hR : IsForcingPreorder P R) (h₁ : ForcedEqual P R σ τ)
    (h₂ : ForcedEqual P R τ υ) : ForcedEqual P R σ υ :=
  fun p hp ↦ atomicEquality_trans hR σ τ υ p (h₁ p hp) (h₂ p hp)

/-- Forced equality is invariant under automorphisms acting on names. -/
theorem forcedEqual_nameAction_iff {P R π σ τ : V} (hπ : IsForcingAutomorphism P R π)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) :
    ForcedEqual P R (nameAction π σ) (nameAction π τ) ↔ ForcedEqual P R σ τ := by
  constructor
  · intro h p hp
    exact (atomicEquality_nameAction_iff hπ hσ hτ hp).mp (h _ (function_value_mem hπ.1 hp))
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := forcingAutomorphism_surjective hπ q hq
    exact (atomicEquality_nameAction_iff hπ hσ hτ hp).mpr (h p hp)

/-- Forced truth of `φ(τ)` is invariant under automorphisms acting on names. -/
theorem forcedFormula_nameAction_iff {P R π τ : V} (hR : IsForcingPreorder P R)
    (hπ : IsForcingAutomorphism P R π) (φ : SetTheorySemisentence 1) (hτ : IsForcingName P τ) :
    P ⊆ forcingFormula P R φ (standardTuple ![nameAction π τ]) ↔
      P ⊆ forcingFormula P R φ (standardTuple ![τ]) := by
  have key : ∀ p ∈ P, π ‘ p ∈ forcingFormula P R φ (standardTuple ![nameAction π τ]) ↔
      p ∈ forcingFormula P R φ (standardTuple ![τ]) := by
    intro p hp
    have := forcingFormula_nameAction_iff hR hπ φ ![τ] (fun i ↦ by
      rw [Fin.fin_one_eq_zero i]; exact hτ) hp
    rwa [show (fun i ↦ nameAction π (![τ] i)) = ![nameAction π τ] by
      simp [Fin.forall_fin_succ, funext_iff]] at this
  constructor
  · intro h p hp
    exact (key p hp).mp (h _ (function_value_mem hπ.1 hp))
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := forcingAutomorphism_surjective hπ q hq
    exact (key p hp).mpr (h p hp)

/-- The automorphisms in `Γ` fixing every name in `E` up to forced equality. -/
noncomputable def forcedStabilizer (P R Γ E : V) : V :=
  {π ∈ Γ ; ∀ τ ∈ E, ForcedEqual P R (nameAction π τ) τ}

theorem mem_forcedStabilizer (P R Γ E π : V) :
    π ∈ forcedStabilizer P R Γ E ↔ π ∈ Γ ∧ ∀ τ ∈ E, ForcedEqual P R (nameAction π τ) τ :=
  mem_sep_iff

instance forcedStabilizer_definable (P R : V) : ℒₛₑₜ-function₂[V] (forcedStabilizer P R) := by
  have h : ℒₛₑₜ-relation₃[V] (fun H Γ E ↦ ∀ π, π ∈ H ↔
      π ∈ Γ ∧ ∀ τ ∈ E, ForcedEqual P R (nameAction π τ) τ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcedStabilizer P R (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_forcedStabilizer]

theorem forcedStabilizer_subgroup {P R Γ E : V} (hR : IsForcingPreorder P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hE : ∀ τ ∈ E, IsForcingName P τ) :
    IsForcingSubgroup P Γ (forcedStabilizer P R Γ E) := by
  refine ⟨fun π hπ ↦ ((mem_forcedStabilizer P R Γ E π).mp hπ).1,
    (mem_forcedStabilizer P R Γ E _).mpr ⟨hΓ.2.1, fun τ hτ ↦ ?_⟩, ?_, ?_⟩
  · rw [nameAction_identity (hE τ hτ)]
    exact forcedEqual_refl hR τ
  · intro π hπ ρ hρ
    obtain ⟨hπΓ, hπE⟩ := (mem_forcedStabilizer P R Γ E π).mp hπ
    obtain ⟨hρΓ, hρE⟩ := (mem_forcedStabilizer P R Γ E ρ).mp hρ
    have ha := hΓ.1 _ hπΓ
    have hb := hΓ.1 _ hρΓ
    refine (mem_forcedStabilizer P R Γ E _).mpr ⟨hΓ.2.2.1 _ hπΓ _ hρΓ, fun τ hτ ↦ ?_⟩
    rw [← nameAction_compose ha.1 hb.1 (hE τ hτ)]
    refine forcedEqual_trans hR ?_ (hρE τ hτ)
    exact (forcedEqual_nameAction_iff hb (nameAction_isName ha.1 (hE τ hτ)) (hE τ hτ)).mpr (hπE τ hτ)
  · intro π hπ
    obtain ⟨hπΓ, hπE⟩ := (mem_forcedStabilizer P R Γ E π).mp hπ
    have ha := hΓ.1 _ hπΓ
    have hi := forcingAutomorphism_inverse ha
    refine (mem_forcedStabilizer P R Γ E _).mpr ⟨hΓ.2.2.2 _ hπΓ, fun τ hτ ↦ ?_⟩
    have := (forcedEqual_nameAction_iff hi (hE τ hτ) (nameAction_isName ha.1 (hE τ hτ))).mpr
      (forcedEqual_symm (hπE τ hτ))
    rwa [nameAction_compose ha.1 hi.1 (hE τ hτ), forcingAutomorphism_compose_inverse ha,
      nameAction_identity (hE τ hτ)] at this

theorem forcedStabilizer_union (P R Γ E K : V) :
    forcedStabilizer P R Γ (E ∪ K) = forcedStabilizer P R Γ E ∩ forcedStabilizer P R Γ K := by
  ext π
  simp only [mem_forcedStabilizer, mem_union_iff, mem_inter_iff]
  constructor
  · rintro ⟨hg, hf⟩
    exact ⟨⟨hg, fun τ hτ ↦ hf τ (Or.inl hτ)⟩, hg, fun τ hτ ↦ hf τ (Or.inr hτ)⟩
  · rintro ⟨⟨hg, he⟩, _, hk⟩
    exact ⟨hg, fun τ hτ ↦ hτ.elim (he τ) (hk τ)⟩

theorem forcedStabilizer_conjugate_subset {P R Γ E π H : V} (hR : IsForcingPreorder P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hπ : π ∈ Γ) (hE : ∀ τ ∈ E, IsForcingName P τ)
    (hEH : forcedStabilizer P R Γ E ⊆ H) :
    forcedStabilizer P R Γ (repl (nameAction π) (by definability) E) ⊆ conjugateSubgroup π H := by
  intro θ hθ
  obtain ⟨hθΓ, hθE⟩ := (mem_forcedStabilizer _ _ _ _ _).mp hθ
  have ha := hΓ.1 _ hπ
  have hb := hΓ.1 _ hθΓ
  have hi := forcingAutomorphism_inverse ha
  have : IsFunction π := IsFunction.of_mem ha.1
  let ρ := conjugatePermutation (converseGraph π) θ
  have hρΓ : ρ ∈ Γ := by
    unfold ρ conjugatePermutation
    exact hΓ.2.2.1 _ (hΓ.2.2.1 _ (hΓ.2.2.2 _ (hΓ.2.2.2 _ hπ)) _ hθΓ) _ (hΓ.2.2.2 _ hπ)
  have hρE : ∀ τ ∈ E, ForcedEqual P R (nameAction ρ τ) τ := by
    intro τ hτ
    have hτ' : nameAction π τ ∈ repl (nameAction π) (by definability) E :=
      (repl_spec (by definability)).mpr ⟨τ, hτ, rfl⟩
    have hθτ := hθE _ hτ'
    have hπτ := nameAction_isName ha.1 (hE τ hτ)
    have h1 := (forcedEqual_nameAction_iff hi (nameAction_isName hb.1 hπτ) hπτ).mpr hθτ
    rw [nameAction_compose ha.1 hi.1 (hE τ hτ), forcingAutomorphism_compose_inverse ha,
      nameAction_identity (hE τ hτ)] at h1
    have hρτ : nameAction ρ τ = nameAction (converseGraph π) (nameAction θ (nameAction π τ)) := by
      rw [nameAction_compose ha.1 hb.1 (hE τ hτ),
        nameAction_compose (forcingAutomorphism_compose ha hb).1 hi.1 (hE τ hτ)]
      show nameAction (compose (compose (converseGraph (converseGraph π)) θ) (converseGraph π)) τ = _
      rw [converseGraph_involutive]
    rw [hρτ]
    exact h1
  exact (mem_conjugateSubgroup π H θ).mpr
    ⟨ρ, hEH _ ((mem_forcedStabilizer _ _ _ _ _).mpr ⟨hρΓ, hρE⟩),
      (conjugatePermutation_cancel_inverse ha hb).symm⟩

/-- The names `τ` with `⊩ φ(τ)`. -/
def IsForcedName (P R : V) (φ : SetTheorySemisentence 1) (τ : V) : Prop :=
  IsForcingName P τ ∧ P ⊆ forcingFormula P R φ (standardTuple ![τ])

instance isForcedName_definable (P R : V) (φ : SetTheorySemisentence 1) :
    ℒₛₑₜ-predicate[V] (IsForcedName P R φ) := by
  unfold IsForcedName
  simp only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ]
  definability

theorem isForcedName_nameAction {P R π τ : V} (hR : IsForcingPreorder P R)
    (hπ : IsForcingAutomorphism P R π) (φ : SetTheorySemisentence 1) (hτ : IsForcedName P R φ τ) :
    IsForcedName P R φ (nameAction π τ) :=
  ⟨nameAction_isName hπ.1 hτ.1, (forcedFormula_nameAction_iff hR hπ φ hτ.1).mpr hτ.2⟩

/-- The filter on `Γ` generated by the forced stabilizers of finite sets of names in the class `N`. -/
noncomputable def forcedStabilizerFilter (P R Γ : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) : V :=
  sep (℘ Γ) (fun H ↦ IsForcingSubgroup P Γ H ∧ ∃ E, IsInternallyFinite E ∧
    (∀ τ ∈ E, N τ) ∧ forcedStabilizer P R Γ E ⊆ H)
    (by have := hN; have := forcedStabilizer_definable P R; definability)

theorem mem_forcedStabilizerFilter (P R Γ : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (H : V) :
    H ∈ forcedStabilizerFilter P R Γ N hN ↔ IsForcingSubgroup P Γ H ∧ ∃ E, IsInternallyFinite E ∧
      (∀ τ ∈ E, N τ) ∧ forcedStabilizer P R Γ E ⊆ H := by
  simp only [forcedStabilizerFilter, mem_sep_iff, mem_power_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.1, h⟩⟩

theorem forcedStabilizer_mem_forcedStabilizerFilter {P R Γ E : V} (hR : IsForcingPreorder P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) {N : V → Prop} (hN : ℒₛₑₜ-predicate N)
    (hNname : ∀ τ, N τ → IsForcingName P τ) (hEf : IsInternallyFinite E) (hE : ∀ τ ∈ E, N τ) :
    forcedStabilizer P R Γ E ∈ forcedStabilizerFilter P R Γ N hN :=
  (mem_forcedStabilizerFilter P R Γ N hN _).mpr
    ⟨forcedStabilizer_subgroup hR hΓ (fun τ hτ ↦ hNname τ (hE τ hτ)), E, hEf, hE, fun _ h ↦ h⟩

/-- For a class of names closed under the action of `Γ`, the generated filter is normal. -/
theorem forcedStabilizerFilter_normal {P R Γ : V} (hR : IsForcingPreorder P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) {N : V → Prop} (hN : ℒₛₑₜ-predicate N)
    (hNname : ∀ τ, N τ → IsForcingName P τ)
    (hNact : ∀ π ∈ Γ, ∀ τ, N τ → N (nameAction π τ)) :
    IsNormalSubgroupFilter P Γ (forcedStabilizerFilter P R Γ N hN) := by
  refine ⟨fun H hH ↦ ((mem_forcedStabilizerFilter P R Γ N hN H).mp hH).1, ?_, ?_, ?_, ?_⟩
  · exact (mem_forcedStabilizerFilter P R Γ N hN Γ).mpr
      ⟨forcingGroup_subgroup_self hΓ, ∅, internallyFinite_empty, by simp,
        fun π hπ ↦ ((mem_forcedStabilizer _ _ _ _ _).mp hπ).1⟩
  · intro H hH K hK hHK
    obtain ⟨_, E, hEf, hE, hEH⟩ := (mem_forcedStabilizerFilter P R Γ N hN H).mp hH
    exact (mem_forcedStabilizerFilter P R Γ N hN K).mpr ⟨hK, E, hEf, hE, subset_trans hEH hHK⟩
  · intro H hH K hK
    obtain ⟨hHs, E, hEf, hE, hEH⟩ := (mem_forcedStabilizerFilter P R Γ N hN H).mp hH
    obtain ⟨hKs, D, hDf, hD, hDK⟩ := (mem_forcedStabilizerFilter P R Γ N hN K).mp hK
    refine (mem_forcedStabilizerFilter P R Γ N hN _).mpr
      ⟨forcingSubgroup_inter hHs hKs, E ∪ D, internallyFinite_union hEf hDf, ?_, ?_⟩
    · intro τ hτ
      exact (mem_union_iff.mp hτ).elim (hE τ) (hD τ)
    · rw [forcedStabilizer_union]
      intro π hπ
      exact mem_inter_iff.mpr ⟨hEH _ (mem_inter_iff.mp hπ).1, hDK _ (mem_inter_iff.mp hπ).2⟩
  · intro π hπ H hH
    obtain ⟨hHs, E, hEf, hE, hEH⟩ := (mem_forcedStabilizerFilter P R Γ N hN H).mp hH
    refine (mem_forcedStabilizerFilter P R Γ N hN _).mpr
      ⟨conjugateSubgroup_subgroup hΓ hπ hHs, repl (nameAction π) (by definability) E,
        internallyFinite_repl _ _ hEf, ?_,
        forcedStabilizer_conjugate_subset hR hΓ hπ (fun τ hτ ↦ hNname τ (hE τ hτ)) hEH⟩
    intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := (repl_spec (by definability)).mp hσ
    exact hNact π hπ τ (hE τ hτ)

/-- Karagila–Schilhan's `O(P, {ẋ : ⊩ φ(ẋ)})`: the filter generated by forced stabilizers of
finitely many names satisfying `φ` is normal. -/
theorem forcedNameFilter_normal {P R Γ : V} (hR : IsForcingPreorder P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (φ : SetTheorySemisentence 1) :
    IsNormalSubgroupFilter P Γ (forcedStabilizerFilter P R Γ (IsForcedName P R φ) inferInstance) :=
  forcedStabilizerFilter_normal hR hΓ _ (fun _ h ↦ h.1)
    (fun π hπ τ hτ ↦ isForcedName_nameAction hR (hΓ.1 π hπ) φ hτ)

end ZFVP
