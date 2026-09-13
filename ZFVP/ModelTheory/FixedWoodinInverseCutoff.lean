import ZFVP.SetTheory.FixedNamedPrefixCutoffTests
import ZFVP.ModelTheory.WoodinSparseOwnCutoffs
import ZFVP.ModelTheory.WoodinSparseActualInverseRankAgreement

/-! Fixed cutoff tests at the completed sparse inverse-stage parameters.
The constructed iteration supplies the forcing invariants and a successful least
cutoff, which is identified with the actual stage cardinal. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinNamedPrefixCutoff_least_of_inaccessible {P R one γ τ : V}
    (hc : IsChoicelessInaccessible (woodinNamedPrefixCutoff P R one γ τ)) :
    IsLeastOrdinal (IsWoodinNamedPrefixCutoff P R one γ τ) (woodinNamedPrefixCutoff P R one γ τ) := by
  have he := (leastOrdinalOrZero_eq_iff (fun γ δ ↦ IsWoodinNamedPrefixCutoff P R one γ τ δ)
    (by definability) γ (woodinNamedPrefixCutoff P R one γ τ)).mp rfl
  rcases he with h | ⟨_, hzero⟩
  · exact h
  · have hw := hc.2.1
    rw [hzero, zero_def] at hw
    exact (not_mem_empty hw).elim

theorem woodinSparse_fixed_inverseCutoff_context {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let c := woodinSparsePrefixCode θ
    let P := woodinSparseInverseBase θ c
    let R := woodinSparseInverseOrder θ c
    let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
    let τ := hartogsNumberName P R (checkName ∅ γ)
    let δ := (kpair.π₂ (woodinIterationRec θ)) ‘ θ;
    IsForcingPreorder P R ∧ IsForcingTop P R ∅ ∧ IsForcingName P τ ∧
      (∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ])) ∧
      IsLeastOrdinal (IsWoodinNamedPrefixCutoff P R ∅ γ τ) δ := by
  dsimp only
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hi := woodinSparsePrefix_inverse_rankInputs hΩ hAC hθ h0 (ordinal_limit_of_not_successor hlim) hn
  have he := woodinSparsePrefix_inverse_cutoff hΩ hAC hsub h0 hlim hn
  have hc := ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.inaccessible θ (mem_succ_self θ)
  rw [← he] at hc
  have hl := woodinNamedPrefixCutoff_least_of_inaccessible hc
  change IsLeastOrdinal _ (woodinSparseInverseCutoff θ (woodinSparsePrefixCode θ)) at hl
  rw [he] at hl
  refine ⟨hi.preorder, hi.top, hartogsNumberName_isName _ _ _, ?_, hl⟩
  intro p hp
  exact forces_zeroMember_of_regular hi.preorder hi.top hp
    ⟨_, hartogsNumberName_isName _ _ _⟩ (hi.regular p hp)

theorem woodinSparse_fixed_inverseCutoff_tests {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let c := woodinSparsePrefixCode θ
    let P := woodinSparseInverseBase θ c
    let R := woodinSparseInverseOrder θ c
    let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
    let τ := hartogsNumberName P R (checkName ∅ γ)
    let δ := (kpair.π₂ (woodinIterationRec θ)) ‘ θ;
    fixedPiTwoNamedPrefixCutoffFormula.Evalb ![P, R, ∅, γ, τ, δ] ∧
      fixedSigmaTwoSmallerNamedPrefixFailuresFormula.Evalb ![P, R, ∅, γ, τ, δ] := by
  dsimp only
  obtain ⟨hR, ht, hτ, hz, hleast⟩ := woodinSparse_fixed_inverseCutoff_context hΩ hAC hθ h0 hlim hn
  refine ⟨(eval_fixedPiTwoNamedPrefixCutoffFormula hR ht hτ hz).mpr hleast.2.1, ?_⟩
  exact (eval_fixedSigmaTwoSmallerNamedPrefixFailuresFormula hR ht hτ hz).mpr
    ((isLeastOrdinal_iff_no_smaller _ _).mp hleast).2.2

theorem woodinSparse_fixed_inverseSelector_iff {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) (δ : V) :
    let c := woodinSparsePrefixCode θ
    let P := woodinSparseInverseBase θ c
    let R := woodinSparseInverseOrder θ c
    let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
    fixedSuccessfulNamedPrefixSelectorFormula.Evalb
      ![δ, P, R, ∅, γ, hartogsNumberName P R (checkName ∅ γ)] ↔
      δ = (kpair.π₂ (woodinIterationRec θ)) ‘ θ := by
  dsimp only
  obtain ⟨hR, ht, hτ, hz, hleast⟩ := woodinSparse_fixed_inverseCutoff_context hΩ hAC hθ h0 hlim hn
  have he := eval_fixedSuccessfulNamedPrefixSelectorFormula (δ := δ) hR ht hτ hz ⟨_, hleast.2.1⟩
  change _ ↔ δ = woodinSparseInverseCutoff θ (woodinSparsePrefixCode θ) at he
  let := hΩ.inaccessible.1
  rw [woodinSparsePrefix_inverse_cutoff hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ) h0 hlim hn] at he
  exact he

end ZFVP
