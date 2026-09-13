import ZFVP.SetTheory.FinitePermutationExtension
import ZFVP.SetTheory.CohenLeastSupport
import ZFVP.SetTheory.AtomicForcingAction
import ZFVP.SetTheory.AtomicEqualityTransitivity

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A permutation agreeing with `π` on `E` and fixing `F` sends a condition supported in
`E ∪ F` into the union of that condition and its `π` image. -/
theorem cohenConditionAction_subset_union_of_agree {I E F p π ζ : V}
    (hp : p ∈ cohenConditions I) (hζ : IsInternalPermutation I ζ)
    (hsupp : cohenSupport p ⊆ E ∪ F)
    (hagree : ∀ i ∈ E, ζ ‘ i = π ‘ i) (hfix : ∀ i ∈ F, ζ ‘ i = i) :
    cohenConditionAction I ζ p ⊆ p ∪ cohenConditionAction I π p := by
  have hact := cohenConditionAction_condition hζ hp
  have : IsFunction (cohenConditionAction I ζ p) :=
    ((mem_finitePartialFunctions _ _ _).mp hact).2.1
  intro z hz
  obtain ⟨u, b, rfl⟩ := IsFunction.mem_eq_kpair hz
  obtain ⟨i, hi, n, hn, rfl⟩ := mem_prod_iff.mp
    (finitePartialFunction_domain hact _ (mem_domain_of_kpair_mem hz))
  obtain ⟨j, hj, hij⟩ := (cohenConditionAction_pair_iff hp).mp hz
  have hjs := hsupp j ((mem_cohenSupport p j).mpr ⟨n, b, hj⟩)
  rcases mem_union_iff.mp hjs with hjE | hjF
  · apply mem_union_iff.mpr ∘ Or.inr
    apply (cohenConditionAction_pair_iff hp).mpr
    exact ⟨j, hj, hij.trans (hagree j hjE)⟩
  · apply mem_union_iff.mpr ∘ Or.inl
    have he : i = j := hij.trans (hfix j hjF)
    simpa only [he] using hj

/-- Under the finite-support amalgamation hypotheses, any common extension of `p` and
`π p` forces the first name equal to its `π` image. -/
theorem cohen_atomicEquality_amalgamation {E F τ σ p π r : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ)
    (hσ : IsForcingName (cohenConditions (ω : V)) σ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport σ F)
    (hp : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ)
    (hsupp : cohenSupport p ⊆ E ∪ F)
    (hπ : IsInternalPermutation (ω : V) π)
    (hfix : ∀ i ∈ E ∩ F, π ‘ i = i)
    (havoid : ∀ i ∈ E, i ∉ F → π ‘ i ∉ F)
    (hr : r ∈ cohenConditions (ω : V))
    (hrp : ⟨r, p⟩ₖ ∈ cohenOrder (ω : V))
    (hrπp : ⟨r, cohenConditionAction (ω : V) π p⟩ₖ ∈ cohenOrder (ω : V)) :
    r ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ
      (nameAction (cohenPermutation (ω : V) π) τ) := by
  have hpP := atomicEquality_subset _ _ _ _ p hp
  obtain ⟨ζ, hζ, hζfix, hagree⟩ := finite_permutation_extend_fixing hF.1 hE.1 hE.2.1 hπ
    (fun i hiE hiF ↦ hfix i (mem_inter_iff.mpr ⟨hiE, hiF⟩)) havoid
  have hζτ := cohenNameAction_eq_of_agree_on_support hτ hE.1 hE.2.2 hζ hπ hagree
  have hζσ := hF.2.2 ζ hζ hζfix
  have hsub := cohenConditionAction_subset_union_of_agree hpP hζ hsupp hagree hζfix
  have hζpr : cohenConditionAction (ω : V) ζ p ⊆ r := by
    intro z hz
    exact (mem_union_iff.mp (hsub z hz)).elim
      (((pair_mem_cohenOrder _ _ _).mp hrp).2.2 z)
      (((pair_mem_cohenOrder _ _ _).mp hrπp).2.2 z)
  have hrζp : ⟨r, cohenConditionAction (ω : V) ζ p⟩ₖ ∈ cohenOrder (ω : V) :=
    (pair_mem_cohenOrder _ _ _).mpr ⟨hr, cohenConditionAction_condition hζ hpP, hζpr⟩
  have hζeq := atomicEquality_nameAction_forward (cohenPermutation_automorphism hζ) hτ hσ hp
  rw [cohenPermutation_value hpP, hζτ, hζσ] at hζeq
  have hR := (cohen_poset (ω : V)).1
  have hrζeq := atomicEquality_mono hR hζeq hr hrζp
  have hre := atomicEquality_mono hR hp hr hrp
  apply atomicEquality_trans hR τ σ _ r hre
  rw [atomicEquality_symm (cohenConditions (ω : V)) (cohenOrder (ω : V)) σ (nameAction (cohenPermutation (ω : V) π) τ)]
  exact hrζeq

end ZFVP

