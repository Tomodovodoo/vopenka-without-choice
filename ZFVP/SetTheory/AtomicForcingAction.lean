import ZFVP.SetTheory.AtomicMembership
import ZFVP.SetTheory.SymmetryAction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicEquality_nameAction_forward {P R π σ τ p : V}
    (hπ : IsForcingAutomorphism P R π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ atomicEquality P R σ τ) :
    π ‘ p ∈ atomicEquality P R (nameAction π σ) (nameAction π τ) := by
  have h := forcingName_induction P
    (fun σ ↦ ∀ τ, IsForcingName P τ → ∀ p, p ∈ atomicEquality P R σ τ →
      π ‘ p ∈ atomicEquality P R (nameAction π σ) (nameAction π τ)) (by definability) ?_ σ hσ
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
    obtain ⟨q, hq, hqq'⟩ := forcingAutomorphism_surjective hπ q' hq'
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
    obtain ⟨q, hq, hqq'⟩ := forcingAutomorphism_surjective hπ q' hq'
    subst q'
    obtain ⟨r, hrP, hrq, υ, s, hs, hrs, hE⟩ := hr ν t ht q hq
      ((hπ.2.2.2 q hq p hpP).mpr hq'p)
      ((hπ.2.2.2 q hq t (forcingName_condition hτ ht)).mpr hq't)
    exact ⟨π ‘ r, function_value_mem hπ.1 hrP, (hπ.2.2.2 r hrP q hq).mp hrq,
      nameAction π υ, π ‘ s, (mem_nameAction_iff hσ π _).mpr ⟨υ, s, hs, rfl⟩,
      (hπ.2.2.2 r hrP s (forcingName_condition hσ hs)).mp hrs,
      ih υ s hs ν (forcingName_subname hτ ht) r hE⟩

theorem atomicEquality_nameAction_iff {P R π σ τ p : V}
    (hπ : IsForcingAutomorphism P R π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ P) :
    π ‘ p ∈ atomicEquality P R (nameAction π σ) (nameAction π τ) ↔ p ∈ atomicEquality P R σ τ := by
  constructor
  · intro hE
    have he := atomicEquality_nameAction_forward (forcingAutomorphism_inverse hπ)
      (nameAction_isName hπ.1 hσ) (nameAction_isName hπ.1 hτ) hE
    simpa only [nameAction_inverse_cancel hπ hσ, nameAction_inverse_cancel hπ hτ,
      converseGraph_value_value hπ.1 hπ.2.1 hp] using he
  · exact atomicEquality_nameAction_forward hπ hσ hτ

theorem atomicMembership_nameAction_forward {P R π σ τ p : V}
    (hπ : IsForcingAutomorphism P R π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ atomicMembership P R σ τ) :
    π ‘ p ∈ atomicMembership P R (nameAction π σ) (nameAction π τ) := by
  obtain ⟨hpP, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hp
  apply (mem_atomicMembership_iff _ _ _ _ _).mpr
  refine ⟨function_value_mem hπ.1 hpP, ?_⟩
  intro q' hq' hq'p
  obtain ⟨q, hq, hqq'⟩ := forcingAutomorphism_surjective hπ q' hq'
  subst q'
  obtain ⟨r, hr, hrq, ν, s, hνs, hrs, hE⟩ := hh q hq ((hπ.2.2.2 q hq p hpP).mpr hq'p)
  exact ⟨π ‘ r, function_value_mem hπ.1 hr, (hπ.2.2.2 r hr q hq).mp hrq,
    nameAction π ν, π ‘ s, (mem_nameAction_iff hτ π _).mpr ⟨ν, s, hνs, rfl⟩,
    (hπ.2.2.2 r hr s (forcingName_condition hτ hνs)).mp hrs,
    atomicEquality_nameAction_forward hπ hσ (forcingName_subname hτ hνs) hE⟩

theorem atomicMembership_nameAction_iff {P R π σ τ p : V}
    (hπ : IsForcingAutomorphism P R π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ P) :
    π ‘ p ∈ atomicMembership P R (nameAction π σ) (nameAction π τ) ↔ p ∈ atomicMembership P R σ τ := by
  constructor
  · intro hM
    have hm := atomicMembership_nameAction_forward (forcingAutomorphism_inverse hπ)
      (nameAction_isName hπ.1 hσ) (nameAction_isName hπ.1 hτ) hM
    simpa only [nameAction_inverse_cancel hπ hσ, nameAction_inverse_cancel hπ hτ,
      converseGraph_value_value hπ.1 hπ.2.1 hp] using hm
  · exact atomicMembership_nameAction_forward hπ hσ hτ

end ZFVP
