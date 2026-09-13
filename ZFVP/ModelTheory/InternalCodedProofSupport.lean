import ZFVP.ModelTheory.UniformCodedSequentProofs
import ZFVP.SetTheory.FiniteSets

/-! Every internally finite proof uses an internally finite part of its theory.
The original proof graph is retained; no external enumeration of its lines is used. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsOpenCodedSequentRule.theory_mono {T U P n Γ : V}
    (h : IsOpenCodedSequentRule T P n Γ) (hTU : T ⊆ U) :
    IsOpenCodedSequentRule U P n Γ := by
  rcases h with h | ⟨φ, hφ, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨φ, hTU _ hφ, he⟩

theorem IsOpenCodedSequentProof.theory_mono {T U p n Γ : V}
    (hp : IsOpenCodedSequentProof T p n Γ) (hTU : T ⊆ U) :
    IsOpenCodedSequentProof U p n Γ := by
  obtain ⟨hf, l, hl, hd, he, hs⟩ := hp
  refine ⟨hf, l, hl, hd, he, fun i hi ↦ ?_⟩
  obtain ⟨m, Δ, hv, hc, hr⟩ := hs i hi
  exact ⟨m, Δ, hv, hc, hr.theory_mono hTU⟩

theorem OpenCodedSequentConsistent.subtheory {T U : V}
    (hU : OpenCodedSequentConsistent U) (hTU : T ⊆ U) : OpenCodedSequentConsistent T := by
  rintro ⟨p, hp⟩
  exact hU ⟨p, hp.theory_mono hTU⟩

theorem IsOpenCodedSequentProof.internallyFinite {T p n Γ : V}
    (hp : IsOpenCodedSequentProof T p n Γ) : IsInternallyFinite p := by
  obtain ⟨hf, l, hl, hd, _⟩ := hp
  let := hf
  apply internallyFinite_function
  rw [hd]
  exact internallyFinite_of_cardLE_natural (ω_succ_closed hl) (CardLE.refl _)

/-- Applying this map to a singleton sequent recovers its open axiom code.
Other sequents may contribute extra formulas, removed by intersection with T. -/
noncomputable def openCodedProofSupport (T p : V) : V :=
  T ∩ repl (fun q ↦ ⟨kpair.π₁ q, ⋃ˢ (kpair.π₂ q)⟩ₖ) (by definability) (range p)

instance openCodedProofSupport_definable : ℒₛₑₜ-function₂[V] openCodedProofSupport := by
  unfold openCodedProofSupport
  definability

theorem openCodedProofSupport_subset (T p : V) : openCodedProofSupport T p ⊆ T := by
  intro a ha
  exact (mem_inter_iff.mp ha).1

theorem IsOpenCodedSequentProof.support_finite {T p n Γ : V}
    (hp : IsOpenCodedSequentProof T p n Γ) : IsInternallyFinite (openCodedProofSupport T p) :=
  internallyFinite_subset
    (internallyFinite_repl _ _ (internallyFinite_range hp.internallyFinite))
    (fun _ ha ↦ (mem_inter_iff.mp ha).2)

theorem IsOpenCodedSequentProof.over_support {T p n Γ : V}
    (hp : IsOpenCodedSequentProof T p n Γ) :
    IsOpenCodedSequentProof (openCodedProofSupport T p) p n Γ := by
  obtain ⟨hf, l, hl, hd, he, hs⟩ := hp
  let := hf
  refine ⟨hf, l, hl, hd, he, fun i hi ↦ ?_⟩
  obtain ⟨m, Δ, hv, hc, hr⟩ := hs i hi
  refine ⟨m, Δ, hv, hc, ?_⟩
  rcases hr with hr | ⟨φ, hφ, rfl⟩
  · exact Or.inl hr
  · refine Or.inr ⟨φ, mem_inter_iff.mpr ⟨hφ, ?_⟩, rfl⟩
    apply (repl_spec _).mpr
    refine ⟨⟨m, ({φ} : V)⟩ₖ, ?_, by simp⟩
    rw [← hv]
    exact mem_range_of_kpair_mem (kpair_value_mem hi)

theorem IsOpenCodedSequentProof.finite_subtheory {T p n Γ : V}
    (hp : IsOpenCodedSequentProof T p n Γ) :
    ∃ A, A ⊆ T ∧ IsInternallyFinite A ∧ IsOpenCodedSequentProof A p n Γ :=
  ⟨openCodedProofSupport T p, openCodedProofSupport_subset T p, hp.support_finite, hp.over_support⟩

theorem openCodedSequentConsistent_iff_finite (T : V) : OpenCodedSequentConsistent T ↔
    ∀ A, A ⊆ T → IsInternallyFinite A → OpenCodedSequentConsistent A := by
  constructor
  · intro hT A hA _
    exact hT.subtheory hA
  · intro hall
    rintro ⟨p, hp⟩
    obtain ⟨A, hAT, hfin, hpA⟩ := hp.finite_subtheory
    exact hall A hAT hfin ⟨p, hpA⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The shared proof-checker formula transfers the whole internal proof
predicate, including lengths that are externally nonstandard. -/
theorem map_openCodedSequentProof_iff (j : ElementaryMap V W) (T p n Γ : V) :
    IsOpenCodedSequentProof (j T) (j p) (j n) (j Γ) ↔ IsOpenCodedSequentProof T p n Γ :=
  (j.map_defined isOpenCodedSequentProofFormula
    (fun v ↦ IsOpenCodedSequentProof (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ IsOpenCodedSequentProof (v 0) (v 1) (v 2) (v 3)) ![T, p, n, Γ]).symm

/-- This is an equivalence of internal consistency assertions. It does not
identify internal consistency with external consistency in a nonstandard model. -/
theorem map_openCodedSequentConsistent_iff (j : ElementaryMap V W) (T : V) :
    OpenCodedSequentConsistent (j T) ↔ OpenCodedSequentConsistent T :=
  (j.map_defined openCodedSequentConsistentFormula
    (fun v ↦ OpenCodedSequentConsistent (v 0))
    (fun v ↦ OpenCodedSequentConsistent (v 0)) ![T]).symm

end ElementaryMap

end ZFVP
