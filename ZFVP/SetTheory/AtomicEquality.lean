import ZFVP.SetTheory.AtomicEqualityRecursion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicEqualityAt_coherent (P R C D : V) (hC : IsSubnameClosed C) (hD : IsSubnameClosed D)
    (σ τ : V) (hτC : τ ∈ C) (hτD : τ ∈ D) :
    atomicEqualityAt P R C σ τ = atomicEqualityAt P R D σ τ := by
  have h := projectedRank_induction (nameClosure σ) (fun x : V ↦ x) (by definability)
    (fun υ ↦ ∀ ν ∈ C, ν ∈ D → atomicEqualityAt P R C υ ν = atomicEqualityAt P R D υ ν)
    (by definability) ?_
  · exact h σ (mem_nameClosure_self σ) τ hτC hτD
  intro υ hυ ih ν hνC hνD
  apply SetTheory.mem_ext_iff.mpr
  intro p
  rw [mem_atomicEqualityAt_iff _ _ _ _ _ hνC, mem_atomicEqualityAt_iff _ _ _ _ _ hνD]
  apply and_congr_right
  intro _
  apply atomicEqualityTest_congr
  intro υ' s hs ν' t ht
  exact ih υ' (nameClosure_closed σ υ hυ υ' (mem_domain_of_kpair_mem hs)) (rank_subname_lt hs)
    ν' (hC ν hνC ν' (mem_domain_of_kpair_mem ht)) (hD ν hνD ν' (mem_domain_of_kpair_mem ht))

noncomputable def atomicEquality (P R σ τ : V) : V :=
  atomicEqualityAt P R (nameClosure τ) σ τ

instance atomicEquality_definable (P R : V) : ℒₛₑₜ-function₂[V] (atomicEquality P R) := by
  unfold atomicEquality
  definability

theorem atomicEqualityAt_eq (P R C : V) (hC : IsSubnameClosed C) (σ : V) {τ : V} (hτ : τ ∈ C) :
    atomicEqualityAt P R C σ τ = atomicEquality P R σ τ :=
  atomicEqualityAt_coherent P R C (nameClosure τ) hC (nameClosure_closed τ)
    σ τ hτ (mem_nameClosure_self τ)

theorem mem_atomicEquality_iff (P R σ τ p : V) :
    p ∈ atomicEquality P R σ τ ↔ p ∈ P ∧ AtomicEqualityTest P R (atomicEquality P R) σ τ p := by
  rw [atomicEquality, mem_atomicEqualityAt_iff _ _ _ _ _ (mem_nameClosure_self τ)]
  apply and_congr_right
  intro _
  apply atomicEqualityTest_congr
  intro υ s _ ν t ht
  exact atomicEqualityAt_eq P R (nameClosure τ) (nameClosure_closed τ) υ (subname_mem_nameClosure ht)

theorem atomicEquality_subset (P R σ τ : V) : atomicEquality P R σ τ ⊆ P := by
  intro p hp
  exact ((mem_atomicEquality_iff _ _ _ _ _).mp hp).1

theorem atomicEquality_mono {P R σ τ p q : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ atomicEquality P R σ τ) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) :
    q ∈ atomicEquality P R σ τ := by
  obtain ⟨hpP, hl, hr⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp hp
  apply (mem_atomicEquality_iff _ _ _ _ _).mpr
  refine ⟨hq, ?_, ?_⟩
  · intro υ s hs r hrP hrq hrs
    exact hl υ s hs r hrP (hR.2.2 r hrP q hq p hpP hrq hqp) hrs
  · intro ν t ht r hrP hrq hrt
    exact hr ν t ht r hrP (hR.2.2 r hrP q hq p hpP hrq hqp) hrt

theorem atomicEqualityTest_swap (P R σ τ p : V) (E : V → V → V) :
    AtomicEqualityTest P R E σ τ p ↔ AtomicEqualityTest P R (fun υ ν ↦ E ν υ) τ σ p :=
  ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

theorem atomicEquality_symm (P R σ τ : V) : atomicEquality P R σ τ = atomicEquality P R τ σ := by
  have h := projectedRank_induction (nameClosure σ) (fun x : V ↦ x) (by definability)
    (fun υ ↦ ∀ ν, atomicEquality P R υ ν = atomicEquality P R ν υ) (by definability) ?_
  · exact h σ (mem_nameClosure_self σ) τ
  intro υ hυ ih ν
  apply SetTheory.mem_ext_iff.mpr
  intro p
  rw [mem_atomicEquality_iff, mem_atomicEquality_iff]
  apply and_congr_right
  intro _
  rw [atomicEqualityTest_swap]
  apply atomicEqualityTest_congr
  intro ν' t _ υ' s hs
  exact ih υ' (nameClosure_closed σ υ hυ υ' (mem_domain_of_kpair_mem hs)) (rank_subname_lt hs) ν'

theorem atomicEquality_refl {P R : V} (hR : IsForcingPreorder P R) (σ : V) :
    atomicEquality P R σ σ = P := by
  have h := projectedRank_induction (nameClosure σ) (fun x : V ↦ x) (by definability)
    (fun υ ↦ ∀ p ∈ P, p ∈ atomicEquality P R υ υ) (by definability) ?_
  · apply SetTheory.subset_antisymm (atomicEquality_subset _ _ _ _)
    exact h σ (mem_nameClosure_self σ)
  intro υ hυ ih p hp
  apply (mem_atomicEquality_iff _ _ _ _ _).mpr
  have hc : ∀ ν t, ⟨ν, t⟩ₖ ∈ υ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, t⟩ₖ ∈ R →
      ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ∃ ν' t', ⟨ν', t'⟩ₖ ∈ υ ∧ ⟨r, t'⟩ₖ ∈ R ∧
        r ∈ atomicEquality P R ν ν' := by
    intro ν t ht q hq _ hqt
    exact ⟨q, hq, hR.2.1 q hq, ν, t, ht, hqt,
      ih ν (nameClosure_closed σ υ hυ ν (mem_domain_of_kpair_mem ht)) (rank_subname_lt ht) q hq⟩
  refine ⟨hp, hc, ?_⟩
  intro ν t ht q hq hqp hqt
  obtain ⟨r, hr, hrq, ν', t', ht', hrt', he⟩ := hc ν t ht q hq hqp hqt
  exact ⟨r, hr, hrq, ν', t', ht', hrt', atomicEquality_symm P R ν ν' ▸ he⟩

theorem forcingOrder_left_mem {P R p q : V} (hR : IsForcingPreorder P R)
    (hpq : ⟨p, q⟩ₖ ∈ R) : p ∈ P := by
  have h : p ∈ P ∧ q ∈ P := by simpa using hR.1 _ hpq
  exact h.1

theorem forcingOrder_right_mem {P R p q : V} (hR : IsForcingPreorder P R)
    (hpq : ⟨p, q⟩ₖ ∈ R) : q ∈ P := by
  have h : p ∈ P ∧ q ∈ P := by simpa using hR.1 _ hpq
  exact h.2

theorem atomicEquality_dense {P R σ τ p : V} (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hd : ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ atomicEquality P R σ τ, ⟨r, q⟩ₖ ∈ R) :
    p ∈ atomicEquality P R σ τ := by
  apply (mem_atomicEquality_iff _ _ _ _ _).mpr
  refine ⟨hp, ?_, ?_⟩
  · intro υ s hs q hq hqp hqs
    obtain ⟨r, hr, hrq⟩ := hd q hq hqp
    obtain ⟨hrP, hl, _⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp hr
    obtain ⟨v, hv, hvr, ν, t, ht, hvt, he⟩ := hl υ s hs r hrP (hR.2.1 r hrP)
      (hR.2.2 r hrP q hq s (forcingOrder_right_mem hR hqs) hrq hqs)
    exact ⟨v, hv, hR.2.2 v hv r hrP q hq hvr hrq, ν, t, ht, hvt, he⟩
  · intro ν t ht q hq hqp hqt
    obtain ⟨r, hr, hrq⟩ := hd q hq hqp
    obtain ⟨hrP, _, hh⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp hr
    obtain ⟨v, hv, hvr, υ, s, hs, hvs, he⟩ := hh ν t ht r hrP (hR.2.1 r hrP)
      (hR.2.2 r hrP q hq t (forcingOrder_right_mem hR hqt) hrq hqt)
    exact ⟨v, hv, hR.2.2 v hv r hrP q hq hvr hrq, υ, s, hs, hvs, he⟩

end ZFVP
