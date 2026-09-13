import ZFVP.ModelTheory.SchmerlInternalInfinitaryEquations

/-! Internal induction and binder-depth recursion for infinitary fragments. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsFragment.immediate_mem {L F s t : V} (hF : IsFragment L F) (ht : t ∈ F)
    (hst : IsImmediate s t) : s ∈ F := by
  have he := (hF.2 t ht).1
  have hn := (hF.2 t ht).2
  generalize hnt : kpair.π₁ t = n at he hn
  generalize hφt : kpair.π₂ t = φ at he hn
  subst t
  rcases hn.2 with ⟨ψ, _, rfl⟩ | ⟨ψ, rfl, hψ⟩ | ⟨f, hf, hd, rfl, hmem⟩ |
    ⟨ψ, rfl, hψ⟩ | ⟨ψ, rfl, hψ⟩
  · exact False.elim (immediate_fo_iff _ _ _ hst)
  · exact ((immediate_neg_iff _ _ _).mp hst) ▸ hψ
  · obtain ⟨_, i, hi, rfl⟩ := (immediate_conj_iff _ _ _).mp hst
    exact hmem i (hd ▸ hi)
  · exact ((immediate_exs_iff _ _ _).mp hst) ▸ hψ
  · exact ((immediate_q_iff _ _ _).mp hst) ▸ hψ

set_option maxHeartbeats 800000 in
theorem fragment_induction {L F : V} (hF : IsFragment L F) (P : V → V → Prop)
    (hP : ℒₛₑₜ-relation[V] P)
    (hfo : ∀ n φ, ⟨n, foCode φ⟩ₖ ∈ F → φ ∈ formulaSet L ∅ n → P n (foCode φ))
    (hneg : ∀ n φ, ⟨n, negCode φ⟩ₖ ∈ F → ⟨n, φ⟩ₖ ∈ F → P n φ → P n (negCode φ))
    (hconj : ∀ n f, ⟨n, conjCode f⟩ₖ ∈ F → IsFunction f → domain f = (ω : V) →
      (∀ i ∈ (ω : V), ⟨n, f ‘ i⟩ₖ ∈ F) → (∀ i ∈ (ω : V), P n (f ‘ i)) → P n (conjCode f))
    (hexs : ∀ n φ, ⟨n, exsCode φ⟩ₖ ∈ F → ⟨succ n, φ⟩ₖ ∈ F → P (succ n) φ → P n (exsCode φ))
    (hq : ∀ n φ, ⟨n, qCode φ⟩ₖ ∈ F → ⟨succ n, φ⟩ₖ ∈ F → P (succ n) φ → P n (qCode φ)) :
    ∀ n φ, ⟨n, φ⟩ₖ ∈ F → P n φ := by
  have hall : ∀ t ∈ F, P (kpair.π₁ t) (kpair.π₂ t) := by
    apply internalWellFounded_induction (immediateRelation_wellFounded F)
      (fun t ↦ P (kpair.π₁ t) (kpair.π₂ t)) (by definability)
    intro t ht ih
    have he := (hF.2 t ht).1
    have hn := (hF.2 t ht).2
    generalize hnt : kpair.π₁ t = n at he hn
    generalize hφt : kpair.π₂ t = φ at he hn
    subst t
    have hi {s : V} (hs : s ∈ F) (hst : IsImmediate s ⟨n, φ⟩ₖ) : P (kpair.π₁ s) (kpair.π₂ s) :=
      ih s hs ((pair_mem_immediateRelation F s ⟨n, φ⟩ₖ).mpr ⟨hs, ht, hst⟩)
    rcases hn.2 with ⟨ψ, hψ, rfl⟩ | ⟨ψ, rfl, hψ⟩ | ⟨f, hf, hd, rfl, hmem⟩ |
      ⟨ψ, rfl, hψ⟩ | ⟨ψ, rfl, hψ⟩
    · exact hfo n ψ ht hψ
    · exact hneg n ψ ht hψ (by simpa using hi hψ ((immediate_neg_iff _ _ _).mpr rfl))
    · apply hconj n f ht hf hd hmem
      intro i hiω
      simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
        hi (hmem i hiω) ((immediate_conj_iff _ _ _).mpr ⟨hf, i, hd.symm ▸ hiω, rfl⟩)
    · exact hexs n ψ ht hψ (by simpa using hi hψ ((immediate_exs_iff _ _ _).mpr rfl))
    · exact hq n ψ ht hψ (by simpa using hi hψ ((immediate_q_iff _ _ _).mpr rfl))
  intro n φ hφ
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hall ⟨n, φ⟩ₖ hφ

noncomputable def depthDomain (F : V) : V := F ×ˢ (ω : V)

noncomputable def depthRelation (D : V) : V :=
  {p ∈ D ×ˢ D ; IsImmediate (kpair.π₁ (kpair.π₁ p)) (kpair.π₁ (kpair.π₂ p))}

instance depthDomain_definable : ℒₛₑₜ-function₁[V] depthDomain := by unfold depthDomain; definability

instance depthRelation_definable : ℒₛₑₜ-function₁[V] depthRelation := by
  have h : ℒₛₑₜ-relation[V] (fun R D ↦ ∀ p, p ∈ R ↔ p ∈ D ×ˢ D ∧
      IsImmediate (kpair.π₁ (kpair.π₁ p)) (kpair.π₁ (kpair.π₂ p))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = depthRelation (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [depthRelation, mem_sep_iff]

@[simp] theorem pair_mem_depthDomain (F p k : V) :
    ⟨p, k⟩ₖ ∈ depthDomain F ↔ p ∈ F ∧ k ∈ (ω : V) := by
  simp only [depthDomain, kpair_mem_iff]

theorem pair_mem_depthRelation (D x y : V) :
    ⟨x, y⟩ₖ ∈ depthRelation D ↔ x ∈ D ∧ y ∈ D ∧ IsImmediate (kpair.π₁ x) (kpair.π₁ y) := by
  simp only [depthRelation, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem depthRelation_wellFounded (D : V) : IsInternallyWellFounded (depthRelation D) D := by
  apply projectedRank_internallyWellFounded _ _ (fun x ↦ kpair.π₂ (kpair.π₁ x)) (by definability)
  intro x _ y _ hxy
  exact immediate_rank ((pair_mem_depthRelation D x y).mp hxy).2.2

noncomputable def depthRecursion (F : V) (f : V → V → V) (hf : ℒₛₑₜ-function₂[V] f) : V :=
  wellFoundedRecursion (depthRelation_wellFounded (depthDomain F)) f hf

instance depthRecursion_isFunction (F : V) (f : V → V → V) (hf : ℒₛₑₜ-function₂[V] f) :
    IsFunction (depthRecursion F f hf) := wellFoundedRecursion_isFunction _ _ _

@[simp] theorem domain_depthRecursion (F : V) (f : V → V → V) (hf : ℒₛₑₜ-function₂[V] f) :
    domain (depthRecursion F f hf) = depthDomain F := domain_wellFoundedRecursion _ _ _

theorem depthRecursion_value (F : V) (f : V → V → V) (hf : ℒₛₑₜ-function₂[V] f)
    {q : V} (hq : q ∈ depthDomain F) :
    (depthRecursion F f hf) ‘ q = f q ((depthRecursion F f hf) ↾
      (predecessors (depthRelation (depthDomain F)) (depthDomain F) q)) :=
  wellFoundedRecursion_value _ _ _ hq

theorem depthRecursion_previous {L F p q i j : V} (hF : IsFragment L F)
    (f : V → V → V) (hf : ℒₛₑₜ-function₂[V] f) (hq : q ∈ F)
    (hi : i ∈ (ω : V)) (hj : j ∈ (ω : V)) (hpq : IsImmediate p q) :
    ((depthRecursion F f hf) ↾ (predecessors (depthRelation (depthDomain F)) (depthDomain F)
      ⟨q, j⟩ₖ)) ‘ ⟨p, i⟩ₖ = (depthRecursion F f hf) ‘ ⟨p, i⟩ₖ := by
  have hp := hF.immediate_mem hq hpq
  have hpi := (pair_mem_depthDomain F p i).mpr ⟨hp, hi⟩
  have hqj := (pair_mem_depthDomain F q j).mpr ⟨hq, hj⟩
  apply value_restrict (by simpa using hpi)
  apply (mem_predecessors_iff _ _ _ _).mpr
  refine ⟨hpi, (pair_mem_depthRelation _ _ _).mpr ⟨hpi, hqj, ?_⟩⟩
  simpa only [kpair.π₁_kpair] using hpq

end ZFVP.Infinitary.Internal
