import ZFVP.ModelTheory.SchmerlInternalInfinitarySubstitution
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.NaturalClosureCardinality

/-! The image of an internal fragment under simultaneous substitution is an
actual valid fragment. Its quantifiers use the successor substitution state. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def substitutionDepths (F G : V) : V :=
  {q ∈ depthDomain F ; kpair.π₁ (kpair.π₁ q) = stateSource (G ‘ (kpair.π₂ q))}

instance substitutionDepths_definable : ℒₛₑₜ-function₂[V] substitutionDepths := by
  have h : ℒₛₑₜ-relation₃[V] (fun S F G ↦ ∀ q, q ∈ S ↔ q ∈ depthDomain F ∧
      kpair.π₁ (kpair.π₁ q) = stateSource (G ‘ (kpair.π₂ q))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = substitutionDepths (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [substitutionDepths, mem_sep_iff]

@[simp] theorem pair_mem_substitutionDepths (F G n φ k : V) :
    ⟨⟨n, φ⟩ₖ, k⟩ₖ ∈ substitutionDepths F G ↔
      ⟨n, φ⟩ₖ ∈ F ∧ k ∈ (ω : V) ∧ n = stateSource (G ‘ k) := by
  simp only [substitutionDepths, mem_sep_iff, pair_mem_depthDomain,
    kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

noncomputable def substitutedNode (L F G q : V) : V :=
  ⟨stateTarget (G ‘ (kpair.π₂ q)), (infinitarySubstitutionGraph L F G) ‘ q⟩ₖ

instance substitutedNode_definable : ℒₛₑₜ-function₄[V] substitutedNode := by
  unfold substitutedNode
  definability

noncomputable def substitutedFragment (L F G : V) : V :=
  repl (substitutedNode L F G) (by definability) (substitutionDepths F G)

instance substitutedFragment_definable : ℒₛₑₜ-function₃[V] substitutedFragment := by
  have h : ℒₛₑₜ-relation₄[V] (fun S L F G ↦ ∀ p, p ∈ S ↔
      ∃ q ∈ substitutionDepths F G, p = substitutedNode L F G q) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = substitutedFragment (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [substitutedFragment, repl_spec]

theorem substitutedNode_mem {L F G n φ k : V} (hφ : ⟨n, φ⟩ₖ ∈ F)
    (hk : k ∈ (ω : V)) (hc : n = stateSource (G ‘ k)) :
    ⟨stateTarget (G ‘ k), (infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ⟩ₖ ∈
      substitutedFragment L F G := by
  apply (repl_spec _).mpr
  exact ⟨⟨⟨n, φ⟩ₖ, k⟩ₖ, (pair_mem_substitutionDepths _ _ _ _ _).mpr ⟨hφ, hk, hc⟩,
    by simp only [substitutedNode, kpair.π₂_kpair]⟩

theorem substitutedFragment_countable {L F G : V} (hF : IsInternallyCountable F) :
    IsInternallyCountable (substitutedFragment L F G) :=
  internallyCountable_repl _ _ ((cardLE_of_subset (fun x h ↦ sep_subset x h)).trans
    ((prod_cardLE_prod hF internallyCountable_omega).trans omega_prod_cardLE_omega))

theorem substitutedFragment_valid {L F G : V} (hF : IsFragment L F)
    (hG : ∀ k ∈ (ω : V), IsSubstitutionState L ∅ ∅ (G ‘ k))
    (hsource : ∀ k ∈ (ω : V), stateSource (G ‘ (succ k)) = succ (stateSource (G ‘ k)))
    (htarget : ∀ k ∈ (ω : V), stateTarget (G ‘ (succ k)) = succ (stateTarget (G ‘ k))) :
    IsFragment L (substitutedFragment L F G) := by
  refine ⟨hF.1, ?_⟩
  intro p hp
  obtain ⟨q, hq, rfl⟩ := (repl_spec _).mp hp
  obtain ⟨hp, hc⟩ := mem_sep_iff.mp hq
  obtain ⟨t, ht, k, hk, rfl⟩ := mem_prod_iff.mp hp
  have he := (hF.2 t ht).1
  have hn := (hF.2 t ht).2
  generalize hnt : kpair.π₁ t = n at he hn hc
  generalize hφt : kpair.π₂ t = φ at he hn
  subst t
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hc
  simp only [substitutedNode, kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨trivial, (hG k hk).2.1, ?_⟩
  have hchild {m ψ j : V} (hψ : ⟨m, ψ⟩ₖ ∈ F) (hj : j ∈ (ω : V))
      (hm : m = stateSource (G ‘ j)) := substitutedNode_mem (L := L) hψ hj hm
  have hs : succ n = stateSource (G ‘ (succ k)) := by rw [hsource k hk, hc]
  rcases hn.2 with ⟨ψ, hψ, rfl⟩ | ⟨ψ, rfl, hψ⟩ | ⟨f, hf, hd, rfl, hmem⟩ |
    ⟨ψ, rfl, hψ⟩ | ⟨ψ, rfl, hψ⟩
  · rw [infinitarySubstitutionGraph_fo ht hk]
    exact Or.inl ⟨_, formulaSubstitutionGraph_valid hF.1 hG hsource htarget n ψ hψ k hk hc, rfl⟩
  · rw [infinitarySubstitutionGraph_neg hF ht hk]
    exact Or.inr (Or.inl ⟨_, rfl, hchild hψ hk hc⟩)
  · rw [infinitarySubstitutionGraph_conj hF ht hk]
    refine Or.inr (Or.inr (Or.inl ⟨_, inferInstance, domain_transformConjunction _ _ _, rfl, ?_⟩))
    intro i hi
    rw [value_transformConjunction _ _ _ hi]
    simpa only [substitutionChild, kpair.π₁_kpair, kpair.π₂_kpair] using hchild (hmem i hi) hk hc
  · rw [infinitarySubstitutionGraph_exs hF ht hk]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, by
      simpa only [htarget k hk] using hchild hψ (ω_succ_closed hk) hs⟩)))
  · rw [infinitarySubstitutionGraph_q hF ht hk]
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl, by
      simpa only [htarget k hk] using hchild hψ (ω_succ_closed hk) hs⟩)))

end ZFVP.Infinitary.Internal
