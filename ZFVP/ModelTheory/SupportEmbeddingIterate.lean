import ZFVP.ModelTheory.SupportStageEmbeddingAction
import ZFVP.ModelTheory.CriticalPointRestriction

/-! Finite iterates of a coded embedding between rank stages.

For an embedding `f` from `hierarchy θ` to `hierarchy θ'` the `n`-th iterate `f ∘ ... ∘ f` makes
sense on a smaller stage `hierarchy β` as long as the forward orbit of `β` stays inside the
source. This file builds that iterate as an internal function and proves it is elementary.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The iterate as a function of its starting point -/

/-- The recursion step of `naturalIteration`, written without `if`. -/
theorem naturalIterationStep_eq_iff (F : V → V) (a g y : V) :
    y = naturalIterationStep F a g ↔
      (domain g = 0 ∧ y = a) ∨ (domain g ≠ 0 ∧ y = F (g ‘ (⋃ˢ domain g))) := by
  unfold naturalIterationStep
  split <;> simp_all

/-- Any attempt function of length `n` computes the value of the recursion at `n`. -/
theorem transfiniteRec_eq_of_isAttempt {F : V → V} (hF : ℒₛₑₜ-function₁ F) {n g : V}
    (hn : IsOrdinal n) (hg : IsAttempt F n g) :
    Replacement.transfiniteRec F hF n = F g := by
  classical
  have h0 : IsAttempt F n (Replacement.replAttemptOrEmpty F hF (IsOrdinal.toOrdinal n)) :=
    Replacement.replAttemptOrEmpty_aux F hF (IsOrdinal.toOrdinal n)
  have : IsFunction g := hg.2.1
  have : IsFunction (Replacement.replAttemptOrEmpty F hF (IsOrdinal.toOrdinal n)) := h0.2.1
  have he : Replacement.replAttemptOrEmpty F hF n = g := by
    simpa only [IsOrdinal.toOrdinal_val] using
      IsAttempt.isAttempt_unique (α := IsOrdinal.toOrdinal n) h0 hg
  simp [Replacement.transfiniteRec, hn, he]

/-- First order description of `z = criticalIterate f x n`: either `n` is not an ordinal and `z`
is empty, or some attempt function of length `n` for the iteration started at `x` has `z` as its
next value. Written without `if` and without a Lean level recursion, so it is visibly definable in
all four arguments at once. -/
def IterateSpec (f x n z : V) : Prop :=
  (IsOrdinal n ∧ ∃ g, (IsFunction g ∧ domain g = n ∧
      ∀ b ∈ n, ∀ y, (⟨b, y⟩ₖ ∈ g ↔
        ((domain (g ↾ b) = 0 ∧ y = x) ∨
          (domain (g ↾ b) ≠ 0 ∧ y = f ‘ ((g ↾ b) ‘ (⋃ˢ domain (g ↾ b))))))) ∧
      ((domain g = 0 ∧ z = x) ∨ (domain g ≠ 0 ∧ z = f ‘ (g ‘ (⋃ˢ domain g))))) ∨
    (¬IsOrdinal n ∧ z = ∅)

theorem iterateSpec_iff (f x n z : V) : IterateSpec f x n z ↔ z = criticalIterate f x n := by
  have hF : ℒₛₑₜ-function₁ (fun y : V ↦ f ‘ y) := by definability
  have hS : ℒₛₑₜ-function₁ (naturalIterationStep (fun y : V ↦ f ‘ y) x) :=
    naturalIterationStep_definable _ hF x
  have hcrit : criticalIterate f x n =
      Replacement.transfiniteRec (naturalIterationStep (fun y : V ↦ f ‘ y) x) hS n := rfl
  have hatt : ∀ g : V, IsAttempt (naturalIterationStep (fun y : V ↦ f ‘ y) x) n g ↔
      (IsOrdinal n ∧ IsFunction g ∧ domain g = n ∧
        ∀ b ∈ n, ∀ y, (⟨b, y⟩ₖ ∈ g ↔
          ((domain (g ↾ b) = 0 ∧ y = x) ∨
            (domain (g ↾ b) ≠ 0 ∧ y = f ‘ ((g ↾ b) ‘ (⋃ˢ domain (g ↾ b))))))) := by
    intro g
    unfold IsAttempt
    simp only [naturalIterationStep_eq_iff]
  by_cases hn : IsOrdinal n
  · simp only [IterateSpec, hn, true_and, not_true_eq_false, false_and, or_false]
    constructor
    · rintro ⟨g, hg, hz⟩
      have hga : IsAttempt (naturalIterationStep (fun y : V ↦ f ‘ y) x) n g :=
        (hatt g).mpr ⟨hn, hg⟩
      rw [hcrit, transfiniteRec_eq_of_isAttempt hS hn hga]
      exact (naturalIterationStep_eq_iff (fun y : V ↦ f ‘ y) x g z).mpr hz
    · intro hz
      obtain ⟨g, hg⟩ := Replacement.attempt_function_exists
        (naturalIterationStep (fun y : V ↦ f ‘ y) x) hS (IsOrdinal.toOrdinal n)
      refine ⟨g, ((hatt g).mp hg).2, ?_⟩
      apply (naturalIterationStep_eq_iff (fun y : V ↦ f ‘ y) x g z).mp
      rw [hz, hcrit, transfiniteRec_eq_of_isAttempt hS hn hg]
  · simp only [IterateSpec, hn, false_and, not_false_eq_true, true_and, false_or]
    rw [hcrit, Replacement.transfiniteRec_spec_of_not_isOrdinal _ hS hn]

instance criticalIterate_start_definable (f n : V) :
    ℒₛₑₜ-function₁[V] (fun x ↦ criticalIterate f x n) := by
  have h : ℒₛₑₜ-relation (fun z x : V ↦ IterateSpec f x n z) := by
    unfold IterateSpec; definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = criticalIterate f (v 1) n ↔ _
  exact (iterateSpec_iff f (v 1) n (v 0)).symm

/-! ### The iterate as an internal function on a stage -/

/-- The `n`-th iterate of `f`, as an internal function on the stage `hierarchy β`. -/
noncomputable def supportEmbeddingIterate (f β n : V) : V :=
  definableGraph (hierarchy β) (fun x ↦ criticalIterate f x n) (criticalIterate_start_definable f n)

theorem value_supportEmbeddingIterate {f β n x : V} (hx : x ∈ hierarchy β) :
    (supportEmbeddingIterate f β n) ‘ x = criticalIterate f x n :=
  value_definableGraph _ _ _ hx

instance supportEmbeddingIterate_isFunction (f β n : V) :
    IsFunction (supportEmbeddingIterate f β n) := definableGraph_isFunction _ _ _

@[simp] theorem domain_supportEmbeddingIterate (f β n : V) :
    domain (supportEmbeddingIterate f β n) = hierarchy β := domain_definableGraph _ _ _

@[simp] theorem supportEmbeddingIterate_zero (f β : V) :
    supportEmbeddingIterate f β 0 = SetTheory.identity (hierarchy β) := by
  apply mem_ext
  intro p
  rw [supportEmbeddingIterate, mem_definableGraph_iff, mem_identity_iff]
  simp only [criticalIterate_zero]

theorem supportEmbeddingIterate_zero_value {f β x : V} (hx : x ∈ hierarchy β) :
    (supportEmbeddingIterate f β 0) ‘ x = x := by
  rw [supportEmbeddingIterate_zero, identity_value hx]

instance supportEmbeddingIterate_definable (f β : V) :
    ℒₛₑₜ-function₁[V] (supportEmbeddingIterate f β) := by
  have h : ℒₛₑₜ-relation (fun z n : V ↦
      ∀ p, (p ∈ z ↔ ∃ x ∈ hierarchy β, ∃ w, IterateSpec f x n w ∧ p = ⟨x, w⟩ₖ)) := by
    unfold IterateSpec; definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = supportEmbeddingIterate f β (v 1) ↔ _
  rw [mem_ext_iff]
  constructor
  · intro hz p
    rw [hz, supportEmbeddingIterate, mem_definableGraph_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, criticalIterate f x (v 1), (iterateSpec_iff _ _ _ _).mpr rfl, rfl⟩
    · rintro ⟨x, hx, w, hw, rfl⟩
      exact ⟨x, hx, by rw [(iterateSpec_iff f x (v 1) w).mp hw]⟩
  · intro hz p
    rw [hz p, supportEmbeddingIterate, mem_definableGraph_iff]
    constructor
    · rintro ⟨x, hx, w, hw, rfl⟩
      exact ⟨x, hx, by rw [(iterateSpec_iff f x (v 1) w).mp hw]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, criticalIterate f x (v 1), (iterateSpec_iff _ _ _ _).mpr rfl, rfl⟩

/-- Two internal functions with the same domain and the same values are equal, even when they are
presented with different codomains. -/
theorem function_eq_of_pointwise {X Y Z f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Z ^ X)
    (hv : ∀ x ∈ X, f ‘ x = g ‘ x) : f = g := by
  have hf' : IsFunction f := IsFunction.of_mem hf
  have hg' : IsFunction g := IsFunction.of_mem hg
  have hdf : domain f = X := domain_eq_of_mem_function hf
  have hdg : domain g = X := domain_eq_of_mem_function hg
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, y, _, rfl⟩ : ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ := by
      simpa [mem_prod_iff] using subset_prod_of_mem_function hf _ hp
    have hxy : g ‘ x = y := by rw [← hv x hx]; exact value_eq_of_kpair_mem hp
    have hmem := kpair_value_mem (f := g) (x := x) (by rw [hdg]; exact hx)
    rwa [hxy] at hmem
  · intro hp
    obtain ⟨x, hx, y, _, rfl⟩ : ∃ x ∈ X, ∃ y ∈ Z, p = ⟨x, y⟩ₖ := by
      simpa [mem_prod_iff] using subset_prod_of_mem_function hg _ hp
    have hxy : f ‘ x = y := by rw [hv x hx]; exact value_eq_of_kpair_mem hp
    have hmem := kpair_value_mem (f := f) (x := x) (by rw [hdf]; exact hx)
    rwa [hxy] at hmem

/-! ### Elementarity of the iterate -/

section Iterate

variable {θ θ' γ f β : V} [IsOrdinal θ] [IsOrdinal θ'] [IsOrdinal γ]
  (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
  (hω' : (ω : V) ∈ θ') (hsucc' : ∀ ξ ∈ θ', succ ξ ∈ θ')
  (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
  (hωγ : (ω : V) ∈ γ) (hsuccγ : ∀ ξ ∈ γ, succ ξ ∈ γ) (hγθ : γ ∈ θ)
  (hFγ : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy γ)
  (hβne : IsNonempty β)
  (horbit : ∀ n ∈ (ω : V), criticalIterate f β n ∈ γ)

include h hγθ horbit

omit [IsOrdinal γ] in
/-- Every point of the forward orbit of `β` is an ordinal above `β`. -/
theorem supportEmbeddingIterate_orbit_ordinal (hβ : IsOrdinal β) {n : V} (hn : n ∈ (ω : V)) :
    IsOrdinal (criticalIterate f β n) ∧ β ⊆ criticalIterate f β n := by
  let := hβ
  let := (inferInstance : IsOrdinal θ)
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  apply naturalNumber_induction
    (fun n ↦ IsOrdinal (criticalIterate f β n) ∧ β ⊆ criticalIterate f β n)
    (by definability) ?_ ?_ n hn
  · simp only [criticalIterate_zero]
    exact ⟨hβ, subset_refl β⟩
  · rintro m hm ⟨h1, h2⟩
    have hmem : criticalIterate f β m ∈ hierarchy θ :=
      ordinal_subset_hierarchy θ _ (IsOrdinal.toIsTransitive.mem_trans (horbit m hm) hγθ)
    rw [criticalIterate_succ f β hm]
    exact ⟨h.value_ordinal h1 hmem,
      fun x hx ↦ h.ordinal_subset_value h1 hmem x (h2 x hx)⟩

include hω hsucc hω' hsucc' hωγ hsuccγ hFγ hβne

/-- The `n`-th iterate is an elementary embedding from `hierarchy β` to the stage at the `n`-th
point of the forward orbit of `β`. -/
theorem supportEmbeddingIterate_embedding (hβ : IsOrdinal β) {n : V} (hn : n ∈ (ω : V)) :
    IsCodedMembershipEmbedding (hierarchy β) (hierarchy (criticalIterate f β n))
      (supportEmbeddingIterate f β n) := by
  let := hβ
  let := (inferInstance : IsOrdinal θ)
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  apply naturalNumber_induction
    (fun n ↦ IsCodedMembershipEmbedding (hierarchy β) (hierarchy (criticalIterate f β n))
      (supportEmbeddingIterate f β n)) (by definability) ?_ ?_ n hn
  · have hne : IsNonempty (hierarchy β) :=
      ⟨∅, ordinal_subset_hierarchy β _ (IsOrdinal.empty_mem_iff_nonempty.mpr hβne)⟩
    simpa using IsCodedMembershipEmbedding.identity hne
  · intro m hm ih
    obtain ⟨hord, hsub⟩ := supportEmbeddingIterate_orbit_ordinal h hγθ horbit hβ hm
    let := hord
    have hmγ : criticalIterate f β m ∈ γ := horbit m hm
    have hmθ : criticalIterate f β m ∈ θ := IsOrdinal.toIsTransitive.mem_trans hmγ hγθ
    have hmem : criticalIterate f β m ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hmθ
    have hmne : IsNonempty (criticalIterate f β m) :=
      ⟨∅, hsub _ (IsOrdinal.empty_mem_iff_nonempty.mpr hβne)⟩
    have hres : IsCodedMembershipEmbedding (hierarchy (criticalIterate f β m))
        (hierarchy (f ‘ (criticalIterate f β m))) (f ↾ (hierarchy (criticalIterate f β m))) :=
      supportEmbedding_restrict_hierarchy hω hsucc hω' hsucc' h hωγ hsuccγ hγθ hFγ hord hmne hmγ
    have hcomp := ih.comp hres
    have hstage : hierarchy (criticalIterate f β m) ∈ hierarchy θ :=
      hierarchy_mem_hierarchy_of_support hsucc hmem
    have heq : supportEmbeddingIterate f β (succ m) =
        compose (supportEmbeddingIterate f β m) (f ↾ (hierarchy (criticalIterate f β m))) := by
      let := IsFunction.of_mem h.function
      apply function_eq_of_pointwise (definableGraph_mem_function _ _ _) hcomp.function
      intro x hx
      have hvx : (supportEmbeddingIterate f β m) ‘ x = criticalIterate f x m :=
        value_supportEmbeddingIterate hx
      have hxm : criticalIterate f x m ∈ hierarchy (criticalIterate f β m) := by
        rw [← hvx]; exact function_value_mem ih.function hx
      have hxθ : criticalIterate f x m ∈ hierarchy θ :=
        IsTransitive.transitive _ hstage _ hxm
      rw [value_compose_of_mem_function ih.function hres.function hx, hvx,
        value_restrict (by rw [domain_eq_of_mem_function h.function]; exact hxθ) hxm,
        ← criticalIterate_succ f x hm]
      exact value_definableGraph _ _ _ hx
    rw [heq, criticalIterate_succ f β hm]
    exact hcomp

end Iterate

/-! ### Critical point of the iterate -/

section CriticalPoint

variable {θ θ' γ f β κ : V} [IsOrdinal θ] [IsOrdinal θ'] [IsOrdinal γ]

omit [IsOrdinal θ] in
/-- Points below the critical point are fixed by every iterate. -/
theorem criticalIterate_fixed_below {α : V} [IsTransitive (hierarchy θ)]
    (hκ : IsCriticalPoint (hierarchy θ) f κ) (hα : α ∈ κ) {n : V} (hn : n ∈ (ω : V)) :
    criticalIterate f α n = α := by
  apply naturalNumber_induction (fun n ↦ criticalIterate f α n = α) (by definability) ?_ ?_ n hn
  · simp
  · intro m hm ih
    rw [criticalIterate_succ f α hm, ih, hκ.fixed_below hα]

omit [IsOrdinal γ] in
/-- The forward orbit of the critical point stays inside the source stage, sits below the forward
orbit of `β`, and moves strictly upward. -/
theorem criticalIterate_criticalPoint_orbit
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hγθ : γ ∈ θ) (horbit : ∀ n ∈ (ω : V), criticalIterate f β n ∈ γ)
    (hκ : IsCriticalPoint (hierarchy θ) f κ) (hκβ : κ ∈ β)
    {n : V} (hn : n ∈ (ω : V)) :
    IsOrdinal (criticalIterate f κ n) ∧ criticalIterate f κ n ∈ criticalIterate f β n ∧
      κ ⊆ criticalIterate f κ n ∧ criticalIterate f κ n ∈ f ‘ (criticalIterate f κ n) := by
  let := (inferInstance : IsOrdinal θ)
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  have hstage : ∀ m ∈ (ω : V), criticalIterate f β m ∈ hierarchy θ := fun m hm ↦
    ordinal_subset_hierarchy θ _ (IsOrdinal.toIsTransitive.mem_trans (horbit m hm) hγθ)
  apply naturalNumber_induction
    (fun n ↦ IsOrdinal (criticalIterate f κ n) ∧ criticalIterate f κ n ∈ criticalIterate f β n ∧
      κ ⊆ criticalIterate f κ n ∧ criticalIterate f κ n ∈ f ‘ (criticalIterate f κ n))
    (by definability) ?_ ?_ n hn
  · simp only [criticalIterate_zero]
    exact ⟨hκ.ordinal, hκβ, subset_refl κ, hκ.lt_value h⟩
  · rintro m hm ⟨h1, h2, h3, h4⟩
    have hxθ : criticalIterate f κ m ∈ hierarchy θ :=
      IsTransitive.transitive _ (hstage m hm) _ h2
    have hfxθ : f ‘ (criticalIterate f κ m) ∈ hierarchy θ := by
      have hmem : f ‘ (criticalIterate f κ m) ∈ f ‘ (criticalIterate f β m) :=
        (h.value_mem_iff hxθ (hstage m hm)).mpr h2
      have : f ‘ (criticalIterate f β m) ∈ hierarchy θ := by
        rw [← criticalIterate_succ f β hm]
        exact hstage _ (ω_succ_closed hm)
      exact IsTransitive.transitive _ this _ hmem
    rw [criticalIterate_succ f κ hm, criticalIterate_succ f β hm]
    exact ⟨h.value_ordinal h1 hxθ, (h.value_mem_iff hxθ (hstage m hm)).mpr h2,
      fun x hx ↦ h.ordinal_subset_value h1 hxθ x (h3 x hx),
      (h.value_mem_iff hxθ hfxθ).mpr h4⟩

omit [IsOrdinal γ] in
/-- Every nonzero iterate has the same critical point as `f`. -/
theorem supportEmbeddingIterate_criticalPoint
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hγθ : γ ∈ θ) (horbit : ∀ n ∈ (ω : V), criticalIterate f β n ∈ γ)
    (hκ : IsCriticalPoint (hierarchy θ) f κ) (hβ : IsOrdinal β) (hκV : κ ∈ hierarchy β)
    {n : V} (hn : n ∈ (ω : V)) :
    IsCriticalPoint (hierarchy β) (supportEmbeddingIterate f β (succ n)) κ := by
  let := (inferInstance : IsOrdinal θ)
  let := hβ
  let := hκ.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  let := hierarchy_transitive β
  have hκβ : κ ∈ β := ordinal_mem_hierarchy_iff.mp hκV
  obtain ⟨h1, _, h3, h4⟩ :=
    criticalIterate_criticalPoint_orbit h hγθ horbit hκ hκβ hn
  let := h1
  have hlt : κ ∈ criticalIterate f κ (succ n) := by
    rw [criticalIterate_succ f κ hn]
    let := h.value_ordinal h1 (by
      have := criticalIterate_criticalPoint_orbit h hγθ horbit hκ hκβ hn
      exact IsTransitive.transitive _ (ordinal_subset_hierarchy θ _
        (IsOrdinal.toIsTransitive.mem_trans (horbit n hn) hγθ)) _ this.2.1)
    rcases IsOrdinal.subset_iff.mp h3 with he | hl
    · exact he ▸ h4
    · exact IsOrdinal.toIsTransitive.mem_trans hl h4
  apply IsCriticalPoint.of_fixed_below hκ.ordinal hκV
  · rw [value_supportEmbeddingIterate hκV]
    intro he
    rw [he] at hlt
    exact mem_irrefl κ hlt
  · intro α hα
    have hαV : α ∈ hierarchy β := IsTransitive.transitive _ hκV _ hα
    rw [value_supportEmbeddingIterate hαV,
      criticalIterate_fixed_below hκ hα (ω_succ_closed hn)]

/-- The value of the iterate at the critical point is the iterate of the critical point. -/
theorem supportEmbeddingIterate_value_criticalPoint {n : V} (hκ : κ ∈ hierarchy β) :
    (supportEmbeddingIterate f β n) ‘ κ = criticalIterate f κ n :=
  value_supportEmbeddingIterate hκ

end CriticalPoint

end ZFVP
