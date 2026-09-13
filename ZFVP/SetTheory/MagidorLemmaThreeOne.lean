import ZFVP.SetTheory.MagidorSupercompactBounded
import ZFVP.ModelTheory.SupportEmbeddingIterate
import ZFVP.SetTheory.NaturalPredecessor

/-! # Magidor's Lemma 3.1, in embedding form

Magidor's lemma, quoted as Lemma 3.1 in Bagaria, *C(n)-cardinals*, section 3: if `j : V_lam →
V_mu` is elementary, `lam` is a limit ordinal and `κ` is the critical point of `j`, then `κ` is
`<lam`-supercompact. Bagaria states the conclusion with normal fine measures on `P_κ(γ)`, which
this project does not have, so the conclusion here is the small-embedding form
`IsMagidorSupercompactUpTo κ lam`: for every `γ ∈ lam` above `κ` there is a stage `V_lb` with
`lb ∈ κ` and an elementary `e : V_lb → V_γ` whose critical point goes to `κ`.

The two halves of Bagaria's proof are separated below.

The first half is Kunen's theorem, and it is unconditional: `exists_criticalIterate_mem` says the
critical sequence `κ, f ‘ κ, f ‘ (f ‘ κ), ...` passes above every `γ ∈ lam`. If it did not, all
of its stages would be ordinals below `γ`, so the critical limit would be an ordinal in `lam`, and
`false_of_criticalLimit_mem` (Kunen's theorem applied to the restriction of `f` to the stage of the
critical limit, which `f` fixes) refutes that.

The second half is the reflection, and it is where the argument needs the `m`-th iterate of `f` as
an embedding defined on a stage that contains `γ`. Bagaria writes `j_{m+1} = j ∘ j_m` without
comment. That composite is not available in general here: `f` goes from `V_{lam+omega}` to
`V_{lam'+omega}`, and `f ‘ x` need not lie back in the source stage, so `f ‘ (f ‘ x)` need not be
defined. Two cases where the composite is available are proved:

* `magidorSupercompactUpTo_of_subset_value`: `lam ⊆ f ‘ κ`, that is `f ‘ κ` is already above every
  `γ ∈ lam`. This is the case Bagaria's Definition 3.2 of `lam`-extendibility builds in, and one
  step of `f` suffices; no iterate is needed.
* `magidorSupercompactUpTo_of_closed`: `lam` is closed under `f`, so the whole forward orbit of any
  ordinal of `lam` stays in `lam` and the finite iterates of `f` are available on stages below
  `lam`. This is the rank-into-rank shape of the hypothesis.

`magidorSupercompactUpTo_of_criticalPoint` is the disjunction of the two. What is not proved is the
remaining case, where `lam` is not closed under `f` but `f ‘ κ` is still below some `γ ∈ lam`: then
the first half gives an `m` with `γ ∈ f^m ‘ κ`, but the intermediate values `f ‘ γ, ..., f^{m-1} ‘ γ`
may leave `V_{lam+omega}`, so `f^m` is not available on `V_γ` and the reflection has no witness to
carry. Closing that case needs a construction of the composite that this project does not have.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A limit ordinal is closed under successors. -/
theorem succ_mem_of_limitOrdinal {lam ζ : V} (hlim : IsLimitOrdinal lam) (hζ : ζ ∈ lam) :
    succ ζ ∈ lam := by
  have : IsOrdinal lam := hlim.1
  have : IsOrdinal ζ := IsOrdinal.of_mem hζ
  rcases IsOrdinal.mem_trichotomy (succ ζ) lam with hm | he | hm
  · exact hm
  · exact absurd ⟨ζ, he.symm⟩ hlim.2.2
  · rcases mem_succ_iff.mp hm with he' | hm'
    · exact absurd hζ (he' ▸ mem_irrefl lam)
    · exact absurd (IsOrdinal.toIsTransitive.mem_trans hm' hζ) (mem_irrefl lam)

/-- Successor closure of a set crosses a coded embedding. -/
theorem value_successor_closed {A B f x : V} [IsTransitive A] [IsTransitive B]
    (h : IsCodedMembershipEmbedding A B f) (hxA : x ∈ A) (hx : ∀ ξ ∈ x, succ ξ ∈ x) :
    ∀ ξ ∈ f ‘ x, succ ξ ∈ f ‘ x := by
  have h0 := (eval_boundedSuccessorClosedFormula x).mpr hx
  have he := (h.bounded_formula_iff boundedSuccessorClosedFormula_bounded ![x]
    (by simp [hxA])).mp h0
  have hvec : (fun i ↦ f ‘ ((![x] : Fin 1 → V) i)) = ![f ‘ x] := by
    funext i
    exact Fin.cases rfl (fun t ↦ Fin.elim0 t) i
  rw [hvec] at he
  exact (eval_boundedSuccessorClosedFormula (f ‘ x)).mp he

/-- If `lam` is closed under `f`, the forward orbit of a successor-closed ordinal of `lam` above
`ω` consists of successor-closed ordinals of `lam` above `ω`, each one inside the next. -/
theorem criticalIterate_closed_orbit {θ θ' lam f x : V} [IsOrdinal θ] [IsOrdinal θ']
    [IsOrdinal lam] (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hlamθ : lam ∈ θ) (hclosed : ∀ δ ∈ lam, f ‘ δ ∈ lam)
    (hx : x ∈ lam) (hωx : (ω : V) ∈ x) (hsuccx : ∀ ξ ∈ x, succ ξ ∈ x) (hxf : x ∈ f ‘ x)
    {i : V} (hi : i ∈ (ω : V)) :
    criticalIterate f x i ∈ lam ∧ (ω : V) ∈ criticalIterate f x i ∧
      (∀ ξ ∈ criticalIterate f x i, succ ξ ∈ criticalIterate f x i) ∧
      criticalIterate f x i ∈ criticalIterate f x (succ i) := by
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  have hstage : ∀ y : V, y ∈ lam → y ∈ hierarchy θ := by
    intro y hy
    let := IsOrdinal.of_mem hy
    exact ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans hy hlamθ)
  have hωθ : (ω : V) ∈ θ := IsOrdinal.toIsTransitive.mem_trans
    (IsOrdinal.toIsTransitive.mem_trans hωx hx) hlamθ
  have hωH : (ω : V) ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hωθ
  apply naturalNumber_induction
    (fun i ↦ criticalIterate f x i ∈ lam ∧ (ω : V) ∈ criticalIterate f x i ∧
      (∀ ξ ∈ criticalIterate f x i, succ ξ ∈ criticalIterate f x i) ∧
      criticalIterate f x i ∈ criticalIterate f x (succ i)) (by definability) ?_ ?_ i hi
  · rw [criticalIterate_zero, criticalIterate_succ f x (by simp : (0 : V) ∈ (ω : V)),
      criticalIterate_zero]
    exact ⟨hx, hωx, hsuccx, hxf⟩
  · rintro k hk ⟨h1, h2, h3, h4⟩
    have hyH : criticalIterate f x k ∈ hierarchy θ := hstage _ h1
    have hfy : f ‘ (criticalIterate f x k) ∈ lam := hclosed _ h1
    have hfyH : f ‘ (criticalIterate f x k) ∈ hierarchy θ := hstage _ hfy
    refine ⟨by rwa [criticalIterate_succ f x hk], ?_, ?_, ?_⟩
    · rw [criticalIterate_succ f x hk]
      have hm := (h.value_mem_iff hωH hyH).mpr h2
      rwa [h.value_omega hωH] at hm
    · rw [criticalIterate_succ f x hk]
      exact value_successor_closed h hyH h3
    · rw [criticalIterate_succ f x hk, criticalIterate_succ f x (ω_succ_closed hk),
        criticalIterate_succ f x hk]
      have h4' : criticalIterate f x k ∈ f ‘ (criticalIterate f x k) := by
        rwa [criticalIterate_succ f x hk] at h4
      exact (h.value_mem_iff hyH hfyH).mpr h4'

/-- If `lam` is closed under `f`, so is the whole forward orbit of any of its members. -/
theorem criticalIterate_mem_of_closed {lam f x : V}
    (hclosed : ∀ δ ∈ lam, f ‘ δ ∈ lam) (hx : x ∈ lam) {i : V} (hi : i ∈ (ω : V)) :
    criticalIterate f x i ∈ lam := by
  apply naturalNumber_induction (fun i ↦ criticalIterate f x i ∈ lam) (by definability) ?_ ?_ i hi
  · simpa only [criticalIterate_zero] using hx
  · intro k hk ih
    rw [criticalIterate_succ f x hk]
    exact hclosed _ ih

section Magidor

variable {lam lam' f κ : V} [IsOrdinal lam] [IsOrdinal lam']
  (hlim : IsLimitOrdinal lam) (hωlam : (ω : V) ∈ lam)
  (hlim' : IsLimitOrdinal lam') (hωlam' : (ω : V) ∈ lam')
  (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
  (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
    (hierarchy (ordinalAdd lam' (ω : V))) f)
  (hκ : IsCriticalPoint (hierarchy (ordinalAdd lam (ω : V))) f κ)

include hlim hωlam hlim' hωlam' hF h hκ

/-! ### Kunen's theorem: the critical sequence passes above every ordinal of `lam` -/

/-- The critical sequence of `f` is not bounded by any `γ ∈ lam` above the critical point. If it
were, every stage of it would be an ordinal below `γ`, the critical limit would be an ordinal of
`lam`, and Kunen's theorem in the form `false_of_criticalLimit_mem` would refute that. -/
theorem exists_criticalIterate_mem (hAC : InternalChoice V) {γ : V}
    (hκγ : κ ∈ γ) (hγ : γ ∈ lam) : ∃ n ∈ (ω : V), γ ∈ criticalIterate f κ n := by
  by_contra hcontra
  have hcon : ∀ n ∈ (ω : V), γ ∉ criticalIterate f κ n := by
    intro n hn hmem
    exact hcontra ⟨n, hn, hmem⟩
  have hsucclam : ∀ ξ ∈ lam, succ ξ ∈ lam := fun _ hξ ↦ succ_mem_of_limitOrdinal hlim hξ
  have hsucclam' : ∀ ξ ∈ lam', succ ξ ∈ lam' := fun _ hξ ↦ succ_mem_of_limitOrdinal hlim' hξ
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  let := hκ.ordinal
  have hγord : IsOrdinal γ := IsOrdinal.of_mem hγ
  let := hγord
  have hγθ : γ ∈ ordinalAdd lam (ω : V) := IsOrdinal.toIsTransitive.mem_trans hγ hlamθ
  have key : ∀ n ∈ (ω : V),
      IsOrdinal (criticalIterate f κ n) ∧ criticalIterate f κ n ⊆ γ := by
    intro n hn
    apply naturalNumber_induction
      (fun n ↦ IsOrdinal (criticalIterate f κ n) ∧ criticalIterate f κ n ⊆ γ)
      (by definability) ?_ ?_ n hn
    · simpa only [criticalIterate_zero] using
        And.intro hκ.ordinal (IsOrdinal.toIsTransitive.transitive κ hκγ)
    · rintro m hm ⟨ho, hs⟩
      let := ho
      have hmem : criticalIterate f κ m ∈ hierarchy (ordinalAdd lam (ω : V)) := by
        rcases IsOrdinal.subset_iff.mp hs with he | hl
        · exact ordinal_mem_hierarchy_iff.mpr (he ▸ hγθ)
        · exact ordinal_mem_hierarchy_iff.mpr
            (IsOrdinal.toIsTransitive.mem_trans hl hγθ)
      have hne := hcon (succ m) (ω_succ_closed hm)
      rw [criticalIterate_succ f κ hm] at hne ⊢
      let := h.value_ordinal ho hmem
      refine ⟨h.value_ordinal ho hmem, ?_⟩
      rcases IsOrdinal.mem_trichotomy (f ‘ (criticalIterate f κ m)) γ with hl | he | hg
      · exact IsOrdinal.toIsTransitive.transitive _ hl
      · exact he ▸ subset_refl _
      · exact absurd hg hne
  have hlimord : IsOrdinal (criticalLimit f κ) := by
    apply IsOrdinal.sUnion
    intro y hy
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hn : n ∈ (ω : V) := by simpa using mem_domain_of_kpair_mem hny
    have he : y = criticalIterate f κ n :=
      (value_eq_of_kpair_mem hny).symm.trans (criticalSequence_value f κ hn)
    exact he.symm ▸ (key n hn).1
  let := hlimord
  have hsub : criticalLimit f κ ⊆ γ := by
    intro x hx
    obtain ⟨n, hn, hxn⟩ := (mem_criticalLimit_iff f κ x).mp hx
    exact (key n hn).2 x hxn
  have hmem : criticalLimit f κ ∈ lam := by
    rcases IsOrdinal.subset_iff.mp hsub with he | hl
    · exact he ▸ hγ
    · exact IsOrdinal.toIsTransitive.mem_trans hl hγ
  exact false_of_criticalLimit_mem hAC hωlam hsucclam hωlam' hsucclam' hF h hκ hmem

/-! ### The one step case -/

/-- If `f ‘ κ` is already above `γ`, the restriction `f ↾ V_γ` is a small embedding into
`V_{f ‘ γ}` for the pair `(f ‘ κ, f ‘ γ)`: its source `γ` lies below `f ‘ κ`, its critical point is
`κ ∈ γ` and it sends `κ` to `f ‘ κ`. Transferring back along `f` gives Magidor's predicate for the
pair `(κ, γ)`. -/
theorem magidorSupercompactAt_of_mem_value {γ : V}
    (hκγ : κ ∈ γ) (hγ : γ ∈ lam) (hγv : γ ∈ f ‘ κ) : IsMagidorSupercompactAt κ γ := by
  have hsucclam : ∀ ξ ∈ lam, succ ξ ∈ lam := fun _ hξ ↦ succ_mem_of_limitOrdinal hlim hξ
  have hsucclam' : ∀ ξ ∈ lam', succ ξ ∈ lam' := fun _ hξ ↦ succ_mem_of_limitOrdinal hlim' hξ
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  let := hκ.ordinal
  have hω : (ω : V) ∈ ordinalAdd lam (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam hlamθ
  have hsucc : ∀ ξ ∈ ordinalAdd lam (ω : V), succ ξ ∈ ordinalAdd lam (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam hξ
  have hω' : (ω : V) ∈ ordinalAdd lam' (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam' (ordinalAdd_omega_gt lam')
  have hsucc' : ∀ ξ ∈ ordinalAdd lam' (ω : V), succ ξ ∈ ordinalAdd lam' (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam' hξ
  have hFlam : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy lam :=
    hierarchy_mono (ordinalAdd_omega_subset_of_successor_closed hωlam hsucclam) _ hF
  have hγord : IsOrdinal γ := IsOrdinal.of_mem hγ
  let := hγord
  have hγθ : γ ∈ ordinalAdd lam (ω : V) := IsOrdinal.toIsTransitive.mem_trans hγ hlamθ
  have hres : IsCodedMembershipEmbedding (hierarchy γ) (hierarchy (f ‘ γ)) (f ↾ (hierarchy γ)) :=
    supportEmbedding_restrict_hierarchy hω hsucc hω' hsucc' h hωlam hsucclam hlamθ hFlam
      hγord ⟨κ, hκγ⟩ hγ
  let := hierarchy_transitive γ
  have hκH : κ ∈ hierarchy γ := ordinal_mem_hierarchy_iff.mpr hκγ
  have hκθ : κ ∈ hierarchy (ordinalAdd lam (ω : V)) := hκ.mem_domain
  have hcrit : IsCriticalPoint (hierarchy γ) (f ↾ (hierarchy γ)) κ :=
    hκ.restrict h.function
      (IsTransitive.transitive _ (hierarchy_mem hγθ)) hκH
  have hval : (f ↾ (hierarchy γ)) ‘ κ = f ‘ κ := by
    let := IsFunction.of_mem h.function
    exact value_restrict (by rw [domain_eq_of_mem_function h.function]; exact hκθ) hκH
  have hwit : IsMagidorSupercompactAt (f ‘ κ) (f ‘ γ) :=
    ⟨γ, hγv, κ, hκγ, f ↾ (hierarchy γ), hres, hcrit, hval⟩
  exact (magidorSupercompactAt_value_iff hωlam hsucclam hωlam' hsucclam' hF h hκγ hγ).mpr hwit

/-- If `f ‘ κ` is above all of `lam`, every `γ ∈ lam` above `κ` is handled by one step of `f`.
This is the shape of Bagaria's Definition 3.2, where `lam`-extendibility asks for `j(κ) > lam`. -/
theorem magidorSupercompactUpTo_of_subset_value (hsub : lam ⊆ f ‘ κ) :
    IsMagidorSupercompactUpTo κ lam := fun γ hγ _ hκγ ↦
  magidorSupercompactAt_of_mem_value hlim hωlam hlim' hωlam' hF h hκ hκγ hγ (hsub γ hγ)

/-! ### The case where `lam` is closed under `f` -/

/-- If `lam` is closed under `f`, every finite iterate of `f` is defined on every stage below
`lam`, and Bagaria's reflection goes through. Take `n` with `γ ∈ f^n ‘ κ`, which exists by
`exists_criticalIterate_mem`. The `n`-th iterate on `V_γ` is a small embedding for the pair
`(f^n ‘ κ, f^n ‘ γ)`: its source `γ` lies below `f^n ‘ κ`, its critical point is `κ ∈ γ`, and it
sends `κ` to `f^n ‘ κ`. The `n`-th iterate on the stage `V_β` for `β := f^{n+1} ‘ κ` carries that
back down to the pair `(κ, γ)`. -/
theorem magidorSupercompactUpTo_of_closed (hAC : InternalChoice V)
    (hclosed : ∀ δ ∈ lam, f ‘ δ ∈ lam) : IsMagidorSupercompactUpTo κ lam := by
  intro γ hγ hγord hκγ
  let := hγord
  have hsucclam : ∀ ξ ∈ lam, succ ξ ∈ lam := fun _ hξ ↦ succ_mem_of_limitOrdinal hlim hξ
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  let := hκ.ordinal
  have hω : (ω : V) ∈ ordinalAdd lam (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam hlamθ
  have hsucc : ∀ ξ ∈ ordinalAdd lam (ω : V), succ ξ ∈ ordinalAdd lam (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam hξ
  have hω' : (ω : V) ∈ ordinalAdd lam' (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam' (ordinalAdd_omega_gt lam')
  have hsucc' : ∀ ξ ∈ ordinalAdd lam' (ω : V), succ ξ ∈ ordinalAdd lam' (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam' hξ
  have hFlam : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy lam :=
    hierarchy_mono (ordinalAdd_omega_subset_of_successor_closed hωlam hsucclam) _ hF
  let := (hierarchy_isSequenceSupport hω hsucc).toIsCodingSupport
  -- the critical point is a successor-closed ordinal of `lam` above `ω` that `f` moves up
  have hκlam : κ ∈ lam := IsOrdinal.toIsTransitive.mem_trans hκγ hγ
  have hωκ : (ω : V) ∈ κ := hκ.omega_lt h
  have hsuccκ : ∀ ξ ∈ κ, succ ξ ∈ κ := fun _ hξ ↦ hκ.succ_closed h hξ
  have hκf : κ ∈ f ‘ κ := hκ.lt_value h
  -- the first stage of the critical sequence above `γ`
  obtain ⟨n, hn, hγn⟩ := exists_criticalIterate_mem hlim hωlam hlim' hωlam' hF h hκ hAC hκγ hγ
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [criticalIterate_zero] at hγn
    exact mem_irrefl γ (IsOrdinal.toIsTransitive.mem_trans hγn hκγ)
  obtain ⟨m, hm, rfl⟩ := (internalNatural_cases hn).resolve_left hn0
  -- the auxiliary stage `ν` and the big stage `β`
  obtain ⟨hνlam, hων, hsuccν, hνβ⟩ :=
    criticalIterate_closed_orbit h hlamθ hclosed hκlam hωκ hsuccκ hκf hn
  obtain ⟨hβlam, hωβ, hsuccβ, hβnext⟩ :=
    criticalIterate_closed_orbit h hlamθ hclosed hκlam hωκ hsuccκ hκf (ω_succ_closed hn)
  let := IsOrdinal.of_mem hνlam
  let := IsOrdinal.of_mem hβlam
  have hβf : criticalIterate f κ (succ (succ m)) ∈ f ‘ (criticalIterate f κ (succ (succ m))) := by
    rwa [criticalIterate_succ f κ (ω_succ_closed hn)] at hβnext
  obtain ⟨hβnlam, hωβn, hsuccβn, -⟩ :=
    criticalIterate_closed_orbit h hlamθ hclosed hβlam hωβ hsuccβ hβf hn
  let := IsOrdinal.of_mem hβnlam
  -- the forward orbits of `γ` and of `β` stay inside `lam`
  have horbitγ : ∀ i ∈ (ω : V), criticalIterate f γ i ∈ lam :=
    fun _ hi ↦ criticalIterate_mem_of_closed hclosed hγ hi
  have horbitβ : ∀ i ∈ (ω : V), criticalIterate f (criticalIterate f κ (succ (succ m))) i ∈ lam :=
    fun _ hi ↦ criticalIterate_mem_of_closed hclosed hβlam hi
  -- the iterate on `V_γ` is a small embedding for the pair `(f^n ‘ κ, f^n ‘ γ)`
  let := hierarchy_transitive γ
  have hκH : κ ∈ hierarchy γ := ordinal_mem_hierarchy_iff.mpr hκγ
  have hEγ : IsCodedMembershipEmbedding (hierarchy γ)
      (hierarchy (criticalIterate f γ (succ m))) (supportEmbeddingIterate f γ (succ m)) :=
    supportEmbeddingIterate_embedding hω hsucc hω' hsucc' h hωlam hsucclam hlamθ hFlam
      ⟨κ, hκγ⟩ horbitγ hγord hn
  have hcritγ : IsCriticalPoint (hierarchy γ) (supportEmbeddingIterate f γ (succ m)) κ :=
    supportEmbeddingIterate_criticalPoint h hlamθ horbitγ hκ hγord hκH hm
  have hwit : IsMagidorSupercompactAt (criticalIterate f κ (succ m))
      (criticalIterate f γ (succ m)) :=
    ⟨γ, hγn, κ, hκγ, supportEmbeddingIterate f γ (succ m), hEγ, hcritγ,
      value_supportEmbeddingIterate hκH⟩
  -- the iterate on `V_β` carries it back down
  have hEβ : IsCodedMembershipEmbedding (hierarchy (criticalIterate f κ (succ (succ m))))
      (hierarchy (criticalIterate f (criticalIterate f κ (succ (succ m))) (succ m)))
      (supportEmbeddingIterate f (criticalIterate f κ (succ (succ m))) (succ m)) :=
    supportEmbeddingIterate_embedding hω hsucc hω' hsucc' h hωlam hsucclam hlamθ hFlam
      ⟨criticalIterate f κ (succ m), hνβ⟩ horbitβ inferInstance hn
  have hFν : (formulaFamily membershipLanguageCode ∅ : V) ∈
      hierarchy (criticalIterate f κ (succ m)) :=
    hierarchy_mono (ordinalAdd_omega_subset_of_successor_closed hων hsuccν) _ hF
  let := hierarchy_transitive (criticalIterate f κ (succ (succ m)))
  have hγβ : γ ∈ criticalIterate f κ (succ (succ m)) :=
    IsOrdinal.toIsTransitive.mem_trans hγn hνβ
  have hκβ : κ ∈ criticalIterate f κ (succ (succ m)) :=
    IsOrdinal.toIsTransitive.mem_trans hκγ hγβ
  have hκHβ : κ ∈ hierarchy (criticalIterate f κ (succ (succ m))) :=
    ordinal_mem_hierarchy_iff.mpr hκβ
  have hγHβ : γ ∈ hierarchy (criticalIterate f κ (succ (succ m))) :=
    ordinal_mem_hierarchy_iff.mpr hγβ
  have hiff := supportEmbedding_magidorSupercompactAt_iff hωβ hsuccβ hωβn hsuccβn hEβ
    hων hsuccν hνβ hFν hκγ hγn
  rw [value_supportEmbeddingIterate hκHβ, value_supportEmbeddingIterate hγHβ] at hiff
  exact hiff.mpr hwit

/-- Magidor's Lemma 3.1 in the two cases where the finite iterates of `f` that Bagaria's proof
composes are available: either one step of `f` already passes above all of `lam`, or `lam` is
closed under `f` and all the steps stay inside `lam`. -/
theorem magidorSupercompactUpTo_of_criticalPoint (hAC : InternalChoice V)
    (hcase : (∀ δ ∈ lam, f ‘ δ ∈ lam) ∨ lam ⊆ f ‘ κ) :
    IsMagidorSupercompactUpTo κ lam := by
  rcases hcase with hclosed | hsub
  · exact magidorSupercompactUpTo_of_closed hlim hωlam hlim' hωlam' hF h hκ hAC hclosed
  · exact magidorSupercompactUpTo_of_subset_value hlim hωlam hlim' hωlam' hF h hκ hsub

end Magidor

end ZFVP
