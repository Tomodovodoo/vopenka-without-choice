import ZFVP.SetTheory.RigidProductRelations
import ZFVP.SetTheory.NaturalPairing
import ZFVP.SetTheory.FunctionUnion

/-! Coding a finite sequence of reals by a single real, in ZF and without any choice.

A finite sequence `s` of reals with domain the natural `n` is coded by the real `realCode s`
whose bit at the natural `naturalPairCode 0 i` is `1` exactly when `i ∈ n`, and whose bit at
`naturalPairCode (succ k) i` is the `k`-th bit of `s ‘ i` when `i ∈ n`. Since `naturalPairCode`
is an injective pairing of naturals, the length and every bit of every entry can be read back,
so the coding is injective and `finiteSequences (cantorSpace V) ≤# cantorSpace V`.

Combined with `hasRigidRelation_of_subset_cantor_ordinal` this gives a rigid relation on every
subset of `finiteSequences (cantorSpace V) ×ˢ γ` for an ordinal `γ`. This is the step Hamkins
and Palumbo take between their Theorem 4 and their Theorem 6. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Two facts about naturals -/

theorem succ_ne_zero_of_natural (k : V) : succ k ≠ (0 : V) := by
  intro h
  have hk : k ∈ succ k := mem_succ_self k
  rw [h, zero_def] at hk
  exact not_mem_empty hk

theorem succ_inj_of_natural {k k' : V} (hk : k ∈ (ω : V)) (hk' : k' ∈ (ω : V))
    (h : succ k = succ k') : k = k' := by
  have : IsOrdinal k := IsOrdinal.of_mem hk
  have : IsOrdinal k' := IsOrdinal.of_mem hk'
  have h1 : k ∈ succ k' := h ▸ mem_succ_self k
  have h2 : k' ∈ succ k := h.symm ▸ mem_succ_self k'
  rcases mem_succ_iff.mp h1 with e | e
  · exact e
  rcases mem_succ_iff.mp h2 with e' | e'
  · exact e'.symm
  exact (mem_irrefl k (IsOrdinal.toIsTransitive.mem_trans e e')).elim

theorem zero_mem_omega : (0 : V) ∈ (ω : V) := by
  rw [zero_def]
  exact empty_mem_ω

/-! ### The bits of the code -/

/-- The code of the finite sequence `s` carries a `1` at the natural `m` exactly when this
holds: either `m` is the length marker `naturalPairCode 0 i` of an index `i` of `s`, or `m` is
`naturalPairCode (succ k) i` for an index `i` of `s` and a natural `k` with the `k`-th bit of
`s ‘ i` equal to `1`. -/
def SeqCodeSpec (s m : V) : Prop :=
  (∃ i ∈ domain s, m = naturalPairCode 0 i) ∨
    (∃ i ∈ domain s, ∃ k ∈ (ω : V), m = naturalPairCode (succ k) i ∧ (s ‘ i) ‘ k = 1)

instance seqCodeSpec_definable : ℒₛₑₜ-relation[V] SeqCodeSpec := by
  unfold SeqCodeSpec
  definability

/-- The bit of the code of `s` at `m`: `1` if `SeqCodeSpec s m` holds and `0` otherwise. -/
noncomputable def seqCodeBit (s m : V) : V := {z ∈ (1 : V) ; SeqCodeSpec s m}

instance seqCodeBit_definable : ℒₛₑₜ-function₂[V] seqCodeBit := by
  have h : ℒₛₑₜ-relation₃ (fun y s m : V ↦ ∀ z, z ∈ y ↔ z ∈ (1 : V) ∧ SeqCodeSpec s m) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = seqCodeBit (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [seqCodeBit]

theorem seqCodeBit_eq_one {s m : V} (h : SeqCodeSpec s m) : seqCodeBit s m = 1 := by
  apply mem_ext
  intro z
  simp [seqCodeBit, h]

theorem seqCodeBit_eq_zero {s m : V} (h : ¬ SeqCodeSpec s m) : seqCodeBit s m = 0 := by
  apply mem_ext
  intro z
  simp [seqCodeBit, h, zero_def]

theorem seqCodeBit_eq_one_iff {s m : V} : seqCodeBit s m = 1 ↔ SeqCodeSpec s m := by
  constructor
  · intro h
    by_contra hc
    exact zero_ne_one ((seqCodeBit_eq_zero hc).symm.trans h)
  · exact seqCodeBit_eq_one

theorem seqCodeBit_mem_two (s m : V) : seqCodeBit s m ∈ ((2 : ℕ) : V) := by
  by_cases h : SeqCodeSpec s m
  · rw [seqCodeBit_eq_one h]; simp
  · rw [seqCodeBit_eq_zero h]; simp

/-! ### The code of a finite sequence of reals -/

/-- The real coding the finite sequence `s`. -/
noncomputable def realCode (s : V) : V :=
  definableGraph (ω : V) (fun m ↦ seqCodeBit s m) (by definability)

instance realCode_definable : ℒₛₑₜ-function₁[V] realCode := by
  have h : ℒₛₑₜ-relation (fun y s : V ↦ ∀ p, p ∈ y ↔ ∃ m ∈ (ω : V), p = ⟨m, seqCodeBit s m⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = realCode (v 1) ↔ _
  rw [mem_ext_iff]
  simp [realCode, mem_definableGraph_iff]

theorem realCode_mem_cantorSpace (s : V) : realCode s ∈ cantorSpace V :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun m _ ↦ seqCodeBit_mem_two s m)

theorem realCode_value {s m : V} (hm : m ∈ (ω : V)) : (realCode s) ‘ m = seqCodeBit s m :=
  value_definableGraph _ _ _ hm

/-- The length marker: the code of `s` has a `1` at `naturalPairCode 0 i` exactly for the
indices `i` of `s`. -/
theorem realCode_marker {s i : V} (hs : s ∈ finiteSequences (cantorSpace V))
    (hi : i ∈ (ω : V)) : (realCode s) ‘ (naturalPairCode 0 i) = 1 ↔ i ∈ domain s := by
  obtain ⟨hd, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  have hsub : domain s ⊆ (ω : V) := IsTransitive.transitive _ hd
  have h0 : (0 : V) ∈ (ω : V) := zero_mem_omega
  rw [realCode_value (naturalPairCode_natural h0 hi), seqCodeBit_eq_one_iff]
  constructor
  · rintro (⟨i', hi', he⟩ | ⟨i', hi', k, hk, he, -⟩)
    · have hii := (naturalPairCode_injective h0 hi h0 (hsub i' hi') he).2
      exact hii.symm ▸ hi'
    · exact absurd (naturalPairCode_injective h0 hi (ω_succ_closed hk) (hsub i' hi') he).1.symm
        (succ_ne_zero_of_natural k)
  · intro h
    exact Or.inl ⟨i, h, rfl⟩

/-- The bits: for an index `i` of `s` and a natural `k`, the code of `s` has a `1` at
`naturalPairCode (succ k) i` exactly when the `k`-th bit of `s ‘ i` is `1`. -/
theorem realCode_bit {s i k : V} (hs : s ∈ finiteSequences (cantorSpace V))
    (hi : i ∈ domain s) (hk : k ∈ (ω : V)) :
    (realCode s) ‘ (naturalPairCode (succ k) i) = 1 ↔ (s ‘ i) ‘ k = 1 := by
  obtain ⟨hd, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  have hsub : domain s ⊆ (ω : V) := IsTransitive.transitive _ hd
  have h0 : (0 : V) ∈ (ω : V) := zero_mem_omega
  rw [realCode_value (naturalPairCode_natural (ω_succ_closed hk) (hsub i hi)),
    seqCodeBit_eq_one_iff]
  constructor
  · rintro (⟨i', hi', he⟩ | ⟨i', hi', k', hk', he, hval⟩)
    · exact absurd
        (naturalPairCode_injective (ω_succ_closed hk) (hsub i hi) h0 (hsub i' hi') he).1
        (succ_ne_zero_of_natural k)
    · obtain ⟨hkk, hii⟩ := naturalPairCode_injective (ω_succ_closed hk) (hsub i hi)
        (ω_succ_closed hk') (hsub i' hi') he
      rw [hii, succ_inj_of_natural hk hk' hkk]
      exact hval
  · intro h
    exact Or.inr ⟨i, hi, k, hk, rfl, h⟩

/-- Distinct finite sequences of reals get distinct codes. -/
theorem realCode_inj {s t : V} (hs : s ∈ finiteSequences (cantorSpace V))
    (ht : t ∈ finiteSequences (cantorSpace V)) (h : realCode s = realCode t) : s = t := by
  obtain ⟨hds, hsf⟩ := (mem_finiteSequences_iff_domain _ s).mp hs
  obtain ⟨hdt, htf⟩ := (mem_finiteSequences_iff_domain _ t).mp ht
  have hsubs : domain s ⊆ (ω : V) := IsTransitive.transitive _ hds
  have hsubt : domain t ⊆ (ω : V) := IsTransitive.transitive _ hdt
  have hdom : domain s = domain t := by
    apply mem_ext
    intro i
    constructor
    · intro hi
      exact (realCode_marker ht (hsubs i hi)).mp (h ▸ (realCode_marker hs (hsubs i hi)).mpr hi)
    · intro hi
      exact (realCode_marker hs (hsubt i hi)).mp (h ▸ (realCode_marker ht (hsubt i hi)).mpr hi)
  have : IsFunction s := IsFunction.of_mem hsf
  have : IsFunction t := IsFunction.of_mem htf
  apply functions_eq_of_domain_values hdom
  intro i hi
  have hsi : s ‘ i ∈ cantorSpace V := function_value_mem hsf hi
  have hti : t ‘ i ∈ cantorSpace V := function_value_mem htf (hdom ▸ hi)
  apply cantor_eq_of_values hsi hti
  intro k hk
  have hiff : (s ‘ i) ‘ k = 1 ↔ (t ‘ i) ‘ k = 1 := by
    rw [← realCode_bit hs hi hk, ← realCode_bit ht (hdom ▸ hi) hk, h]
  rcases cantor_value_mem_two hsi hk with h1 | h1 <;>
    rcases cantor_value_mem_two hti hk with h2 | h2
  · rw [h1, h2]
  · exact absurd (h1.symm.trans (hiff.mpr h2)) zero_ne_one
  · exact absurd (h2.symm.trans (hiff.mp h1)) zero_ne_one
  · rw [h1, h2]

/-! ### The two exported statements -/

/-- A finite sequence of reals is coded by a single real. -/
theorem cardLE_cantorSpace_finiteSequences :
    finiteSequences (cantorSpace V) ≤# cantorSpace V := by
  refine ⟨definableGraph (finiteSequences (cantorSpace V)) realCode realCode_definable,
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun s _ ↦ realCode_mem_cantorSpace s), ?_⟩
  intro s t z hs ht
  obtain ⟨hsA, hzs⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hs
  obtain ⟨htA, hzt⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp ht
  exact realCode_inj hsA htA (hzs.symm.trans hzt)

/-- Every subset of `finiteSequences (cantorSpace V) ×ˢ γ` for an ordinal `γ` carries a rigid
relation. -/
theorem hasRigidRelation_of_subset_finiteSequences_prod {A γ : V} (hγ : IsOrdinal γ)
    (hA : A ⊆ finiteSequences (cantorSpace V) ×ˢ γ) : HasRigidRelation A := by
  classical
  have hG : ℒₛₑₜ-function₁ (fun u : V ↦ ⟨realCode (kpair.π₁ u), kpair.π₂ u⟩ₖ) := by definability
  have hf := definableGraph_mem_function A (fun u : V ↦ ⟨realCode (kpair.π₁ u), kpair.π₂ u⟩ₖ) hG
  have hran := range_definableGraph A (fun u : V ↦ ⟨realCode (kpair.π₁ u), kpair.π₂ u⟩ₖ) hG
  have hBsub : repl (fun u : V ↦ ⟨realCode (kpair.π₁ u), kpair.π₂ u⟩ₖ) hG A ⊆
      cantorSpace V ×ˢ γ := by
    intro y hy
    obtain ⟨u, huA, rfl⟩ := (repl_spec hG).mp hy
    obtain ⟨-, -, h3⟩ := eq_kpair_of_mem_prod (hA u huA)
    exact mem_prod_iff.mpr ⟨_, realCode_mem_cantorSpace _, kpair.π₂ u, h3, rfl⟩
  have hinj : Injective (definableGraph A
      (fun u : V ↦ ⟨realCode (kpair.π₁ u), kpair.π₂ u⟩ₖ) hG) := by
    intro u v z hu hv
    obtain ⟨huA, hzu⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hu
    obtain ⟨hvA, hzv⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hv
    obtain ⟨hu1, hu2, -⟩ := eq_kpair_of_mem_prod (hA u huA)
    obtain ⟨hv1, hv2, -⟩ := eq_kpair_of_mem_prod (hA v hvA)
    have he : (⟨realCode (kpair.π₁ u), kpair.π₂ u⟩ₖ : V)
        = ⟨realCode (kpair.π₁ v), kpair.π₂ v⟩ₖ := hzu.symm.trans hzv
    obtain ⟨he1, he2⟩ := kpair_iff.mp he
    rw [hu1, hv1, realCode_inj hu2 hv2 he1, he2]
  exact hasRigidRelation_of_bijection hf hinj hran
    (hasRigidRelation_of_subset_cantor_ordinal hγ hBsub)

end ZFVP
