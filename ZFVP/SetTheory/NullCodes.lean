import ZFVP.SetTheory.RandomExhaustion
import ZFVP.SetTheory.MeasurableStrongLimit

/-! Null codes: sequences of covers, one of measure `2^{-m}` for each `m`, and the coded null `G_δ`
sets they determine. Non-positive trees have codes enumerating a small level for each precision,
and the exhaustion certificate of a dense set of random conditions packages into a single code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A code: for each `m`, a cover of measure at most `2^{-m}`. -/
def IsNullCode (F : V) : Prop := ∀ m ∈ (ω : V), ∀ k ∈ (ω : V), SmallMeasure ((F ‘ m) “ k) m

instance isNullCode_definable : ℒₛₑₜ-predicate[V] IsNullCode := by
  unfold IsNullCode
  definability

noncomputable def nullCodes (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  {F ∈ ((binarySequences V) ^ (ω : V)) ^ (ω : V) ; IsNullCode F}

theorem mem_nullCodes_iff (F : V) :
    F ∈ nullCodes V ↔ F ∈ ((binarySequences V) ^ (ω : V)) ^ (ω : V) ∧ IsNullCode F :=
  mem_sep_iff

/-- `x` meets every cover of the code. -/
def CodedMeets (F x : V) : Prop :=
  ∀ m ∈ (ω : V), ∃ i ∈ (ω : V), x ↾ (domain ((F ‘ m) ‘ i)) = (F ‘ m) ‘ i

instance codedMeets_definable : ℒₛₑₜ-relation[V] CodedMeets := by
  unfold CodedMeets
  definability

/-- The coded null set. -/
noncomputable def codedNull (F : V) : V := {x ∈ cantorSpace V ; CodedMeets F x}

instance codedNull_definable : ℒₛₑₜ-function₁[V] codedNull := by
  have h : ℒₛₑₜ-relation (fun N F : V ↦ ∀ x, x ∈ N ↔ x ∈ cantorSpace V ∧ CodedMeets F x) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = codedNull (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [codedNull, mem_sep_iff]

theorem mem_codedNull_iff (F x : V) : x ∈ codedNull F ↔ x ∈ cantorSpace V ∧ CodedMeets F x := mem_sep_iff

theorem isNull_codedNull {F : V} (hF : F ∈ nullCodes V) : IsNull (codedNull F) := by
  obtain ⟨hFf, hcode⟩ := (mem_nullCodes_iff F).mp hF
  intro m hm
  refine ⟨F ‘ m, function_value_mem hFf hm, fun x hx ↦ ((mem_codedNull_iff _ _).mp hx).2 m hm, hcode m hm⟩

theorem codedNull_subset_cantorSpace (F : V) : codedNull F ⊆ cantorSpace V :=
  fun x hx ↦ ((mem_codedNull_iff _ _).mp hx).1

/-- The constant function with value `a` on `ω`. -/
theorem const_mem_function {A a : V} (ha : a ∈ A) : (ω : V) ×ˢ ({a} : V) ∈ A ^ (ω : V) := by
  rw [mem_function_iff]
  refine ⟨prod_subset_prod_of_subset (fun x hx ↦ hx) (fun x hx ↦ by rw [mem_singleton_iff] at hx; rw [hx]; exact ha),
    fun n hn ↦ ⟨a, kpair_mem_iff.mpr ⟨hn, mem_singleton_iff.mpr rfl⟩, fun y hy ↦ mem_singleton_iff.mp (kpair_mem_iff.mp hy).2⟩⟩

theorem const_image_subset (a k : V) : image ((ω : V) ×ˢ ({a} : V)) k ⊆ ({a} : V) := by
  intro s hs
  obtain ⟨i, -, hi⟩ := (mem_image_iff' _ _ _).mp hs
  exact (kpair_mem_iff.mp hi).2

theorem zeroCodeGraph_definable : ℒₛₑₜ-function₁ (fun m : V ↦ (ω : V) ×ˢ ({zeroSequence m} : V)) := by
  unfold zeroSequence
  definability

/-- The trivial code: constant zero sequences. -/
theorem nullCodes_nonempty : IsNonempty (nullCodes V) := by
  refine ⟨definableGraph (ω : V) (fun m ↦ (ω : V) ×ˢ ({zeroSequence m} : V)) zeroCodeGraph_definable,
    (mem_nullCodes_iff _).mpr ⟨?_, ?_⟩⟩
  · exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun m hm ↦ const_mem_function (zeroSequence_mem_binarySequences hm))
  · intro m hm k _
    rw [value_definableGraph _ _ _ hm]
    exact smallMeasure_mono_family (smallMeasure_singleton_zeroSequence hm) (const_image_subset _ _)

/-- The level enumerations of a tree at precision `m`: a level `M` with small level set and a
sequence enumerating it, of measure at most `2^{-m}`. -/
def LevelEnumPair (T m q : V) : Prop :=
  kpair.π₁ q ∈ (ω : V) ∧ kpair.π₂ q ∈ (binarySequences V) ^ (ω : V) ∧
    (∀ k ∈ (ω : V), SmallMeasure ((kpair.π₂ q) “ k) m) ∧
    ∀ s ∈ levelSet T (kpair.π₁ q), ∃ i ∈ (ω : V), (kpair.π₂ q) ‘ i = s

instance levelEnumPair_definable : ℒₛₑₜ-relation₃[V] LevelEnumPair := by
  unfold LevelEnumPair levelSet
  definability

noncomputable def levelEnumSet (T m : V) : V :=
  {q ∈ (ω : V) ×ˢ ((binarySequences V) ^ (ω : V)) ; LevelEnumPair T m q}

instance levelEnumSet_definable (T : V) : ℒₛₑₜ-function₁[V] (levelEnumSet T) := by
  have h : ℒₛₑₜ-relation (fun C m : V ↦ ∀ q, q ∈ C ↔
      q ∈ (ω : V) ×ˢ ((binarySequences V) ^ (ω : V)) ∧ LevelEnumPair T m q) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = levelEnumSet T (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [levelEnumSet, mem_sep_iff]

theorem mem_levelEnumSet_iff (T m q : V) :
    q ∈ levelEnumSet T m ↔ q ∈ (ω : V) ×ˢ ((binarySequences V) ^ (ω : V)) ∧ LevelEnumPair T m q :=
  mem_sep_iff

theorem levelEnumSet_nonempty {T m : V} (hm : m ∈ (ω : V))
    (hsmall : ∃ M ∈ (ω : V), levelSet T M ×ˢ (((2 : ℕ) : V) ^ m) ≤# ((2 : ℕ) : V) ^ M) :
    IsNonempty (levelEnumSet T m) := by
  obtain ⟨M, hM, hMsmall⟩ := hsmall
  have hDω : levelSet T M ≤# (ω : V) := by
    obtain ⟨n, hn, hle⟩ := levelSet_finite (T := T) hM
    exact hle.le.trans (cardLE_of_subset (IsTransitive.ω.transitive n hn))
  obtain ⟨g, hg, hgcov, hgsurj⟩ := exists_cover_of_enumerable (A := (∅ : V)) hm (levelSet_subset_binarySequences hM)
    hDω (fun x hx ↦ (not_mem_empty hx).elim) (fun F hF _ ↦ by
      refine ⟨M, hM, fun s hs ↦ by rw [domain_eq_of_mem_function ((mem_levelSet_iff _ _ _).mp (hF s hs)).2], ?_⟩
      rw [shadow_self (fun s hs ↦ ((mem_levelSet_iff _ _ _).mp (hF s hs)).2)]
      exact (prod_cardLE_prod (cardLE_of_subset hF) (CardLE.refl _)).trans hMsmall)
  refine ⟨⟨M, g⟩ₖ, (mem_levelEnumSet_iff _ _ _).mpr ⟨kpair_mem_iff.mpr ⟨hM, hg⟩, ?_⟩⟩
  unfold LevelEnumPair
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  exact ⟨hM, hg, hgcov.2, hgsurj⟩

theorem enumPi2_definable (c T : V) : ℒₛₑₜ-function₁ (fun m : V ↦ kpair.π₂ (c ‘ (levelEnumSet T m))) := by
  definability

/-- A non-positive tree has a null code enumerating a small level for each precision. -/
theorem exists_code_of_not_positive (hAC : InternalChoice V) {T : V} (hT : IsTree T) (h : ¬ IsPositiveTree T) :
    ∃ F ∈ nullCodes V, ∀ m ∈ (ω : V), ∃ M ∈ (ω : V), ∀ s ∈ levelSet T M, ∃ i ∈ (ω : V), (F ‘ m) ‘ i = s := by
  have hsmall : ∀ m ∈ (ω : V), ∃ M ∈ (ω : V), levelSet T M ×ˢ (((2 : ℕ) : V) ^ m) ≤# ((2 : ℕ) : V) ^ M := by
    intro m hm
    by_contra hcon
    push Not at hcon
    exact h ⟨hT, m, hm, hcon⟩
  obtain ⟨ℒ, hℒdef⟩ : ∃ L : V, L = repl (levelEnumSet T) (levelEnumSet_definable T) (ω : V) := ⟨_, rfl⟩
  obtain ⟨c, -, hcval⟩ := hAC ℒ (fun X hX ↦ by
    rw [hℒdef] at hX
    obtain ⟨m, hm, rfl⟩ := (repl_spec (levelEnumSet_definable T)).mp hX
    exact levelEnumSet_nonempty hm (hsmall m hm))
  have hc : ∀ m ∈ (ω : V), LevelEnumPair T m (c ‘ (levelEnumSet T m)) := fun m hm ↦
    ((mem_levelEnumSet_iff _ _ _).mp (hcval _ (by
      rw [hℒdef]; exact (repl_spec (levelEnumSet_definable T)).mpr ⟨m, hm, rfl⟩))).2
  obtain ⟨F, hFdef⟩ : ∃ F : V, F = definableGraph (ω : V) (fun m ↦ kpair.π₂ (c ‘ (levelEnumSet T m)))
    (enumPi2_definable c T) := ⟨_, rfl⟩
  have hFval : ∀ m ∈ (ω : V), F ‘ m = kpair.π₂ (c ‘ (levelEnumSet T m)) := by
    intro m hm
    rw [hFdef]
    exact value_definableGraph _ _ _ hm
  refine ⟨F, (mem_nullCodes_iff F).mpr ⟨?_, fun m hm k hk ↦ ?_⟩, fun m hm ↦ ?_⟩
  · rw [hFdef]
    exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun m hm ↦ (hc m hm).2.1)
  · rw [hFval m hm]
    exact (hc m hm).2.2.1 k hk
  · refine ⟨kpair.π₁ (c ‘ (levelEnumSet T m)), (hc m hm).1, fun s hs ↦ ?_⟩
    rw [hFval m hm]
    exact (hc m hm).2.2.2 s hs

/-- The certificate triples `(Mseq, M, f)` at precision `m` for a sequence `E` of trees. -/
def CertTriple (E m q : V) : Prop :=
  kpair.π₁ q ∈ (ω : V) ^ (ω : V) ∧ kpair.π₁ (kpair.π₂ q) ∈ (ω : V) ∧
    kpair.π₂ (kpair.π₂ q) ∈ (binarySequences V) ^ (ω : V) ∧
    (∀ k ∈ (ω : V), SmallMeasure ((kpair.π₂ (kpair.π₂ q)) “ k) m) ∧
    (∀ n ∈ (ω : V), ∀ s ∈ binarySequences V, LeavesTree (E ‘ n) ((kpair.π₁ q) ‘ n) s →
      ∃ i ∈ (ω : V), (kpair.π₂ (kpair.π₂ q)) ‘ i = s) ∧
    ∀ s ∈ levelSet (avoidTree E (kpair.π₁ q)) (kpair.π₁ (kpair.π₂ q)), ∃ i ∈ (ω : V), (kpair.π₂ (kpair.π₂ q)) ‘ i = s

instance certTriple_definable : ℒₛₑₜ-relation₃[V] CertTriple := by
  unfold CertTriple levelSet avoidTree
  definability

noncomputable def certSet (E m : V) : V :=
  {q ∈ ((ω : V) ^ (ω : V)) ×ˢ ((ω : V) ×ˢ ((binarySequences V) ^ (ω : V))) ; CertTriple E m q}

instance certSet_definable (E : V) : ℒₛₑₜ-function₁[V] (certSet E) := by
  have h : ℒₛₑₜ-relation (fun C m : V ↦ ∀ q, q ∈ C ↔
      q ∈ ((ω : V) ^ (ω : V)) ×ˢ ((ω : V) ×ˢ ((binarySequences V) ^ (ω : V))) ∧ CertTriple E m q) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = certSet E (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [certSet, mem_sep_iff]

theorem mem_certSet_iff (E m q : V) : q ∈ certSet E m ↔
    q ∈ ((ω : V) ^ (ω : V)) ×ˢ ((ω : V) ×ˢ ((binarySequences V) ^ (ω : V))) ∧ CertTriple E m q :=
  mem_sep_iff

theorem certPi_definable (c E : V) :
    ℒₛₑₜ-function₁ (fun m : V ↦ kpair.π₂ (kpair.π₂ (c ‘ (certSet E m)))) := by
  definability

/-- The random code of a dense set: a sequence `E` in `D` and a null code `F` with, for each `m`,
levels `Mseq m` and `M m` such that `F m` enumerates the sequences leaving `E n` above `Mseq m n`
and the level `M m` of the avoiding tree. -/
theorem exists_random_code (hAC : InternalChoice V) {D : V} (hD : D ⊆ randomConditions V)
    (hdense : ForcingDense (randomConditions V) (inclusionOrder (randomConditions V)) D) :
    ∃ E ∈ (randomConditions V) ^ (ω : V), (∀ n ∈ (ω : V), E ‘ n ∈ D) ∧ ∃ F ∈ nullCodes V, ∃ c : V,
      ∀ m ∈ (ω : V), CertTriple E m (c ‘ (certSet E m)) ∧ F ‘ m = kpair.π₂ (kpair.π₂ (c ‘ (certSet E m))) := by
  obtain ⟨E, hE, hED, hcert⟩ := exists_random_certificate hAC hD hdense
  have hne : ∀ m ∈ (ω : V), IsNonempty (certSet E m) := by
    intro m hm
    obtain ⟨Mseq, hMseq, M, hM, f, hf, hsmall, hleave, hlevel⟩ := hcert m hm
    refine ⟨⟨Mseq, ⟨M, f⟩ₖ⟩ₖ, (mem_certSet_iff _ _ _).mpr ⟨kpair_mem_iff.mpr ⟨hMseq, kpair_mem_iff.mpr ⟨hM, hf⟩⟩, ?_⟩⟩
    unfold CertTriple
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨hMseq, hM, hf, hsmall, hleave, hlevel⟩
  obtain ⟨ℒ, hℒdef⟩ : ∃ L : V, L = repl (certSet E) (certSet_definable E) (ω : V) := ⟨_, rfl⟩
  obtain ⟨c, -, hcval⟩ := hAC ℒ (fun X hX ↦ by
    rw [hℒdef] at hX
    obtain ⟨m, hm, rfl⟩ := (repl_spec (certSet_definable E)).mp hX
    exact hne m hm)
  have hc : ∀ m ∈ (ω : V), CertTriple E m (c ‘ (certSet E m)) := fun m hm ↦
    ((mem_certSet_iff _ _ _).mp (hcval _ (by
      rw [hℒdef]; exact (repl_spec (certSet_definable E)).mpr ⟨m, hm, rfl⟩))).2
  obtain ⟨F, hFdef⟩ : ∃ F : V, F = definableGraph (ω : V) (fun m ↦ kpair.π₂ (kpair.π₂ (c ‘ (certSet E m))))
    (certPi_definable c E) := ⟨_, rfl⟩
  have hFval : ∀ m ∈ (ω : V), F ‘ m = kpair.π₂ (kpair.π₂ (c ‘ (certSet E m))) := by
    intro m hm
    rw [hFdef]
    exact value_definableGraph _ _ _ hm
  refine ⟨E, hE, hED, F, (mem_nullCodes_iff F).mpr ⟨?_, fun m hm k hk ↦ ?_⟩, c, fun m hm ↦ ⟨hc m hm, hFval m hm⟩⟩
  · rw [hFdef]
    exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun m hm ↦ (hc m hm).2.2.1)
  · rw [hFval m hm]
    exact (hc m hm).2.2.2.1 k hk

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U) (hω : (ω : V) ∈ κ)

include hAC hU hc hω in
/-- Below a measurable, the null codes are fewer than `κ`. -/
theorem nullCodes_small : ∃ ν ∈ κ, nullCodes V ≤# ν := by
  have hB : binarySequences V ≤# (ω : V) := binarySequences_countable hAC
  have h1 : (binarySequences V) ^ (ω : V) ≤# ℘ (ω : V) := by
    refine CardLE.trans (cardLE_of_subset (fun f hf ↦ mem_power_iff.mpr (mem_function_iff.mp hf).1)) ?_
    exact (power_cardLE_of_cardLE ((prod_cardLE_prod (CardLE.refl _) hB).trans omega_prod_cardLE_omega))
  obtain ⟨ν₁, hν₁, hpow₁⟩ := power_small_of_measurable hAC hU hc hω (CardLE.refl (ω : V))
  have : IsOrdinal ν₁ := IsOrdinal.of_mem hν₁
  have hBω : (binarySequences V) ^ (ω : V) ≤# ν₁ := h1.trans hpow₁
  have hν₁' : ν₁ ∪ (ω : V) ∈ κ := union_mem_of_ordinals hν₁ hω
  have : IsOrdinal (ν₁ ∪ (ω : V)) := ordinal_union_isOrdinal ν₁ (ω : V)
  have h3 : (ω : V) ×ˢ ((binarySequences V) ^ (ω : V)) ≤# (ν₁ ∪ (ω : V)) ×ˢ (ν₁ ∪ (ω : V)) :=
    prod_cardLE_prod (cardLE_of_subset (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)))
      (hBω.trans (cardLE_of_subset (fun x hx ↦ mem_union_iff.mpr (Or.inl hx))))
  have h4 : (ν₁ ∪ (ω : V)) ×ˢ (ν₁ ∪ (ω : V)) ≤# (ν₁ ∪ (ω : V)) ∪ (ω : V) :=
    ordinal_prod_cardLE_union_omega (ν₁ ∪ (ω : V))
  have h5 : (ν₁ ∪ (ω : V)) ∪ (ω : V) ⊆ ν₁ ∪ (ω : V) := by
    intro x hx
    rcases mem_union_iff.mp hx with hx | hx
    · exact hx
    · exact mem_union_iff.mpr (Or.inr hx)
  have h2 : ((binarySequences V) ^ (ω : V)) ^ (ω : V) ≤# ℘ (ν₁ ∪ (ω : V)) :=
    (cardLE_of_subset (fun f hf ↦ mem_power_iff.mpr (mem_function_iff.mp hf).1)).trans
      (power_cardLE_of_cardLE (h3.trans (h4.trans (cardLE_of_subset h5))))
  obtain ⟨ν₂, hν₂, hpow₂⟩ := power_small_of_measurable hAC hU hc hν₁' (CardLE.refl _)
  exact ⟨ν₂, hν₂, (cardLE_of_subset (fun F hF ↦ ((mem_nullCodes_iff F).mp hF).1)).trans (h2.trans hpow₂)⟩

include hAC hU hc hω in
theorem randomConditions_small : ∃ ν ∈ κ, randomConditions V ≤# ν := by
  have hB : binarySequences V ≤# (ω : V) := binarySequences_countable hAC
  obtain ⟨ν, hν, hpow⟩ := power_small_of_measurable hAC hU hc hω hB
  exact ⟨ν, hν, (cardLE_of_subset (fun T hT ↦ (mem_sep_iff.mp hT).1)).trans hpow⟩

end

end ZFVP
