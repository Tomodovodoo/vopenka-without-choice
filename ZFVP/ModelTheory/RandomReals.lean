import ZFVP.SetTheory.NullCodes
import ZFVP.ModelTheory.LevySmallSetLocalization
import ZFVP.ModelTheory.PerfectSetDecision
import ZFVP.ModelTheory.DecidedName

/-! Random reals over the ground model in the Levy extension: a real is random if it avoids every
ground-coded null set. The non-random reals form a null set, and a random real determines a
filter of ground positive trees which meets every ground dense set of random conditions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem extendsPredicate_definable (F : V) : ℒₛₑₜ-predicate (fun t : V ↦ ∃ s ∈ F, s ⊆ t) := by
  definability

namespace ForcingContext

variable (S : ForcingContext V)

theorem check_power_two {M : V} (hM : M ∈ (ω : V)) :
    S.check (((2 : ℕ) : V) ^ M) = ((2 : ℕ) : S.Model) ^ (S.check M) := by
  have h := S.checkEmbedding.map_finiteFunctionSet ((2 : ℕ) : V) hM
  have h2 := S.checkEmbedding.map_numeral 2
  change S.check (((2 : ℕ) : V) ^ M) = S.check ((2 : ℕ) : V) ^ S.check M at h
  change S.check ((2 : ℕ) : V) = ((2 : ℕ) : S.Model) at h2
  rw [h, h2]

theorem check_levelSet {T M : V} (hM : M ∈ (ω : V)) :
    S.check (levelSet T M) = levelSet (S.check T) (S.check M) := by
  unfold levelSet
  have h := S.checkEmbedding.map_inter T (((2 : ℕ) : V) ^ M)
  change S.check (T ∩ ((2 : ℕ) : V) ^ M) = S.check T ∩ S.check (((2 : ℕ) : V) ^ M) at h
  rw [h, S.check_power_two hM]

theorem check_image (f k : V) : S.check (image f k) = image (S.check f) (S.check k) := by
  unfold image
  rw [S.check_range, S.check_restrict]

theorem check_shadow {F M : V} (hM : M ∈ (ω : V)) :
    S.check (shadow F M) = shadow (S.check F) (S.check M) := by
  unfold shadow
  have h := S.checkEmbedding.map_separation (((2 : ℕ) : V) ^ M) (fun t ↦ ∃ s ∈ F, s ⊆ t)
    (fun t ↦ ∃ s ∈ S.check F, s ⊆ t) (extendsPredicate_definable F) (extendsPredicate_definable (S.check F)) (by
      intro t _
      constructor
      · rintro ⟨s, hs, hst⟩
        exact ⟨S.check s, (S.check_mem_iff _ _).mpr hs, (S.checkEmbedding.subset_iff s t).mpr hst⟩
      · rintro ⟨s', hs', hst⟩
        obtain ⟨s, hs, rfl⟩ := (S.mem_check_iff _ _).mp hs'
        exact ⟨s, hs, (S.checkEmbedding.subset_iff s t).mp hst⟩)
  change S.check (sep (((2 : ℕ) : V) ^ M) (fun t ↦ ∃ s ∈ F, s ⊆ t) (extendsPredicate_definable F)) =
    sep (S.check (((2 : ℕ) : V) ^ M)) (fun t ↦ ∃ s ∈ S.check F, s ⊆ t) (extendsPredicate_definable (S.check F)) at h
  rw [h, S.check_power_two hM]

theorem check_smallMeasure {F m : V} (hm : m ∈ (ω : V)) (h : SmallMeasure F m) :
    SmallMeasure (S.check F) (S.check m) := by
  obtain ⟨M, hM, hdom, hle⟩ := h
  refine ⟨S.check M, by rw [← S.check_omega_eq]; exact (S.check_mem_iff _ _).mpr hM, fun s hs ↦ ?_, ?_⟩
  · obtain ⟨s₀, hs₀, rfl⟩ := (S.mem_check_iff _ _).mp hs
    have h := S.checkEmbedding.map_relationDomain s₀
    change S.check (domain s₀) = domain (S.check s₀) at h
    rw [← h]
    exact (S.checkEmbedding.subset_iff _ _).mpr (hdom s₀ hs₀)
  · have h1 := S.checkEmbedding.map_cardLE hle
    change S.check (shadow F M ×ˢ (((2 : ℕ) : V) ^ m)) ≤# S.check (((2 : ℕ) : V) ^ M) at h1
    have hprod := S.checkEmbedding.map_prod (shadow F M) (((2 : ℕ) : V) ^ m)
    change S.check (shadow F M ×ˢ (((2 : ℕ) : V) ^ m)) = S.check (shadow F M) ×ˢ S.check (((2 : ℕ) : V) ^ m) at hprod
    rw [hprod, S.check_shadow hM, S.check_power_two hm, S.check_power_two hM] at h1
    exact h1

theorem check_isTree {T : V} (hT : IsTree T) : IsTree (S.check T) := by
  refine ⟨fun s hs ↦ ?_, fun s hs n hn ↦ ?_⟩
  · obtain ⟨s₀, hs₀, rfl⟩ := (S.mem_check_iff _ _).mp hs
    rw [← S.check_binarySequences]
    exact (S.check_mem_iff _ _).mpr (hT.1 s₀ hs₀)
  · obtain ⟨s₀, hs₀, rfl⟩ := (S.mem_check_iff _ _).mp hs
    have : IsFunction s₀ := binarySequence_isFunction (hT.1 s₀ hs₀)
    rw [S.check_domain] at hn
    obtain ⟨n₀, hn₀, rfl⟩ := (S.mem_check_iff _ _).mp hn
    rw [← S.check_restrict]
    exact (S.check_mem_iff _ _).mpr (hT.2 s₀ hs₀ n₀ hn₀)

theorem check_mem_nullCodes {F : V} (hF : F ∈ nullCodes V) : S.check F ∈ nullCodes S.Model := by
  obtain ⟨hFf, hcode⟩ := (mem_nullCodes_iff F).mp hF
  have hFfun : IsFunction F := IsFunction.of_mem hFf
  have hFdom : domain F = (ω : V) := domain_eq_of_mem_function hFf
  refine (mem_nullCodes_iff _).mpr ⟨?_, ?_⟩
  · have h1 : S.check F ∈ S.check ((binarySequences V) ^ (ω : V)) ^ S.check (ω : V) :=
      (S.check_function_iff _ _ _).mpr hFf
    rw [S.check_omega_eq] at h1
    refine mem_function_of_mem_function_of_subset h1 (fun f hf ↦ ?_)
    obtain ⟨f₀, hf₀, rfl⟩ := (S.mem_check_iff _ _).mp hf
    have := (S.check_function_iff _ _ _).mpr hf₀
    rw [S.check_omega_eq, S.check_binarySequences] at this
    exact this
  · intro m' hm' k' hk'
    rw [← S.check_omega_eq] at hm' hk'
    obtain ⟨m, hm, rfl⟩ := (S.mem_check_iff _ _).mp hm'
    obtain ⟨k, hk, rfl⟩ := (S.mem_check_iff _ _).mp hk'
    rw [S.check_value (by rw [hFdom]; exact hm), ← S.check_image]
    exact S.check_smallMeasure hm (hcode m hm k hk)

end ForcingContext

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The non-random reals: those in a ground-coded null set. -/
noncomputable def nonRandom : (levyContext κ hG).Model :=
  {x ∈ cantorSpace (levyContext κ hG).Model ; ∃ F ∈ (levyContext κ hG).check (nullCodes V), x ∈ codedNull F}

omit [IsOrdinal κ] in
theorem mem_nonRandom_iff (x : (levyContext κ hG).Model) :
    x ∈ nonRandom hG ↔ x ∈ cantorSpace (levyContext κ hG).Model ∧
      ∃ F ∈ (levyContext κ hG).check (nullCodes V), x ∈ codedNull F :=
  mem_sep_iff

/-- A real is random over the ground model if it lies in no ground-coded null set. -/
def IsRandomOver (x : (levyContext κ hG).Model) : Prop :=
  x ∈ cantorSpace (levyContext κ hG).Model ∧ x ∉ nonRandom hG

theorem random_avoids_code {x : (levyContext κ hG).Model} (hx : IsRandomOver hG x) {F : V}
    (hF : F ∈ nullCodes V) : ¬ CodedMeets ((levyContext κ hG).check F) x := by
  intro h
  exact hx.2 ((mem_nonRandom_iff hG x).mpr ⟨hx.1, (levyContext κ hG).check F,
    ((levyContext κ hG).check_mem_iff _ _).mpr hF, (mem_codedNull_iff _ _).mpr ⟨hx.1, h⟩⟩)

theorem codedNullGraph_definable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (E : M) :
    ℒₛₑₜ-function₁ (fun n : M ↦ codedNull (E ‘ n)) := by
  definability

include hAC hU hc hω in
/-- The non-random reals form a null set. -/
theorem nonRandom_null : IsNull (nonRandom hG) := by
  let W := levyContext κ hG
  have hACW : InternalChoice W.Model := W.internalChoice_of_ground hAC
  obtain ⟨ν, hν, hsmall⟩ := nullCodes_small hAC hU hc hω
  have hcount : IsInternallyCountable (W.check (nullCodes V)) :=
    internallyCountable_of_cardLE (levy_check_countable hG hν) (W.checkEmbedding.map_cardLE hsmall)
  obtain ⟨F₀, hF₀⟩ := nullCodes_nonempty (V := V)
  obtain ⟨E, hE, hrange⟩ := exists_surjection_of_cardLE hcount ((W.check_mem_iff _ _).mpr hF₀)
  have hEf : IsFunction E := IsFunction.of_mem hE
  have hEdom : domain E = (ω : W.Model) := domain_eq_of_mem_function hE
  obtain ⟨A, hAdef⟩ : ∃ A : W.Model, A = definableGraph (ω : W.Model) (fun n ↦ codedNull (E ‘ n))
    (codedNullGraph_definable E) := ⟨_, rfl⟩
  have hAf : IsFunction A := by rw [hAdef]; exact definableGraph_isFunction _ _ _
  have hAdom : domain A = (ω : W.Model) := by rw [hAdef]; exact domain_definableGraph _ _ _
  have hAval : ∀ n ∈ (ω : W.Model), A ‘ n = codedNull (E ‘ n) := by
    intro n hn
    rw [hAdef]
    exact value_definableGraph _ _ _ hn
  have hnull : ∀ n ∈ (ω : W.Model), IsNull (A ‘ n) := by
    intro n hn
    rw [hAval n hn]
    have hEn : E ‘ n ∈ W.check (nullCodes V) := function_value_mem hE hn
    obtain ⟨F, hF, hEnF⟩ := (W.mem_check_iff _ _).mp hEn
    rw [hEnF]
    exact isNull_codedNull (W.check_mem_nullCodes hF)
  refine isNull_mono (isNull_sUnion_range hACW hAdom hnull) (fun x hx ↦ ?_)
  obtain ⟨-, F', hF', hxF'⟩ := (mem_nonRandom_iff hG x).mp hx
  have hF'r : F' ∈ range E := by rw [hrange]; exact hF'
  obtain ⟨n, hn⟩ := mem_range_iff.mp hF'r
  have hnω : n ∈ (ω : W.Model) := by rw [← hEdom]; exact mem_domain_of_kpair_mem hn
  refine mem_sUnion_iff.mpr ⟨A ‘ n, mem_range_iff.mpr ⟨n, kpair_value_mem (by rw [hAdom]; exact hnω)⟩, ?_⟩
  rw [hAval n hnω, value_eq_of_kpair_mem hn]
  exact hxF'

/-- The filter of ground positive trees whose body contains `x`. -/
noncomputable def randomFilter (x : (levyContext κ hG).Model) : (levyContext κ hG).Model :=
  {T ∈ (levyContext κ hG).check (randomConditions V) ; x ∈ treeBody T}

theorem mem_randomFilter_iff (x T : (levyContext κ hG).Model) :
    T ∈ randomFilter hG x ↔ T ∈ (levyContext κ hG).check (randomConditions V) ∧ x ∈ treeBody T :=
  mem_sep_iff

theorem randomFilter_subset (x : (levyContext κ hG).Model) :
    randomFilter hG x ⊆ (levyContext κ hG).check (randomConditions V) :=
  fun T hT ↦ ((mem_randomFilter_iff hG x T).mp hT).1

theorem check_mem_randomFilter_iff (x : (levyContext κ hG).Model) (T : V) :
    (levyContext κ hG).check T ∈ randomFilter hG x ↔ IsPositiveTree T ∧ x ∈ treeBody ((levyContext κ hG).check T) := by
  rw [mem_randomFilter_iff, (levyContext κ hG).check_mem_iff, mem_randomConditions_iff]

theorem check_pair_mem_inclusionOrder_iff (S : ForcingContext V) (P T T' : V) :
    ⟨S.check T, S.check T'⟩ₖ ∈ S.check (inclusionOrder P) ↔ T ∈ P ∧ T' ∈ P ∧ T ⊆ T' := by
  rw [← S.check_kpair, S.check_mem_iff, pair_mem_inclusionOrder]

include hAC in
/-- Intersections of ground positive trees containing a random real are positive. -/
theorem randomFilter_inter {x : (levyContext κ hG).Model} (hx : IsRandomOver hG x) {T T' : V}
    (hT : IsPositiveTree T) (hT' : IsPositiveTree T')
    (hxT : x ∈ treeBody ((levyContext κ hG).check T)) (hxT' : x ∈ treeBody ((levyContext κ hG).check T')) :
    IsPositiveTree (T ∩ T') := by
  let W := levyContext κ hG
  by_contra hnot
  obtain ⟨F, hF, henum⟩ := exists_code_of_not_positive hAC (tree_inter hT.1 hT'.1) hnot
  apply random_avoids_code hG hx hF
  intro m' hm'
  rw [← W.check_omega_eq] at hm'
  obtain ⟨m, hm, rfl⟩ := (W.mem_check_iff _ _).mp hm'
  obtain ⟨M, hM, hlev⟩ := henum m hm
  have hxTT : x ∈ treeBody (W.check (T ∩ T')) := by
    have h := W.checkEmbedding.map_inter T T'
    change W.check (T ∩ T') = W.check T ∩ W.check T' at h
    rw [h, treeBody_inter]
    exact mem_inter_iff.mpr ⟨hxT, hxT'⟩
  have hMω : W.check M ∈ (ω : W.Model) := by rw [← W.check_omega_eq]; exact (W.check_mem_iff _ _).mpr hM
  have hlevel := restrict_mem_levelSet hxTT hMω
  rw [← W.check_levelSet hM] at hlevel
  obtain ⟨s, hs, hxs⟩ := (W.mem_check_iff _ _).mp hlevel
  obtain ⟨i, hi, hFi⟩ := hlev s hs
  have hFmem := ((mem_nullCodes_iff F).mp hF).1
  have hFf : IsFunction F := IsFunction.of_mem hFmem
  have hFdom : domain F = (ω : V) := domain_eq_of_mem_function hFmem
  have hFm := function_value_mem hFmem hm
  have hFmf : IsFunction (F ‘ m) := IsFunction.of_mem hFm
  have hFmdom : domain (F ‘ m) = (ω : V) := domain_eq_of_mem_function hFm
  have hsf : IsFunction s := IsFunction.of_mem ((mem_levelSet_iff _ _ _).mp hs).2
  refine ⟨W.check i, by rw [← W.check_omega_eq]; exact (W.check_mem_iff _ _).mpr hi, ?_⟩
  rw [W.check_value (by rw [hFdom]; exact hm), W.check_value (by rw [hFmdom]; exact hi), hFi, W.check_domain,
    domain_eq_of_mem_function ((mem_levelSet_iff _ _ _).mp hs).2]
  exact hxs

include hAC in
theorem randomFilter_filter {x : (levyContext κ hG).Model} (hx : IsRandomOver hG x) :
    IsForcingFilter ((levyContext κ hG).check (randomConditions V))
      ((levyContext κ hG).check (inclusionOrder (randomConditions V))) (randomFilter hG x) := by
  let W := levyContext κ hG
  refine ⟨randomFilter_subset hG x, ⟨W.check (binarySequences V), ?_⟩, ?_, ?_⟩
  · refine (check_mem_randomFilter_iff hG x _).mpr ⟨fullTree_positive, ?_⟩
    rw [W.check_binarySequences]
    exact (mem_treeBody_iff _ _).mpr ⟨hx.1, fun n hn ↦ restrict_mem_binarySequences hx.1 hn⟩
  · intro T hT T' hT' hle
    obtain ⟨hTc, hxT⟩ := (mem_randomFilter_iff hG x T).mp hT
    obtain ⟨T₀, hT₀, rfl⟩ := (W.mem_check_iff _ _).mp hTc
    obtain ⟨T₀', hT₀', rfl⟩ := (W.mem_check_iff _ _).mp hT'
    obtain ⟨-, -, hsub⟩ := (check_pair_mem_inclusionOrder_iff W _ _ _).mp hle
    exact (mem_randomFilter_iff hG x _).mpr ⟨hT', treeBody_mono ((W.checkEmbedding.subset_iff _ _).mpr hsub) x hxT⟩
  · intro T hT T' hT'
    obtain ⟨hTc, hxT⟩ := (mem_randomFilter_iff hG x T).mp hT
    obtain ⟨hT'c, hxT'⟩ := (mem_randomFilter_iff hG x T').mp hT'
    obtain ⟨T₀, hT₀, rfl⟩ := (W.mem_check_iff _ _).mp hTc
    obtain ⟨T₀', hT₀', rfl⟩ := (W.mem_check_iff _ _).mp hT'c
    have hpos := randomFilter_inter hAC hG hx ((mem_randomConditions_iff _).mp hT₀)
      ((mem_randomConditions_iff _).mp hT₀') hxT hxT'
    have hinter : W.check (T₀ ∩ T₀') = W.check T₀ ∩ W.check T₀' := W.checkEmbedding.map_inter T₀ T₀'
    refine ⟨W.check (T₀ ∩ T₀'), (check_mem_randomFilter_iff hG x _).mpr ⟨hpos, ?_⟩, ?_, ?_⟩
    · rw [hinter, treeBody_inter]
      exact mem_inter_iff.mpr ⟨hxT, hxT'⟩
    · exact (check_pair_mem_inclusionOrder_iff W _ _ _).mpr
        ⟨(mem_randomConditions_iff _).mpr hpos, hT₀, fun z hz ↦ (mem_inter_iff.mp hz).1⟩
    · exact (check_pair_mem_inclusionOrder_iff W _ _ _).mpr
        ⟨(mem_randomConditions_iff _).mpr hpos, hT₀', fun z hz ↦ (mem_inter_iff.mp hz).2⟩

include hAC in
/-- A random real meets every ground dense set of random conditions. -/
theorem randomFilter_meets {x : (levyContext κ hG).Model} (hx : IsRandomOver hG x) {D : V}
    (hD : D ⊆ randomConditions V)
    (hdense : ForcingDense (randomConditions V) (inclusionOrder (randomConditions V)) D) :
    ∃ q ∈ D, (levyContext κ hG).check q ∈ randomFilter hG x := by
  let W := levyContext κ hG
  have hxc : x ∈ ((2 : ℕ) : W.Model) ^ (ω : W.Model) := (mem_cantorSpace_iff x).mp hx.1
  have hxf : IsFunction x := IsFunction.of_mem hxc
  obtain ⟨E, hE, hED, F, hF, c, hcert⟩ := exists_random_code hAC hD hdense
  have hEf : IsFunction E := IsFunction.of_mem hE
  have hEdom : domain E = (ω : V) := domain_eq_of_mem_function hE
  have hEpos : ∀ n ∈ (ω : V), IsPositiveTree (E ‘ n) := fun n hn ↦
    (mem_randomConditions_iff _).mp (function_value_mem hE hn)
  by_contra hcon
  have hnotin : ∀ n ∈ (ω : V), x ∉ treeBody (W.check (E ‘ n)) := fun n hn h ↦
    hcon ⟨E ‘ n, hED n hn, (check_mem_randomFilter_iff hG x _).mpr ⟨hEpos n hn, h⟩⟩
  apply random_avoids_code hG hx hF
  intro m' hm'
  rw [← W.check_omega_eq] at hm'
  obtain ⟨m, hm, rfl⟩ := (W.mem_check_iff _ _).mp hm'
  obtain ⟨hct, hFm⟩ := hcert m hm
  obtain ⟨q, hq⟩ : ∃ q : V, q = c ‘ (certSet E m) := ⟨_, rfl⟩
  rw [← hq] at hct hFm
  obtain ⟨Mseq, hMs⟩ : ∃ Ms : V, Ms = kpair.π₁ q := ⟨_, rfl⟩
  obtain ⟨M, hMd⟩ : ∃ M : V, M = kpair.π₁ (kpair.π₂ q) := ⟨_, rfl⟩
  obtain ⟨f, hfd⟩ : ∃ f : V, f = kpair.π₂ (kpair.π₂ q) := ⟨_, rfl⟩
  unfold CertTriple at hct
  rw [← hMs, ← hMd, ← hfd] at hct
  rw [← hfd] at hFm
  obtain ⟨hMseq, hM, hf, -, hleave, hlevel⟩ := hct
  have hMseqω : ∀ n ∈ (ω : V), Mseq ‘ n ∈ (ω : V) := fun n hn ↦ function_value_mem hMseq hn
  have hFmem := ((mem_nullCodes_iff F).mp hF).1
  have hFdom : domain F = (ω : V) := domain_eq_of_mem_function hFmem
  have hFf : IsFunction F := IsFunction.of_mem hFmem
  have hff : IsFunction f := IsFunction.of_mem hf
  have hfdom : domain f = (ω : V) := domain_eq_of_mem_function hf
  have hcheckω : ∀ n ∈ (ω : V), W.check n ∈ (ω : W.Model) := fun n hn ↦ by
    rw [← W.check_omega_eq]; exact (W.check_mem_iff _ _).mpr hn
  have hrestr : ∀ n ∈ (ω : V), x ↾ (W.check n) ∈ W.check (binarySequences V) := fun n hn ↦ by
    rw [W.check_binarySequences]; exact restrict_mem_binarySequences hx.1 (hcheckω n hn)
  have hrestrdom : ∀ n ∈ (ω : V), ∀ s : V, x ↾ (W.check n) = W.check s → domain s = n := by
    intro n hn s hs
    have h1 : domain (x ↾ (W.check n)) = W.check n :=
      domain_eq_of_mem_function (function_restrict_mem hxc (IsTransitive.ω.transitive _ (hcheckω n hn)))
    rw [hs] at h1
    have hsf : IsFunction s := IsFunction.of_mem ((mem_finiteSequences_iff_domain _ _).mp
      ((W.check_mem_iff _ _).mp (by rw [← hs]; exact hrestr n hn))).2
    rw [W.check_domain] at h1
    exact (W.check_eq_iff _ _).mp h1
  have key : ∃ s ∈ binarySequences V, (∃ i ∈ (ω : V), f ‘ i = s) ∧ x ↾ (W.check (domain s)) = W.check s := by
    by_cases hA : ∃ n ∈ (ω : V), x ↾ (W.check (Mseq ‘ n)) ∈ W.check (E ‘ n)
    · obtain ⟨n, hn, hxn⟩ := hA
      have hxnot := hnotin n hn
      rw [mem_treeBody_iff] at hxnot
      push Not at hxnot
      obtain ⟨M', hM', hxM'⟩ := hxnot hx.1
      rw [← W.check_omega_eq] at hM'
      obtain ⟨M'₀, hM'₀, rfl⟩ := (W.mem_check_iff _ _).mp hM'
      have hMn : Mseq ‘ n ∈ (ω : V) := hMseqω n hn
      have : IsOrdinal (Mseq ‘ n) := IsOrdinal.nat hMn
      have : IsOrdinal M'₀ := IsOrdinal.nat hM'₀
      have hsub : Mseq ‘ n ⊆ M'₀ := by
        rcases IsOrdinal.subset_or_supset (α := Mseq ‘ n) (β := M'₀) with h | h
        · exact h
        · exfalso
          apply hxM'
          have htree := W.check_isTree (hEpos n hn).1
          have hsub' : W.check M'₀ ⊆ W.check (Mseq ‘ n) := (W.checkEmbedding.subset_iff _ _).mpr h
          rw [← restrict_restrict_of_subset hsub']
          exact tree_restrict_mem htree hxn (hcheckω M'₀ hM'₀) (by
            rw [domain_eq_of_mem_function (function_restrict_mem hxc (IsTransitive.ω.transitive _ (hcheckω _ hMn)))]
            exact (W.checkEmbedding.subset_iff _ _).mpr h)
      obtain ⟨s, hsB, hxs⟩ := (W.mem_check_iff _ _).mp (hrestr M'₀ hM'₀)
      have hsdom : domain s = M'₀ := hrestrdom M'₀ hM'₀ s hxs
      have hleaves : LeavesTree (E ‘ n) (Mseq ‘ n) s := by
        refine ⟨by rw [hsdom]; exact hsub, fun hsE ↦ hxM' (by rw [hxs]; exact (W.check_mem_iff _ _).mpr hsE), ?_⟩
        have hsub' : W.check (Mseq ‘ n) ⊆ W.check M'₀ := (W.checkEmbedding.subset_iff _ _).mpr hsub
        have : W.check (s ↾ (Mseq ‘ n)) ∈ W.check (E ‘ n) := by
          rw [W.check_restrict, ← hxs, restrict_restrict_of_subset hsub']
          exact hxn
        exact (W.check_mem_iff _ _).mp this
      obtain ⟨i, hi, hfi⟩ := hleave n hn s hsB hleaves
      exact ⟨s, hsB, ⟨i, hi, hfi⟩, by rw [hsdom]; exact hxs⟩
    · push Not at hA
      obtain ⟨s, hsB, hxs⟩ := (W.mem_check_iff _ _).mp (hrestr M hM)
      have hsdom : domain s = M := hrestrdom M hM s hxs
      have hs2 : s ∈ ((2 : ℕ) : V) ^ M := by
        have := ((mem_finiteSequences_iff_domain _ _).mp hsB).2
        rw [hsdom] at this
        exact this
      have hsK : s ∈ levelSet (avoidTree E Mseq) M := by
        refine (mem_levelSet_iff _ _ _).mpr ⟨(mem_avoidTree_iff _ _ _).mpr ⟨hsB, fun n hn hMn ↦ ?_⟩, hs2⟩
        rw [hsdom] at hMn
        intro hsE
        apply hA n hn
        have hsub' : W.check (Mseq ‘ n) ⊆ W.check M := (W.checkEmbedding.subset_iff _ _).mpr hMn
        have : W.check (s ↾ (Mseq ‘ n)) ∈ W.check (E ‘ n) := (W.check_mem_iff _ _).mpr hsE
        rw [W.check_restrict, ← hxs, restrict_restrict_of_subset hsub'] at this
        exact this
      obtain ⟨i, hi, hfi⟩ := hlevel s hsK
      exact ⟨s, hsB, ⟨i, hi, hfi⟩, by rw [hsdom]; exact hxs⟩
  obtain ⟨s, hsB, ⟨i, hi, hfi⟩, hxs⟩ := key
  have hsf : IsFunction s := IsFunction.of_mem ((mem_finiteSequences_iff_domain _ _).mp hsB).2
  refine ⟨W.check i, hcheckω i hi, ?_⟩
  rw [W.check_value (by rw [hFdom]; exact hm), hFm, W.check_value (by rw [hfdom]; exact hi), hfi, W.check_domain]
  exact hxs

include hAC hU hc hω hκ in
theorem randomFilter_localized (x : (levyContext κ hG).Model) : IsLocalized hG (randomFilter hG x) := by
  obtain ⟨ν, hν, hsmall⟩ := randomConditions_small hAC hU hc hω
  exact levy_subset_check_localized hAC hU hc hω hκ hG hsmall hν _ (randomFilter_subset hG x)

end

end ZFVP
