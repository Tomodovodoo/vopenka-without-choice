import ZFVP.SetTheory.WoodinSupercompact
import ZFVP.ModelTheory.RelativeSigmaCorrectness
import ZFVP.ModelTheory.DeltaOneMembershipEmbedding
import ZFVP.ModelTheory.TransitiveZFValues
import ZFVP.SetTheory.CodingUniverse

/-! Downward absoluteness of the small-embedding witness predicate to a transitive model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem relativeSigmaCorrect_one_of_cn {M γ : V} [IsTransitive M] (hM : IsSequenceSupport M)
    (hsub : hierarchy γ ⊆ M) (h : Cn 1 γ) : RelativeSigmaCorrect 1 (hierarchy γ) M := by
  let := h.ordinal
  let := hierarchy_transitive γ
  have hs : IsSequenceSupport (hierarchy γ) := h.2.support
  have hAne : IsNonempty (hierarchy γ) := ⟨ω, hs.omega_mem⟩
  have hBne : IsNonempty M := ⟨ω, hM.omega_mem⟩
  intro n φ hφ b hb
  constructor
  · intro hsat
    exact membershipSatisfies_sigmaOne_upward hφ hAne hBne hsub hb hsat
  · intro hsat
    exact (h.2 n φ hφ b hb).mp ⟨M, hM, mem_function_of_mem_function_of_subset hb hsub, hsat⟩

theorem Cn.one_downward {M : V} [IsTransitive M] [Nonempty (SetDomain M)]
    [(SetDomain M)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (γ : SetDomain M) (hsub : hierarchy γ.val ⊆ M)
    (h : Cn 1 γ.val) : Cn 1 γ :=
  (TransitiveZF.cn_iff_relative M 0 γ h.ordinal hsub).mpr
    (relativeSigmaCorrect_one_of_cn (TransitiveZF.sequenceSupport M) hsub h)

section Transfer

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem TransitiveZF.boundedCode_iff (n φ : SetDomain U) :
    IsBoundedFormulaCode n φ ↔ IsBoundedFormulaCode n.val φ.val :=
  TransitiveZF.levyCode_iff U .sigma 0 n φ

theorem TransitiveZF.boundedTruth_iff {n φ b : SetDomain U} (hφ : IsBoundedFormulaCode n φ)
    [IsFunction b] (hd : domain b = n) :
    BoundedTruth n φ b ↔ BoundedTruth n.val φ.val b.val := by
  set A : SetDomain U := boundedTruthDomain b with hA
  have hbA : b ∈ A ^ n := assignment_mem_boundedTruthDomain hd
  have hAt : IsTransitive A.val := TransitiveZF.transitive_val U A inferInstance
  let := hAt
  have hAne : IsNonempty A.val := by
    obtain ⟨x, hx⟩ := (boundedTruthDomain_nonempty b).nonempty
    exact ⟨x.val, hx⟩
  have hbAV : b.val ∈ A.val ^ n.val := (TransitiveZF.function_iff U b n A).mp hbA
  have hφV : IsBoundedFormulaCode n.val φ.val := (TransitiveZF.boundedCode_iff U n φ).mp hφ
  exact (boundedTruth_iff_membershipSatisfies hφ (boundedTruthDomain_nonempty b) hbA).trans
    ((TransitiveZF.satisfies_iff U A n φ b).trans
      (boundedTruth_iff_membershipSatisfies hφV hAne hbAV).symm)

theorem TransitiveZF.rankFunctionClosed_iff {α b : SetDomain U} (hα : IsOrdinal α.val)
    (hsub : hierarchy α.val ⊆ U) (hclos : b.val ^ hierarchy α.val ⊆ U) :
    IsRankFunctionClosed α b ↔ IsRankFunctionClosed α.val b.val := by
  have hα' : IsOrdinal α := (TransitiveZF.ordinal_iff U α).mpr hα
  have hh : (hierarchy α : SetDomain U).val = hierarchy α.val :=
    TransitiveZF.hierarchy_val U α hα' hsub
  constructor
  · intro h f hf
    have hfU : f ∈ U := hclos f hf
    have : (⟨f, hfU⟩ : SetDomain U) ∈ b ^ hierarchy α :=
      (TransitiveZF.function_iff U ⟨f, hfU⟩ (hierarchy α) b).mpr (by rw [hh]; exact hf)
    exact h _ this
  · intro h f hf
    exact h f.val ((hh ▸ (TransitiveZF.function_iff U f (hierarchy α) b).mp hf))

theorem TransitiveZF.starReflectionWitness_iff {α a b φ : SetDomain U} (hα : IsOrdinal α.val)
    (hsub : hierarchy α.val ⊆ U) (hclos : b.val ^ hierarchy α.val ⊆ U)
    (hφ : IsBoundedFormulaCode (2 : SetDomain U) φ) :
    StarReflectionWitness α φ a b ↔ StarReflectionWitness α.val φ.val a.val b.val := by
  have hnum : (2 : SetDomain U).val = (2 : V) := by
    simpa using TransitiveZF.numeral_val U 2
  have htup : (standardTuple ![a, b] : SetDomain U).val = standardTuple ![a.val, b.val] := by
    rw [TransitiveZF.standardTuple_val U ![a, b]]
    congr 1
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  have hbt := TransitiveZF.boundedTruth_iff U (n := (2 : SetDomain U)) (φ := φ)
    (b := standardTuple ![a, b]) hφ (by simp)
  rw [htup, hnum] at hbt
  exact and_congr (TransitiveZF.rankFunctionClosed_iff U hα hsub hclos) hbt

end Transfer

/-- Sigma-one-star correctness passes down to a transitive model of ZF that holds the stage
`hierarchy γ` and is closed under the function spaces used by the reflection clause. -/
theorem IsSigmaOneStarCorrect.downward {M : V} [IsTransitive M] [Nonempty (SetDomain M)]
    [(SetDomain M)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (γ : SetDomain M) (hsub : hierarchy γ.val ⊆ M)
    (hfun : ∀ x ∈ M, ∀ y ∈ M, y ^ x ⊆ M) (h : IsSigmaOneStarCorrect γ.val) :
    IsSigmaOneStarCorrect γ := by
  have hord : IsOrdinal γ.val := h.1.ordinal
  let := hord
  have hord' : IsOrdinal γ := (TransitiveZF.ordinal_iff M γ).mpr hord
  have hh : (hierarchy γ : SetDomain M).val = hierarchy γ.val :=
    TransitiveZF.hierarchy_val M γ hord' hsub
  have hnum : (2 : SetDomain M).val = (2 : V) := by
    simpa using TransitiveZF.numeral_val M 2
  refine ⟨Cn.one_downward γ hsub h.1, ?_⟩
  intro α hα a ha φ hφ hex
  have hαγ : α.val ∈ γ.val := hα
  have hαord : IsOrdinal α.val := IsOrdinal.of_mem hαγ
  let := hαord
  have hαsubγ : hierarchy α.val ⊆ hierarchy γ.val :=
    hierarchy_mono (IsOrdinal.toIsTransitive.transitive α.val hαγ)
  have hαsub : hierarchy α.val ⊆ M := fun x hx ↦ hsub x (hαsubγ x hx)
  have hhα : (hierarchy α : SetDomain M).val = hierarchy α.val :=
    TransitiveZF.hierarchy_val M α ((TransitiveZF.ordinal_iff M α).mpr hαord) hαsub
  have hVαM : hierarchy α.val ∈ M := hhα ▸ (hierarchy α : SetDomain M).property
  have hclos : ∀ b : SetDomain M, b.val ^ hierarchy α.val ⊆ M :=
    fun b ↦ hfun _ hVαM _ b.property
  have hφV : IsBoundedFormulaCode (2 : V) φ.val := by
    have := (TransitiveZF.boundedCode_iff M 2 φ).mp hφ
    rwa [hnum] at this
  have haV : a.val ∈ hierarchy γ.val := hh ▸ ha
  have hexV : ∃ b : V, StarReflectionWitness α.val φ.val a.val b := by
    obtain ⟨b, hb⟩ := hex
    exact ⟨b.val,
      (TransitiveZF.starReflectionWitness_iff M hαord hαsub (hclos b) hφ).mp hb⟩
  obtain ⟨b₀, hb₀, hW⟩ := h.2 α.val hαγ a.val haV φ.val hφV hexV
  refine ⟨⟨b₀, hsub b₀ hb₀⟩, ?_, ?_⟩
  · show b₀ ∈ (hierarchy γ : SetDomain M).val
    rw [hh]
    exact hb₀
  · exact (TransitiveZF.starReflectionWitness_iff M hαord hαsub
      (hclos ⟨b₀, hsub b₀ hb₀⟩) hφ).mpr hW

/-- The same statement in the form the relativization machinery uses. -/
theorem IsSigmaOneStarCorrect.downward_evalb {M : V} [IsTransitive M] [Nonempty (SetDomain M)]
    [(SetDomain M)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (γ : SetDomain M) (hsub : hierarchy γ.val ⊆ M)
    (hfun : ∀ x ∈ M, ∀ y ∈ M, y ^ x ⊆ M) (h : IsSigmaOneStarCorrect γ.val) :
    sigmaOneStarCorrectFormula.Evalb ![γ] :=
  (Defined.eval_iff (R := fun v : Fin 1 → SetDomain M ↦ IsSigmaOneStarCorrect (v 0)) ![γ]).mpr
    (IsSigmaOneStarCorrect.downward γ hsub hfun h)

theorem function_subset_hierarchy_support {θ : V} [IsOrdinal θ] (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ) :
    ∀ x ∈ hierarchy θ, ∀ y ∈ hierarchy θ, y ^ x ⊆ hierarchy θ := by
  intro x hx y hy
  exact (hierarchy_transitive θ).transitive _ (function_mem_hierarchy_limit hsucc hx hy)

section SupportStage

variable {θ : V} [IsOrdinal θ] [Nonempty (SetDomain (hierarchy θ))]
  [(SetDomain (hierarchy θ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Sigma-one-star correctness passes down to a rank stage closed under successor. -/
theorem IsSigmaOneStarCorrect.downward_support (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (γ : SetDomain (hierarchy θ)) (hγθ : γ.val ∈ θ) (h : IsSigmaOneStarCorrect γ.val) :
    IsSigmaOneStarCorrect γ := by
  let := hierarchy_transitive θ
  let := IsOrdinal.of_mem hγθ
  exact IsSigmaOneStarCorrect.downward γ
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive γ.val hγθ))
    (function_subset_hierarchy_support hsucc) h

/-- Every clause of the small-embedding witness passes down to a rank stage closed under
successor that holds `V_{γ+2}`. -/
theorem WoodinSupercompactWitness.downward_support (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (κ γ a : SetDomain (hierarchy θ)) (hγθ : succ (succ γ.val) ∈ θ)
    (hκγ : κ.val ∈ γ.val) (h : WoodinSupercompactWitness κ.val γ.val a.val) :
    WoodinSupercompactWitness κ γ a := by
  let := hierarchy_transitive θ
  obtain ⟨hγord, δ, hδκ, hδstar, x, hx, e, he, c, hc, hecκ, hexa⟩ := h
  let := hγord
  have hsγθ : succ γ.val ∈ θ :=
    IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (succ γ.val)) hγθ
  have hγ'θ : γ.val ∈ θ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self γ.val) hsγθ
  have hκθ : κ.val ∈ θ := IsOrdinal.toIsTransitive.mem_trans hκγ hγ'θ
  have hδθ : δ ∈ θ := IsOrdinal.toIsTransitive.mem_trans hδκ hκθ
  have hsδθ : succ δ ∈ θ := hsucc δ hδθ
  let := IsOrdinal.of_mem hδθ
  -- the source and target stages of the embedding sit inside the rank stage
  have hAθ : hierarchy (succ δ) ∈ hierarchy θ := hierarchy_mem hsδθ
  have hBθ : hierarchy (succ γ.val) ∈ hierarchy θ := hierarchy_mem hsγθ
  have hδM : δ ∈ hierarchy θ := ordinal_subset_hierarchy θ δ hδθ
  have hxM : x ∈ hierarchy θ :=
    (hierarchy_transitive θ).transitive _ (hierarchy_mem hδθ) x hx
  have heM : e ∈ hierarchy θ :=
    function_subset_hierarchy_support hsucc _ hAθ _ hBθ e he.function
  have hcM : c ∈ hierarchy θ :=
    (hierarchy_transitive θ).transitive _ hAθ c hc.mem_domain
  set δ' : SetDomain (hierarchy θ) := ⟨δ, hδM⟩ with hδ'
  set x' : SetDomain (hierarchy θ) := ⟨x, hxM⟩ with hx'
  set e' : SetDomain (hierarchy θ) := ⟨e, heM⟩ with he'
  set c' : SetDomain (hierarchy θ) := ⟨c, hcM⟩ with hc'
  -- the stage computes the rank hierarchy correctly at the relevant ordinals
  have hsucδ : (succ δ' : SetDomain (hierarchy θ)).val = succ δ :=
    TransitiveZF.succ_val (hierarchy θ) δ'
  have hsucγ : (succ γ : SetDomain (hierarchy θ)).val = succ γ.val :=
    TransitiveZF.succ_val (hierarchy θ) γ
  have hordsδ : IsOrdinal (succ δ' : SetDomain (hierarchy θ)) :=
    (TransitiveZF.ordinal_iff (hierarchy θ) (succ δ')).mpr
      (hsucδ ▸ (show IsOrdinal (succ δ) from inferInstance))
  have hordsγ : IsOrdinal (succ γ : SetDomain (hierarchy θ)) :=
    (TransitiveZF.ordinal_iff (hierarchy θ) (succ γ)).mpr
      (hsucγ ▸ (show IsOrdinal (succ γ.val) from inferInstance))
  have hhδ : (hierarchy δ' : SetDomain (hierarchy θ)).val = hierarchy δ :=
    TransitiveZF.hierarchy_val (hierarchy θ) δ'
      ((TransitiveZF.ordinal_iff (hierarchy θ) δ').mpr inferInstance)
      ((hierarchy_transitive θ).transitive _ (hierarchy_mem hδθ))
  have hhA : (hierarchy (succ δ') : SetDomain (hierarchy θ)).val = hierarchy (succ δ) := by
    rw [TransitiveZF.hierarchy_val (hierarchy θ) (succ δ') hordsδ
      (by rw [hsucδ]; exact (hierarchy_transitive θ).transitive _ hAθ), hsucδ]
  have hhB : (hierarchy (succ γ) : SetDomain (hierarchy θ)).val = hierarchy (succ γ.val) := by
    rw [TransitiveZF.hierarchy_val (hierarchy θ) (succ γ) hordsγ
      (by rw [hsucγ]; exact (hierarchy_transitive θ).transitive _ hBθ), hsucγ]
  -- transfer the embedding, the critical point and the two value equations
  have hemb : IsCodedMembershipEmbedding
      (hierarchy (succ δ') : SetDomain (hierarchy θ)) (hierarchy (succ γ)) e' :=
    TransitiveZF.embedding_of_embedding (hierarchy θ) _ _ e' (by rw [hhA, hhB]; exact he)
  have hfun : e' ∈ (hierarchy (succ γ) : SetDomain (hierarchy θ)) ^ (hierarchy (succ δ')) :=
    (TransitiveZF.function_iff (hierarchy θ) e' (hierarchy (succ δ')) (hierarchy (succ γ))).mpr
      (by rw [hhA, hhB]; exact he.function)
  have hAt : IsTransitive (hierarchy (succ δ') : SetDomain (hierarchy θ)) :=
    hierarchy_transitive _
  let := hAt
  have hAtv : IsTransitive (hierarchy (succ δ') : SetDomain (hierarchy θ)).val := by
    rw [hhA]; exact hierarchy_transitive _
  let := hAtv
  have hcrit : IsCriticalPoint (hierarchy (succ δ') : SetDomain (hierarchy θ)) e' c' :=
    (TransitiveZF.criticalPoint_iff (hierarchy θ) _ (hierarchy (succ γ)) e' c' hfun).mpr
      (by rw [hhA]; exact hc)
  refine ⟨(TransitiveZF.ordinal_iff (hierarchy θ) γ).mpr hγord, δ', hδκ,
    IsSigmaOneStarCorrect.downward_support hsucc δ' hδθ hδstar, x', ?_, e', hemb, c', hcrit,
    ?_, ?_⟩
  · show x ∈ (hierarchy δ' : SetDomain (hierarchy θ)).val
    rw [hhδ]
    exact hx
  · exact Subtype.ext ((TransitiveZF.value_val_total (hierarchy θ) e' c').trans hecκ)
  · exact Subtype.ext ((TransitiveZF.value_val_total (hierarchy θ) e' x').trans hexa)

/-- The witness clause in the form the relativization machinery uses. -/
theorem WoodinSupercompactWitness.downward_support_evalb (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (κ γ a : SetDomain (hierarchy θ)) (hγθ : succ (succ γ.val) ∈ θ)
    (hκγ : κ.val ∈ γ.val) (h : WoodinSupercompactWitness κ.val γ.val a.val) :
    woodinSupercompactWitnessFormula.Evalb ![κ, γ, a] :=
  (Defined.eval_iff
      (R := fun v : Fin 3 → SetDomain (hierarchy θ) ↦
        WoodinSupercompactWitness (v 0) (v 1) (v 2)) ![κ, γ, a]).mpr
    (WoodinSupercompactWitness.downward_support hsucc κ γ a hγθ hκγ h)

end SupportStage

end ZFVP
