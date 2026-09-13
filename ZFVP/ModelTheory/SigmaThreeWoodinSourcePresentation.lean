import ZFVP.ModelTheory.DeltaOneWoodinSourceCode
import ZFVP.ModelTheory.SigmaThreeWoodinPrefixes

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def sigmaThreeWoodinSourceCardinalsFormula : SetTheorySemisentence 3 :=
  “z θ K. ∃ κ, !sigmaThreeWoodinSeedCardinalFormula κ ∧ !sigmaOneWoodinInsertSeedFormula z θ K κ”

def piThreeWoodinSourceCardinalsFormula : SetTheorySemisentence 3 :=
  “z θ K. !IsOrdinal.dfn θ ∧ ∀ w, !sigmaThreeWoodinSourceCardinalsFormula w θ K → z = w”

theorem sigmaThreeWoodinSourceCardinalsFormula_sigmaThree : IsSigmaFormula 3 sigmaThreeWoodinSourceCardinalsFormula :=
  .exs (.and (sigmaThreeWoodinSeedCardinalFormula_sigmaThree.subst _)
    ((sigmaOneWoodinInsertSeedFormula_sigmaOne.mono (by omega)).subst _))

theorem piThreeWoodinSourceCardinalsFormula_piThree : IsPiFormula 3 piThreeWoodinSourceCardinalsFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.or (sigmaThreeWoodinSourceCardinalsFormula_sigmaThree.subst _).neg (.bounded (.rel _ _))))

def woodinSourcePrefixCodeCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z θ. ∃ s, !Λ s θ ∧ !sigmaOneWoodinSourceCodeFormula z θ s”

def woodinSourcePrefixCardinalsCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z θ. ∃ K, !Λ K θ ∧ !sigmaThreeWoodinSourceCardinalsFormula z θ K”

def woodinSourceCompletedCodeCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z θ. ∃ r, !Λ r θ ∧ ∃ s, !sigmaOnePairFirstFormula s r ∧
    ∃ η, !boundedSuccFormula η θ ∧ !sigmaOneWoodinSourceCodeFormula z η s”

def woodinSourceCompletedCardinalsCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z θ. ∃ r, !Λ r θ ∧ ∃ K, !sigmaOnePairSecondFormula K r ∧
    ∃ η, !boundedSuccFormula η θ ∧ !sigmaThreeWoodinSourceCardinalsFormula z η K”

theorem woodinSourcePrefixCodeCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinSourcePrefixCodeCertificate Λ) :=
  .exs (.and (hΛ.subst _) ((sigmaOneWoodinSourceCodeFormula_sigmaOne.mono (by omega)).subst _))

theorem woodinSourcePrefixCardinalsCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinSourcePrefixCardinalsCertificate Λ) :=
  .exs (.and (hΛ.subst _) (sigmaThreeWoodinSourceCardinalsFormula_sigmaThree.subst _))

theorem woodinSourceCompletedCodeCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinSourceCompletedCodeCertificate Λ) :=
  .exs (.and (hΛ.subst _) (.exs (.and ((sigmaOnePairFirstFormula_sigmaOne.mono (by omega)).subst _)
    (.exs (.and (.bounded (boundedSuccFormula_bounded.subst _))
      ((sigmaOneWoodinSourceCodeFormula_sigmaOne.mono (by omega)).subst _))))))

theorem woodinSourceCompletedCardinalsCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinSourceCompletedCardinalsCertificate Λ) :=
  .exs (.and (hΛ.subst _) (.exs (.and ((sigmaOnePairSecondFormula_sigmaOne.mono (by omega)).subst _)
    (.exs (.and (.bounded (boundedSuccFormula_bounded.subst _))
      (sigmaThreeWoodinSourceCardinalsFormula_sigmaThree.subst _))))))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaThreeWoodinSourceCardinalsFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun z θ K ↦ IsOrdinal θ ∧ z = woodinSourceCardinals θ K)
      via sigmaThreeWoodinSourceCardinalsFormula :=
  ⟨fun v ↦ by simp [sigmaThreeWoodinSourceCardinalsFormula, woodinSourceCardinals]⟩

instance piThreeWoodinSourceCardinalsFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun z θ K ↦ IsOrdinal θ ∧ z = woodinSourceCardinals θ K)
      via piThreeWoodinSourceCardinalsFormula :=
  ⟨fun v ↦ by simp [piThreeWoodinSourceCardinalsFormula]; exact fun h ↦ Or.inl h⟩

theorem eval_woodinSourcePrefixCodeCertificate (Λ : SetTheorySemisentence 2) (z θ : V) [IsOrdinal θ]
    (he : ∀ s : V, Λ.Evalb ![s, θ] ↔ s = woodinIterationPrefix θ) :
    (woodinSourcePrefixCodeCertificate Λ).Evalb ![z, θ] ↔
      z = woodinSourceCode θ (woodinIterationPrefix θ) := by
  simp only [Semiformula.Evalb] at he
  simp [woodinSourcePrefixCodeCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, show IsOrdinal θ from inferInstance]

theorem eval_woodinSourcePrefixCardinalsCertificate (Λ : SetTheorySemisentence 2) (z θ : V) [IsOrdinal θ]
    (he : ∀ K : V, Λ.Evalb ![K, θ] ↔ K = woodinIterationCardinalPrefix θ) :
    (woodinSourcePrefixCardinalsCertificate Λ).Evalb ![z, θ] ↔
      z = woodinSourceCardinals θ (woodinIterationCardinalPrefix θ) := by
  simp only [Semiformula.Evalb] at he
  simp [woodinSourcePrefixCardinalsCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, show IsOrdinal θ from inferInstance]

theorem eval_woodinSourceCompletedCodeCertificate (Λ : SetTheorySemisentence 2) (z θ : V) [IsOrdinal θ]
    (he : ∀ r : V, Λ.Evalb ![r, θ] ↔ r = woodinIterationRec θ) :
    (woodinSourceCompletedCodeCertificate Λ).Evalb ![z, θ] ↔
      z = woodinSourceCode (succ θ) (kpair.π₁ (woodinIterationRec θ)) := by
  simp only [Semiformula.Evalb] at he
  simp [woodinSourceCompletedCodeCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, show IsOrdinal (succ θ) from inferInstance]

theorem eval_woodinSourceCompletedCardinalsCertificate (Λ : SetTheorySemisentence 2) (z θ : V) [IsOrdinal θ]
    (he : ∀ r : V, Λ.Evalb ![r, θ] ↔ r = woodinIterationRec θ) :
    (woodinSourceCompletedCardinalsCertificate Λ).Evalb ![z, θ] ↔
      z = woodinSourceCardinals (succ θ) (kpair.π₂ (woodinIterationRec θ)) := by
  simp only [Semiformula.Evalb] at he
  simp [woodinSourceCompletedCardinalsCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, show IsOrdinal (succ θ) from inferInstance]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_woodinOutputPiCertificate (Λ : SetTheorySemisentence 2) (z θ a : V)
    (he : ∀ w : V, Λ.Evalb ![w, θ] ↔ w = a) :
    (woodinRecursionStepPiCertificate Λ).Evalb ![z, θ] ↔ z = a := by
  simp only [Semiformula.Evalb] at he
  simp [woodinRecursionStepPiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

/-- Uniform graphs for both source prefixes and completed source stages, with the
seed included in all forcing and cardinal tables. -/
theorem woodinSourcePresentation_deltaThree_uniform :
    ∃ σ π σK πK σC πC σL πL : SetTheorySemisentence 2,
      IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧ IsSigmaFormula 3 σK ∧ IsPiFormula 3 πK ∧
      IsSigmaFormula 3 σC ∧ IsPiFormula 3 πC ∧ IsSigmaFormula 3 σL ∧ IsPiFormula 3 πL ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ θ : V,
        IsWoodinSupercompact δ → θ ∈ δ → ∀ z,
          (σ.Evalb ![z, θ] ↔ z = woodinSourceCode θ (woodinIterationPrefix θ)) ∧
          (π.Evalb ![z, θ] ↔ z = woodinSourceCode θ (woodinIterationPrefix θ)) ∧
          (σK.Evalb ![z, θ] ↔ z = woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) ∧
          (πK.Evalb ![z, θ] ↔ z = woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) ∧
          (σC.Evalb ![z, θ] ↔ z = woodinSourceCode (succ θ) (kpair.π₁ (woodinIterationRec θ))) ∧
          (πC.Evalb ![z, θ] ↔ z = woodinSourceCode (succ θ) (kpair.π₁ (woodinIterationRec θ))) ∧
          (σL.Evalb ![z, θ] ↔ z = woodinSourceCardinals (succ θ) (kpair.π₂ (woodinIterationRec θ))) ∧
          (πL.Evalb ![z, θ] ↔ z = woodinSourceCardinals (succ θ) (kpair.π₂ (woodinIterationRec θ))) := by
  obtain ⟨A, _, B, _, hA, _, hB, _, heAB⟩ := woodinIterationPrefixes_deltaThree_uniform.{u}
  obtain ⟨R, _, _, _, hR, _, _, _, heR⟩ := woodinRecursion_deltaThree_uniform.{u}
  let σ := woodinSourcePrefixCodeCertificate A
  let σK := woodinSourcePrefixCardinalsCertificate B
  let σC := woodinSourceCompletedCodeCertificate R
  let σL := woodinSourceCompletedCardinalsCertificate R
  have hσ := woodinSourcePrefixCodeCertificate_sigmaThree hA
  have hσK := woodinSourcePrefixCardinalsCertificate_sigmaThree hB
  have hσC := woodinSourceCompletedCodeCertificate_sigmaThree hR
  have hσL := woodinSourceCompletedCardinalsCertificate_sigmaThree hR
  refine ⟨σ, woodinRecursionStepPiCertificate σ, σK, woodinRecursionStepPiCertificate σK,
    σC, woodinRecursionStepPiCertificate σC, σL, woodinRecursionStepPiCertificate σL,
    hσ, woodinRecursionStepPiCertificate_piThree hσ, hσK, woodinRecursionStepPiCertificate_piThree hσK,
    hσC, woodinRecursionStepPiCertificate_piThree hσC, hσL, woodinRecursionStepPiCertificate_piThree hσL, ?_⟩
  intro V _ _ _ δ θ hδ hθ z
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hp := fun w ↦ eval_woodinSourcePrefixCodeCertificate A w θ (fun s ↦ (heAB V δ θ hδ hθ s).1)
  have hk := fun w ↦ eval_woodinSourcePrefixCardinalsCertificate B w θ (fun K ↦ (heAB V δ θ hδ hθ K).2.2.1)
  have hc := fun w ↦ eval_woodinSourceCompletedCodeCertificate R w θ (fun r ↦ (heR V δ θ hδ hθ r).1)
  have hl := fun w ↦ eval_woodinSourceCompletedCardinalsCertificate R w θ (fun r ↦ (heR V δ θ hδ hθ r).1)
  exact ⟨hp z, eval_woodinOutputPiCertificate σ z θ _ hp,
    hk z, eval_woodinOutputPiCertificate σK z θ _ hk,
    hc z, eval_woodinOutputPiCertificate σC z θ _ hc,
    hl z, eval_woodinOutputPiCertificate σL z θ _ hl⟩

def woodinSourceDecodedCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z β. ∃ θ, !sigmaOneWoodinRecursiveIndexFormula θ β ∧ !Λ z θ”

theorem woodinSourceDecodedCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinSourceDecodedCertificate Λ) :=
  .exs (.and ((sigmaOneWoodinRecursiveIndexFormula_sigmaOne.mono (by omega)).subst _) (hΛ.subst _))

theorem eval_woodinSourceDecodedCertificate (Λ : SetTheorySemisentence 2) (z β a : V)
    (he : Λ.Evalb ![z, woodinRecursiveIndex β] ↔ z = a) :
    (woodinSourceDecodedCertificate Λ).Evalb ![z, β] ↔ z = a := by
  simpa [woodinSourceDecodedCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def] using he

theorem woodinRecursiveIndex_subset (β : V) [IsOrdinal β] : woodinRecursiveIndex β ⊆ β := by
  classical
  unfold woodinRecursiveIndex
  split
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    exact IsOrdinal.toIsTransitive.mem_trans hxy hy
  · exact subset_refl _

/-- Uniform Delta-three prefix graphs with the positive source length as argument. -/
theorem woodinSourceDecodedPrefixes_deltaThree_uniform :
    ∃ σ π σK πK : SetTheorySemisentence 2,
      IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧ IsSigmaFormula 3 σK ∧ IsPiFormula 3 πK ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ β : V,
        IsWoodinSupercompact δ → β ∈ δ → β ≠ ∅ →
        woodinSourceIndex (woodinRecursiveIndex β) = β ∧ ∀ z,
          (σ.Evalb ![z, β] ↔ z = woodinSourceCode (woodinRecursiveIndex β)
            (woodinIterationPrefix (woodinRecursiveIndex β))) ∧
          (π.Evalb ![z, β] ↔ z = woodinSourceCode (woodinRecursiveIndex β)
            (woodinIterationPrefix (woodinRecursiveIndex β))) ∧
          (σK.Evalb ![z, β] ↔ z = woodinSourceCardinals (woodinRecursiveIndex β)
            (woodinIterationCardinalPrefix (woodinRecursiveIndex β))) ∧
          (πK.Evalb ![z, β] ↔ z = woodinSourceCardinals (woodinRecursiveIndex β)
            (woodinIterationCardinalPrefix (woodinRecursiveIndex β))) := by
  obtain ⟨A, _, B, _, _, _, _, _, hA, _, hB, _, _, _, _, _, he⟩ :=
    woodinSourcePresentation_deltaThree_uniform.{u}
  let σ := woodinSourceDecodedCertificate A
  let σK := woodinSourceDecodedCertificate B
  have hσ := woodinSourceDecodedCertificate_sigmaThree hA
  have hσK := woodinSourceDecodedCertificate_sigmaThree hB
  refine ⟨σ, woodinRecursionStepPiCertificate σ, σK, woodinRecursionStepPiCertificate σK,
    hσ, woodinRecursionStepPiCertificate_piThree hσ, hσK, woodinRecursionStepPiCertificate_piThree hσK, ?_⟩
  intro V _ _ _ δ β hδ hβ hn
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hβ
  have hr : woodinRecursiveIndex β ∈ δ := ordinal_mem_of_subset_mem (woodinRecursiveIndex_subset β) hβ
  refine ⟨woodinSourceIndex_recursiveIndex β hn, ?_⟩
  intro z
  have hp := fun w ↦ eval_woodinSourceDecodedCertificate A w β _ (he V δ _ hδ hr w).1
  have hk := fun w ↦ eval_woodinSourceDecodedCertificate B w β _ (he V δ _ hδ hr w).2.2.1
  exact ⟨hp z, eval_woodinOutputPiCertificate σ z β _ hp,
    hk z, eval_woodinOutputPiCertificate σK z β _ hk⟩

end ZFVP
