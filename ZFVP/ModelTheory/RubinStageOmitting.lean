import ZFVP.ModelTheory.RubinStage
import ZFVP.ModelTheory.OmittingTypesEq

/-! # Enayat's Lemma A.2 without the omitting types hypothesis

`ZFVP.exists_elementary_extension_inseparable_upper_bounds` in `ZFVP.ModelTheory.RubinStage` takes
the Henkin-Orey omitting types theorem as a hypothesis. The language it applies it to,
`LSetC (M ⊕ ℕ)`, has equality, and the theory it applies it to, `rubinTheory δ ρ`, contains the
equality axioms, so `ZFVP.omittingTypesTheoremEq` discharges that hypothesis. What is left is
Enayat's Lemma A.5.

`RubinStage`'s own version is kept as it is: it is stated against `OmittingTypesTheorem`, which
quantifies over equality-free languages and is false (see
`ZFVP.ModelTheory.OmittingTypesCounterexample`), so it can only ever be used by supplying that
hypothesis from somewhere else. This file is the version to use.
-/

namespace ZFVP

open LO LO.FirstOrder LO.Entailment

universe u

/-- Enayat's Lemma A.2 with the omitting types hypothesis discharged: given a countable model `M`,
countably many pairs of inseparable subsets and countably many definable directed sets with no last
element, there is a countable elementary extension in which the pairs are still inseparable and
each directed set has an element above all of its old elements. Enayat's Lemma A.5 (`hA5`) is still
a hypothesis. -/
theorem exists_elementary_extension_inseparable_upper_bounds_of_a5
    (hA5 : SeparatingTypesLocallyOmitted.{u}) (M : Type u) [SetStructure M] [Nonempty M]
    [Countable M] (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (V W : ℕ → M → Prop) (hins : ∀ n, Inseparable M (V n) (W n))
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) :
    Nonempty (InseparableUpperBoundExtension M δ ρ V W) := by
  classical
  let _ : Encodable M := Encodable.ofCountable M
  have : Nonempty (ℕ × ((q : ℕ) × Semisentence (LSetC (M ⊕ ℕ)) (q + 1))) := ⟨(0, ⟨0, ⊤⟩)⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ × ((q : ℕ) × Semisentence (LSetC (M ⊕ ℕ)) (q + 1)))
  obtain ⟨Om⟩ := omittingTypesTheoremEq (LSetC (M ⊕ ℕ)) (rubinTheory δ ρ)
    eqAxiom_subset_rubinTheory (consistent_rubinTheory hdir)
    (fun k ↦ (e k).2.1) (fun k ↦ separatingType (V (e k).1) (W (e k).1) (e k).2.2)
    fun k ↦ hA5 M δ ρ V W hins hdir (e k).1 (e k).2.1 (e k).2.2
  obtain ⟨NM⟩ := exists_normalModel (rubinTheory δ ρ) eqAxiom_subset_rubinTheory
    (fun k ↦ separatingType (V (e k).1) (W (e k).1) (e k).2.2) Om.Dom Om.models Om.omits
  obtain ⟨j, hj⟩ := elementaryMap_of_models_rubinTheory NM.assign NM.models
  have hjc : (fun m ↦ j m) = NM.assign ∘ Sum.inl := funext hj
  refine ⟨{ Model := NM.Dom
            embedding := j
            inseparable := ?_
            upperBound := ?_ }⟩
  · intro n
    have hom : ∀ (q : ℕ) (ψ : Semisentence (LSetC (M ⊕ ℕ)) (q + 1)),
        OmitsWith NM.Dom NM.assign (separatingType (V n) (W n) ψ) := by
      intro q ψ
      obtain ⟨k, hk⟩ := he (n, ⟨q, ψ⟩)
      have hk' := NM.omits k
      rw [hk] at hk'
      exact hk'
    have := inseparable_of_omits NM.assign (V n) (W n) hom
    simpa only [hj] using this
  · intro n
    obtain ⟨hmem, hbound⟩ := upperBound_of_models_rubinTheory NM.assign NM.models n
    refine ⟨NM.assign (Sum.inr n), ?_, fun m hm ↦ ?_⟩
    · rw [hjc]; exact hmem
    · rw [hjc, hj m]; exact hbound m hm

end ZFVP
