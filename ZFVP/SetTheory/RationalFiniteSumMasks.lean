import ZFVP.SetTheory.RationalPartialSums
import ZFVP.SetTheory.FunctionValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rationalMaskedTerm (w E i : V) : V := by
  classical
  exact if i ∈ E then w ‘ i else rationalZero V

def rationalMaskedTermFormula : SetTheorySemisentence 4 :=
  f“q w E i. (i ∈ E ∧ q = !value.dfn w i) ∨ (i ∉ E ∧ q = !rationalZeroFormula)”
instance rationalMaskedTermFormula_defined : ℒₛₑₜ-function₃[V] rationalMaskedTerm via rationalMaskedTermFormula :=
  ⟨fun v ↦ by
    by_cases h : v 3 ∈ v 2
    · simp [rationalMaskedTermFormula, rationalMaskedTerm, h]
    · simp [rationalMaskedTermFormula, rationalMaskedTerm, h]⟩
instance rationalMaskedTerm_definable : ℒₛₑₜ-function₃[V] rationalMaskedTerm := rationalMaskedTermFormula_defined.to_definable

noncomputable def rationalMaskedWeights (w E : V) : V :=
  definableGraph (ω : V) (rationalMaskedTerm w E) (by definability)

def rationalMaskedWeightsFormula : SetTheorySemisentence 3 :=
  f“f w E. ∀ p, p ∈ f ↔ ∃ i ∈ !isω, p = !kpair.dfn i (!rationalMaskedTermFormula w E i)”
instance rationalMaskedWeightsFormula_defined : ℒₛₑₜ-function₂[V] rationalMaskedWeights via rationalMaskedWeightsFormula :=
  ⟨fun v ↦ by
    change rationalMaskedWeightsFormula.Evalb v ↔ v 0 = rationalMaskedWeights (v 1) (v 2)
    rw [mem_ext_iff]
    simp [rationalMaskedWeightsFormula, rationalMaskedWeights, mem_definableGraph_iff]⟩
instance rationalMaskedWeights_definable : ℒₛₑₜ-function₂[V] rationalMaskedWeights := rationalMaskedWeightsFormula_defined.to_definable

theorem rationalMaskedWeights_value (w E : V) {i : V} (hi : i ∈ (ω : V)) :
    (rationalMaskedWeights w E) ‘ i = rationalMaskedTerm w E i := value_definableGraph _ _ _ hi

theorem rationalMaskedWeights_mem {w : V} (hw : ∀ i ∈ (ω : V), w ‘ i ∈ internalRationals V) (E : V) :
    ∀ i ∈ (ω : V), (rationalMaskedWeights w E) ‘ i ∈ internalRationals V := by
  intro i hi
  rw [rationalMaskedWeights_value _ _ hi]
  by_cases he : i ∈ E
  · simpa only [rationalMaskedTerm, he, ↓reduceIte] using hw i hi
  · simpa only [rationalMaskedTerm, he, ↓reduceIte] using (rationalZero_mem (V := V))

theorem rationalFiniteSum_pointwise_le {f g : V}
    (hf : ∀ i ∈ (ω : V), f ‘ i ∈ internalRationals V)
    (hg : ∀ i ∈ (ω : V), g ‘ i ∈ internalRationals V)
    (hle : ∀ i ∈ (ω : V), ¬InternalRationalLT (g ‘ i) (f ‘ i)) :
    ∀ n ∈ (ω : V), ¬InternalRationalLT (rationalPartialSum g n) (rationalPartialSum f n) := by
  apply naturalNumber_induction (fun n ↦ ¬InternalRationalLT (rationalPartialSum g n) (rationalPartialSum f n)) (by definability)
  · simp only [rationalPartialSum_zero]
    exact internalRationalLT_irrefl rationalZero_mem
  · intro n hn ih
    rw [rationalPartialSum_succ _ hn, rationalPartialSum_succ _ hn]
    exact add_le_add
      (show (⟨rationalPartialSum f n, rationalPartialSum_mem hf n hn⟩ : InternalRational V) ≤
        ⟨rationalPartialSum g n, rationalPartialSum_mem hg n hn⟩ from ih)
      (show (⟨f ‘ n, hf n hn⟩ : InternalRational V) ≤ ⟨g ‘ n, hg n hn⟩ from hle n hn)

theorem rationalMaskedWeights_sum_le {w : V}
    (hw : ∀ i ∈ (ω : V), w ‘ i ∈ internalRationals V)
    (hpos : ∀ i ∈ (ω : V), ¬InternalRationalLT (w ‘ i) (rationalZero V)) (E : V) :
    ∀ m ∈ (ω : V), ¬InternalRationalLT (rationalPartialSum w m)
      (rationalPartialSum (rationalMaskedWeights w E) m) := by
  apply rationalFiniteSum_pointwise_le (rationalMaskedWeights_mem hw E) hw
  intro i hi
  rw [rationalMaskedWeights_value _ _ hi]
  by_cases he : i ∈ E
  · simp only [rationalMaskedTerm, he, ↓reduceIte]
    exact internalRationalLT_irrefl (hw i hi)
  · simpa only [rationalMaskedTerm, he, ↓reduceIte] using hpos i hi

theorem rationalMaskedWeights_empty_sum (w : V) : ∀ m ∈ (ω : V),
    rationalPartialSum (rationalMaskedWeights w (∅ : V)) m = rationalZero V := by
  apply naturalNumber_induction
    (fun m ↦ rationalPartialSum (rationalMaskedWeights w (∅ : V)) m = rationalZero V) (by definability)
  · exact rationalPartialSum_zero _
  · intro m hm ih
    rw [rationalPartialSum_succ _ hm, rationalMaskedWeights_value _ _ hm, ih]
    simp only [rationalMaskedTerm, not_mem_empty, ↓reduceIte, rationalAdd_zero rationalZero_mem]

theorem rationalMaskedWeights_singleton_sum {w j : V}
    (hw : ∀ i ∈ (ω : V), w ‘ i ∈ internalRationals V) (hj : j ∈ (ω : V)) :
    ∀ m ∈ (ω : V), rationalPartialSum (rationalMaskedWeights w ({j} : V)) m = rationalMaskedTerm w m j := by
  apply naturalNumber_induction
    (fun m ↦ rationalPartialSum (rationalMaskedWeights w ({j} : V)) m = rationalMaskedTerm w m j) (by definability)
  · rw [rationalPartialSum_zero]
    simp only [rationalMaskedTerm, zero_def, not_mem_empty, ↓reduceIte]
  · intro m hm ih
    rw [rationalPartialSum_succ _ hm, rationalMaskedWeights_value _ _ hm, ih]
    by_cases he : j = m
    · subst j
      simp only [rationalMaskedTerm, mem_succ_self, mem_irrefl, mem_singleton_iff, ↓reduceIte]
      exact congrArg Subtype.val (zero_add (⟨w ‘ m, hw m hm⟩ : InternalRational V))
    · by_cases hjm : j ∈ m
      · simp only [rationalMaskedTerm, mem_succ_iff, mem_singleton_iff, he, Ne.symm he, hjm,
          or_true, false_or, ↓reduceIte, rationalAdd_zero (hw j hj)]
      · simp only [rationalMaskedTerm, mem_succ_iff, mem_singleton_iff, he, Ne.symm he, hjm,
          or_false, false_or, ↓reduceIte, rationalAdd_zero rationalZero_mem]

theorem rationalMaskedWeights_insert_sum {w E j : V}
    (hw : ∀ i ∈ (ω : V), w ‘ i ∈ internalRationals V)
    (hj : j ∈ (ω : V)) (hfresh : j ∉ E) {m : V} (hm : m ∈ (ω : V)) (hjm : j ∈ m) :
    rationalPartialSum (rationalMaskedWeights w (insert j E)) m =
      rationalAdd (rationalPartialSum (rationalMaskedWeights w E) m) (w ‘ j) := by
  have he : ∀ i ∈ (ω : V), (rationalMaskedWeights w (insert j E)) ‘ i =
      rationalAdd ((rationalMaskedWeights w E) ‘ i) ((rationalMaskedWeights w ({j} : V)) ‘ i) := by
    intro i hi
    rw [rationalMaskedWeights_value _ _ hi, rationalMaskedWeights_value _ _ hi, rationalMaskedWeights_value _ _ hi]
    by_cases hij : i = j
    · subst i
      simp only [rationalMaskedTerm, mem_insert, mem_singleton_iff, hfresh, true_or, ↓reduceIte]
      exact congrArg Subtype.val (zero_add (⟨w ‘ j, hw j hi⟩ : InternalRational V)).symm
    · by_cases hiE : i ∈ E
      · simp only [rationalMaskedTerm, mem_insert, mem_singleton_iff, hij, hiE, false_or,
          ↓reduceIte, rationalAdd_zero (hw i hi)]
      · simp only [rationalMaskedTerm, mem_insert, mem_singleton_iff, hij, hiE, false_or,
          ↓reduceIte, rationalAdd_zero rationalZero_mem]
  rw [rationalPartialSum_add (rationalMaskedWeights_mem hw E)
    (rationalMaskedWeights_mem hw ({j} : V)) he m hm, rationalMaskedWeights_singleton_sum hw hj m hm]
  simp only [rationalMaskedTerm, hjm, ↓reduceIte]

end ZFVP
