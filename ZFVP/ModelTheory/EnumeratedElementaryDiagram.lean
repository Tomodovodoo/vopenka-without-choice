import ZFVP.ModelTheory.ConstantExpansion
import ZFVP.ModelTheory.FiniteParameterElementarity
import ZFVP.ModelTheory.InfinitaryHenkinLanguage

/-! A countable list of names suffices to recover the original elementary map. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- All true finite-parameter first-order instances under the chosen enumeration. -/
def enumeratedDiagram {M : Type} [SetStructure M] [Nonempty M] (c : ℕ → M) : Theory (LSetC ℕ) :=
  {σ | ∃ n, ∃ φ : SetTheorySemisentence n, ∃ b : Fin n → ℕ,
    φ.Evalb (c ∘ b) ∧ σ = diagramSentence φ b Empty.elim}

theorem enumeratedDiagram_countable {M : Type} [SetStructure M] [Nonempty M] (c : ℕ → M) :
    (enumeratedDiagram c).Countable := Set.to_countable _

/-- Interpreting a surjective list of names gives an elementary map of the
original model. Repeated names are allowed. -/
theorem elementaryMap_of_models_enumeratedDiagram {M N : Type}
    [SetStructure M] [Nonempty M] [SetStructure N] [Nonempty N]
    (c : ℕ → M) (hc : Function.Surjective c) (d : ℕ → N)
    (h : (setConstStructure N d).toStruc ⊧* enumeratedDiagram c) :
    ∃ j : ElementaryMap M N, ∀ k, j (c k) = d k := by
  classical
  let r : M → ℕ := fun m ↦ Classical.choose (hc m)
  have hr (m : M) : c (r m) = m := Classical.choose_spec (hc m)
  have key {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → ℕ) :
      φ.Evalb (c ∘ b) ↔ φ.Evalb (d ∘ b) := by
    have forward (ψ : SetTheorySemisentence n) :
        ψ.Evalb (c ∘ b) → ψ.Evalb (d ∘ b) := by
      intro hψ
      have hm : diagramSentence ψ b Empty.elim ∈ enumeratedDiagram c :=
        ⟨n, ψ, b, hψ, rfl⟩
      simpa only [Semiformula.Evalb, Empty.eq_elim] using (eval_diagramSentence d ψ b Empty.elim).mp (Semantics.modelsSet_iff.mp h hm)
    refine ⟨forward φ, fun hφ ↦ ?_⟩
    by_contra hn
    have hneg := forward (∼φ) (by simpa using hn)
    simp only [LogicalConnective.HomClass.map_neg] at hneg
    exact hneg hφ
  let j : M → N := d ∘ r
  have hj {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → M) :
      φ.Evalb b ↔ φ.Evalb (j ∘ b) := by
    have hh := key φ (r ∘ b)
    have hb : c ∘ (r ∘ b) = b := funext fun i ↦ hr (b i)
    rw [hb] at hh
    exact hh
  refine ⟨⟨j, elementary_of_semisentences j hj⟩, ?_⟩
  intro k
  have he := key (Semiformula.rel Language.Set.Rel.eq ![.bvar 0, .bvar 1])
    ![r (c k), k]
  change (c (r (c k)) = c k) ↔ (d (r (c k)) = d k) at he
  exact he.mp (hr (c k))

/-- An elementary map realizes every named finite-parameter instance. -/
theorem models_enumeratedDiagram_of_elementaryMap {M : Type} {N : Type*}
    [SetStructure M] [Nonempty M] [SetStructure N] [Nonempty N]
    (j : ElementaryMap M N) (c : ℕ → M) :
    (setConstStructure N (j ∘ c)).toStruc ⊧* enumeratedDiagram c := by
  apply Semantics.modelsSet_iff.mpr
  rintro σ ⟨n, φ, b, hφ, rfl⟩
  apply (eval_diagramSentence (j ∘ c) φ b Empty.elim).mpr
  have he := (j.elementary φ (c ∘ b) (Empty.elim : Empty → M)).mp hφ
  simpa only [Function.comp_def, Empty.eq_elim] using he

end ZFVP


