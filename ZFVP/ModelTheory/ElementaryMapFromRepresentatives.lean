import ZFVP.ModelTheory.FiniteParameterElementarity
import ZFVP.SetTheory.ElementaryMap

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem elementaryMap_from_representatives {I M N : Type*}
    [SetStructure M] [SetStructure N] [Nonempty M]
    (a : I → M) (b : I → N) (ha : Function.Surjective a)
    (hφ : ∀ {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → I),
      φ.Evalb (a ∘ v) ↔ φ.Evalb (b ∘ v)) :
    ∃ j : ElementaryMap M N, ∀ t, j (a t) = b t := by
  classical
  let r : M → I := fun x ↦ (ha x).choose
  have hr : ∀ x, a (r x) = x := fun x ↦ (ha x).choose_spec
  have heq (s t : I) : a s = a t ↔ b s = b t := by
    simpa [Semiformula.Evalb, Structure.rel, Function.comp_def] using
      hφ (.rel Language.Set.Rel.eq ![.bvar 0, .bvar 1]) ![s, t]
  let f : M → N := b ∘ r
  have hf : ∀ {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → M),
      φ.Evalb v ↔ φ.Evalb (f ∘ v) := by
    intro n φ v
    have h := hφ φ (r ∘ v)
    have hv : a ∘ (r ∘ v) = v := by funext i; exact hr (v i)
    rw [hv] at h
    exact h
  refine ⟨⟨f, elementary_of_semisentences f hf⟩, ?_⟩
  intro t
  exact (heq (r (a t)) t).mp (hr (a t))

end ZFVP
