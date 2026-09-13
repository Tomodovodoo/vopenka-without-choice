import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.ForcingOrder

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A definable decreasing assignment of finite sets stabilizes below any condition where
its value is internally finite. The induction applies to nonstandard finite values as well. -/
theorem finite_support_stabilization {P R p : V} (hR : IsForcingPreorder P R)
    (f : V → V) (hf : ℒₛₑₜ-function₁[V] f) (hp : p ∈ P)
    (hfin : IsInternallyFinite (f p))
    (hmono : ∀ q ∈ P, ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → f r ⊆ f q) :
    ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → f r = f q := by
  classical
  have key : ∀ A : V, IsInternallyFinite A →
      ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧
        ∀ i ∈ A, i ∈ f q → ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → i ∈ f r := by
    apply internallyFinite_induction (fun A ↦
      ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧
        ∀ i ∈ A, i ∈ f q → ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → i ∈ f r) (by definability)
    · exact ⟨p, hp, hR.2.1 p hp, fun i hi ↦ (not_mem_empty hi).elim⟩
    · intro A a ih
      obtain ⟨q, hq, hqp, hstable⟩ := ih
      by_cases hall : ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → a ∈ f r
      · refine ⟨q, hq, hqp, ?_⟩
        intro i hi hiq r hr hrq
        rcases mem_insert.mp hi with rfl | hi
        · exact hall r hr hrq
        · exact hstable i hi hiq r hr hrq
      · push Not at hall
        obtain ⟨r, hr, hrq, har⟩ := hall
        refine ⟨r, hr, hR.2.2 r hr q hq p hp hrq hqp, ?_⟩
        intro i hi hir s hs hsr
        rcases mem_insert.mp hi with rfl | hi
        · exact (har hir).elim
        · exact hstable i hi (hmono q hq r hr hrq i hir) s hs
            (hR.2.2 s hs r hr q hq hsr hrq)
  obtain ⟨q, hq, hqp, hstable⟩ := key (f p) hfin
  refine ⟨q, hq, hqp, fun r hr hrq ↦ SetTheory.subset_antisymm (hmono q hq r hr hrq) ?_⟩
  exact fun i hi ↦ hstable i (hmono p hp q hq hqp i hi) hi r hr hrq

end ZFVP
