import ZFVP.SetTheory.ForcingClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingDirectedFamilyFormula : SetTheorySemisentence 4 :=
  f“P R I f. f ∈ !function.dfn P I ∧ ∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I,
    !kpair.dfn (!value.dfn f k) (!value.dfn f i) ∈ R ∧
    !kpair.dfn (!value.dfn f k) (!value.dfn f j) ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An internally indexed family directed towards stronger conditions. -/
def IsForcingDirectedFamily (P R I f : V) : Prop :=
  f ∈ P ^ I ∧ ∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I,
    ⟨f ‘ k, f ‘ i⟩ₖ ∈ R ∧ ⟨f ‘ k, f ‘ j⟩ₖ ∈ R

/-- Lower bounds for directed families with the specified internal index set. -/
def IsForcingDirectedClosedAt (P R I : V) : Prop :=
  ∀ f, IsForcingDirectedFamily P R I f → ∃ p ∈ P, ∀ i ∈ I, ⟨p, f ‘ i⟩ₖ ∈ R

instance forcingDirectedFamilyFormula_defined :
    ℒₛₑₜ-relation₄[V] IsForcingDirectedFamily via forcingDirectedFamilyFormula :=
  ⟨fun v ↦ by simp [forcingDirectedFamilyFormula, IsForcingDirectedFamily]⟩

instance isForcingDirectedFamily_definable : ℒₛₑₜ-relation₄[V] IsForcingDirectedFamily :=
  forcingDirectedFamilyFormula_defined.to_definable

instance isForcingDirectedClosedAt_definable : ℒₛₑₜ-relation₃[V] IsForcingDirectedClosedAt := by
  unfold IsForcingDirectedClosedAt
  definability

theorem IsForcingDescending.directed {P R α f : V} [IsOrdinal α]
    (hR : IsForcingPreorder P R) (hf : IsForcingDescending P R α f) :
    IsForcingDirectedFamily P R α f := by
  refine ⟨hf.1, fun i hi j hj ↦ ?_⟩
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
  · exact ⟨j, hj, hf.2 j hj i hij, hR.2.1 _ (function_value_mem hf.1 hj)⟩
  · exact ⟨i, hi, hR.2.1 _ (function_value_mem hf.1 hi), hR.2.1 _ (function_value_mem hf.1 hi)⟩
  · exact ⟨i, hi, hR.2.1 _ (function_value_mem hf.1 hi), hf.2 i hi j hji⟩

theorem IsForcingDirectedClosedAt.closedAt {P R α : V} [IsOrdinal α]
    (h : IsForcingDirectedClosedAt P R α) (hR : IsForcingPreorder P R) : IsForcingClosedAt P R α :=
  fun f hf ↦ h f (hf.directed hR)

end ZFVP
