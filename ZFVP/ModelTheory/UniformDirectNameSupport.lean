import ZFVP.ModelTheory.ForcingUniformFunctionValues
import ZFVP.ModelTheory.ForcingCompositionName
import ZFVP.ModelTheory.DirectLimitQuotientSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingDirectLimit_uniform_name_support {B R one θ P π E U X : V}
    (hR : IsForcingPreorder B R) (ht : IsForcingTop B R one)
    (hθ : IsChoicelessInaccessible θ) (hB : B ∈ hierarchy θ) (hX : X ∈ hierarchy θ)
    (h : IsSplitForcingSystem θ P π E) (f : ForcingName B) :
    ∃ k ∈ θ, ∀ (G : Set V) (hG : IsExternalForcingGeneric B R G),
      let A : ForcingContext V := ⟨B, R, one, G, hR, ht, hG⟩
      A.ofName f ∈ A.check (forcingDirectLimit θ P π E U) ^ A.check X →
        ∀ i ∈ A.check X, ∃ q ∈ forcingDirectLimit θ P π E U,
          (A.ofName f) ‘ i = A.check q ∧ IsThreadSupport θ E q k := by
  let := hθ.1
  let D := forcingDirectLimit θ P π E U
  let L : V → V := leastOrdinalOrZero (fun q k ↦ IsThreadSupport θ E q k) (by definability)
  have hL (q : V) (hq : q ∈ D) : IsThreadSupport θ E q (L q) := by
    obtain ⟨_, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hq
    exact (leastOrdinalOrZero_spec _ _ _ ⟨k, IsOrdinal.of_mem hk.1, hk⟩).2.1
  let H := definableGraph D L (by definability)
  have hH : H ∈ θ ^ D := definableGraph_mem_function_of_mapsTo _ _ _ _ (fun q hq ↦ (hL q hq).1)
  let := IsFunction.of_mem hH
  let μ : ForcingName B := ⟨forcingCompositionName B R f.val (checkName one H),
    forcingCompositionName_isName _ _ _ _⟩
  let k := forcingCheckedFunctionBound B R one θ X μ.val
  have hk : k ∈ θ := (forcingCheckedFunctionBound_spec hR ht hθ hB hX μ).1
  let := IsOrdinal.of_mem hk
  refine ⟨k, hk, ?_⟩
  intro G hG
  let A : ForcingContext V := ⟨B, R, one, G, hR, ht, hG⟩
  change A.ofName f ∈ A.check D ^ A.check X → _
  intro hf i hi
  have hμ : A.ofName μ = compose (A.ofName f) (A.check H) :=
    A.forcingCompositionName_value f ⟨checkName one H, checkName_isName ht.1 H⟩
  have hμf : A.ofName μ ∈ A.check θ ^ A.check X := by
    rw [hμ]
    exact compose_function hf ((A.check_function_iff H D θ).mpr hH)
  have hb := A.checkedFunctionBound_values hθ hB hX μ hμf i hi
  obtain ⟨q, hq, he⟩ := (A.mem_check_iff D _).mp (function_value_mem hf hi)
  have hLk : L q ∈ k := by
    rw [hμ, value_compose_of_mem_function hf ((A.check_function_iff H D θ).mpr hH) hi,
      he, A.check_value ((domain_eq_of_mem_function hH).symm ▸ hq),
      value_definableGraph _ _ _ hq, A.check_mem_iff] at hb
    exact hb
  refine ⟨q, hq, he, (hL q hq).raise (P := P) ?_ hk (IsOrdinal.toIsTransitive.transitive _ hLk) ?_⟩
  · exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (forcingDirectLimit_subset _ _ _ _ _ _ hq)).2.1
  · intro j hj hkj p hp
    exact h.secComp _ (hL q hq).1 k hk j hj (IsOrdinal.toIsTransitive.transitive _ hLk) hkj p hp

end ZFVP
