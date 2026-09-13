import ZFVP.ModelTheory.SmallRangeFunctionNameHull
import ZFVP.ModelTheory.WeaklyLSFunctionRangeCover

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.weaklyLS_two_hull_function_name (M : ForcingContext V)
    {Y α β δ ν B C : V} [IsOrdinal α] [IsOrdinal β]
    (hY : IsElementaryInclusion Y (hierarchy β))
    (hαβ : succ α ⊆ β) (hα : ∀ ξ ∈ α, succ ξ ∈ α)
    (hδ : IsWeaklyLSCardinal δ) (hδsucc : ∀ ξ ∈ δ, succ ξ ∈ δ)
    (hclosure : (Y ∩ hierarchy α) ^ hierarchy δ ⊆ Y) (hzero : (∅ : V) ∈ Y)
    (hν : ν ∈ δ) (hνα : ν ⊆ α)
    (hνY : hierarchy ν ⊆ Y) (hBν : B ⊆ hierarchy ν) (hPν : M.P ⊆ hierarchy ν)
    (hCY : C ⊆ Y ∩ hierarchy α)
    (hB : ∀ b ∈ B, IsForcingName M.P b) (hC : ∀ c ∈ C, IsForcingName M.P c)
    (F : ForcingName M.P) [IsFunction (M.ofName F)]
    (hdom : domain (M.ofName F) ⊆ range (M.evaluationGraph B hB))
    (hran : range (M.ofName F) ⊆ range (M.evaluationGraph C hC)) :
    ∃ τ : ForcingName M.P, τ.val ∈ Y ∧ M.ofName τ = M.ofName F ∧ τ.val ⊆ hierarchy α := by
  let := hδ.1.1
  rcases eq_empty_or_isNonempty (M.ofName F) with hempty | hne
  · refine ⟨⟨∅, empty_forcingName M.P⟩, hzero, ?_, fun _ hz ↦ False.elim (not_mem_empty hz)⟩
    rw [hempty]
    apply mem_ext
    intro x
    rw [M.mem_ofName_iff]
    simp
  obtain ⟨R, hRC, hcover, η, hη, e, he, hre⟩ :=
    M.weaklyLS_function_range_cover hδ hδsucc hν hPν hBν F hB hC hdom hran hne
  exact M.small_range_function_name_in_hull hY hαβ hα hδsucc hclosure hzero hη hν
    hνα hνY hBν hPν (subset_trans hRC hCY) he hre hB (fun r hr ↦ hC r (hRC r hr))
    F hdom hcover hne

end ZFVP
