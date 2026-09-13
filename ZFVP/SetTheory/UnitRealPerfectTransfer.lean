import ZFVP.SetTheory.BinaryPerfectImages
import ZFVP.SetTheory.BinaryGreedySurjection

/-! Transfer of PSP to the actual internal closed unit interval. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def RealPerfectSetProperty (A : V) : Prop :=
  A ≤# (ω : V) ∨ ∃ P, IsPerfectRealSet P ∧ P ⊆ A

instance realPerfectSetProperty_definable : ℒₛₑₜ-predicate[V] RealPerfectSetProperty := by
  unfold RealPerfectSetProperty
  definability

theorem unitSet_cardLE_binaryPreimage {A : V} (hA : A ⊆ unitReals V) : A ≤# binaryPreimage A := by
  let G := definableGraph A binaryGreedy binaryGreedy_definable
  have hG : G ∈ (binaryPreimage A) ^ A :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (by
      intro x hx
      exact (mem_binaryPreimage_iff _ _).mpr ⟨binaryGreedy_mem x, by
        rw [binaryReal_greedy_of_mem (hA x hx)]
        exact hx⟩)
  refine ⟨G, hG, ?_⟩
  intro x y c hx hy
  obtain ⟨hxA, hcx⟩ := (pair_mem_definableGraph_iff _ _ _ x c).mp hx
  obtain ⟨hyA, hcy⟩ := (pair_mem_definableGraph_iff _ _ _ y c).mp hy
  have he : binaryGreedy x = binaryGreedy y := hcx.symm.trans hcy
  have hb := congrArg binaryReal he
  rwa [binaryReal_greedy_of_mem (hA x hxA), binaryReal_greedy_of_mem (hA y hyA)] at hb

theorem unitRealPerfectSetProperty_of_preimage {A : V} (hA : A ⊆ unitReals V)
    (h : PerfectSetProperty (binaryPreimage A)) : RealPerfectSetProperty A := by
  rcases h with hcount | ⟨T, hT, hTA⟩
  · exact Or.inl ((unitSet_cardLE_binaryPreimage hA).trans hcount)
  · refine Or.inr ⟨binaryImage (treeBody T), binaryPerfectImage_perfect hT, ?_⟩
    intro x hx
    obtain ⟨c, hc, rfl⟩ := (mem_binaryImage_iff _ _).mp hx
    exact ((mem_binaryPreimage_iff _ _).mp (hTA c hc)).2

theorem allUnitRealPerfectSetProperty_of_cantor (h : AllPerfectSetProperty V) :
    ∀ A : V, A ⊆ unitReals V → RealPerfectSetProperty A := by
  intro A hA
  apply unitRealPerfectSetProperty_of_preimage hA
  exact h _ (fun c hc ↦ ((mem_binaryPreimage_iff _ _).mp hc).1)

end ZFVP
