import ZFVP.ModelTheory.EndExtensionBasics
import ZFVP.SetTheory.EndExtensionSets
import ZFVP.SetTheory.EndExtensionHierarchyAgreement
import ZFVP.SetTheory.EndExtensionRank
import ZFVP.SetTheory.BoundedCodingPrimitives
import ZFVP.SetTheory.TransfiniteIteration

/-! Remark 2.6(e) of Enayat, "Models of set theory: extensions and dead ends": for models of
ZF a powerset-preserving end extension is the same thing as a rank extension. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A powerset-preserving end extension computes the same cumulative stages at old ordinals.
The induction is run inside `W` on the image of the internal graph of the stage function,
which is an element of `W`, so the induction hypothesis is a first-order property there. -/
theorem IsPowersetPreserving.map_hierarchy {j : MembershipEndExtension V W}
    (h : j.IsPowersetPreserving) (α : V) [IsOrdinal α] :
    j (hierarchy α) = hierarchy (j α) := by
  -- `F` is the internal graph of the stage function on `succ α`.
  have hdomF : domain (definableGraph (succ α) hierarchy hierarchy_definable) = succ α :=
    domain_definableGraph _ _ _
  set F : V := definableGraph (succ α) hierarchy hierarchy_definable with hFdef
  have hdom : domain (j F) = succ (j α) := by
    rw [← j.map_domain F, hdomF, j.map_succ]
  have hval : ∀ ξ ∈ succ α, (j F) ‘ (j ξ) = j (hierarchy ξ) := by
    intro ξ hξ
    rw [← j.map_value F ξ (by rw [hdomF]; exact hξ)]
    congr 1
    exact value_definableGraph (succ α) hierarchy hierarchy_definable hξ
  -- The stage function of `W` agrees with the image graph below `succ (j α)`.
  have key : ∀ ξ : Ordinal W, (ξ : W) ∈ succ (j α) → (j F) ‘ (ξ : W) = hierarchy (ξ : W) := by
    apply transfinite_induction
      (fun ξ : W ↦ ξ ∈ succ (j α) → (j F) ‘ ξ = hierarchy ξ) (by definability)
    intro ξ ih hmem
    rw [← j.map_succ α] at hmem
    obtain ⟨ξ', hξ'A, hξeq⟩ := (j.mem_map_iff (succ α) (ξ : W)).mp hmem
    have hξ'ord : IsOrdinal ξ' := IsOrdinal.of_mem hξ'A
    have hjξ'ord : IsOrdinal (j ξ') := (j.ordinal_iff ξ').mpr hξ'ord
    -- the induction hypothesis, transported back to `V`
    have ihβ : ∀ β ∈ ξ', j (hierarchy β) = hierarchy (j β) := by
      intro β hβ
      have hβord : IsOrdinal β := IsOrdinal.of_mem hβ
      have hβA : β ∈ succ α := IsOrdinal.toIsTransitive.mem_trans hβ hξ'A
      have : IsOrdinal (j β) := (j.ordinal_iff β).mpr hβord
      have hlt : (IsOrdinal.toOrdinal (j β) : Ordinal W) < ξ := by
        show j β ∈ (ξ : W)
        rw [hξeq]
        exact (j.mem_iff β ξ').mpr hβ
      have hstep : (j F) ‘ (j β) = hierarchy (j β) := ih _ hlt (by
        show j β ∈ succ (j α)
        rw [← j.map_succ α]
        exact (j.mem_iff β (succ α)).mpr hβA)
      rw [hval β hβA] at hstep
      exact hstep
    rw [hξeq, hval ξ' hξ'A]
    -- both stages have the same members, by the recursion clause on either side
    apply mem_ext
    intro y
    rw [j.mem_map_iff, mem_hierarchy_iff_of_ordinal (j ξ') y]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨β, hβ, hzβ⟩ := (mem_hierarchy_iff_of_ordinal ξ' z).mp hz
      refine ⟨j β, (j.mem_iff β ξ').mpr hβ, ?_⟩
      rw [← ihβ β hβ]
      exact (j.map_subset_iff z (hierarchy β)).mpr hzβ
    · rintro ⟨γ, hγ, hyγ⟩
      obtain ⟨β, hβ, rfl⟩ := (j.mem_map_iff ξ' γ).mp hγ
      rw [← ihβ β hβ] at hyγ
      obtain ⟨c, rfl⟩ := h (hierarchy β) y hyγ
      exact ⟨c, (mem_hierarchy_iff_of_ordinal ξ' c).mpr
        ⟨β, hβ, (j.map_subset_iff c (hierarchy β)).mp hyγ⟩, rfl⟩
  have hjα : IsOrdinal (j α) := (j.ordinal_iff α).mpr inferInstance
  have hfin := key (IsOrdinal.toOrdinal (j α)) (mem_succ_self (j α))
  rw [show ((IsOrdinal.toOrdinal (j α) : Ordinal W) : W) = j α from rfl] at hfin
  rw [← hfin, ← hval α (mem_succ_self α)]

/-- Restatement of `map_rank` under the hypothesis of Remark 2.6(e). The hypothesis is not
needed; see `MembershipEndExtension.map_rank`. -/
theorem IsPowersetPreserving.map_rank {j : MembershipEndExtension V W}
    (_h : j.IsPowersetPreserving) (x : V) : j (rank x) = rank (j x) :=
  j.map_rank x

/-- Enayat, Remark 2.6(e), first half: a powerset-preserving end extension is a rank
extension. -/
theorem IsPowersetPreserving.isRankExtension {j : MembershipEndExtension V W}
    (h : j.IsPowersetPreserving) : j.IsRankExtension := by
  intro a b hb
  by_contra hcon
  have h1 : rank b ⊆ rank (j a) := by
    rcases IsOrdinal.mem_trichotomy (rank (j a)) (rank b) with hm | hm | hm
    · exact absurd hm hcon
    · rw [hm]
    · exact (inferInstance : IsOrdinal (rank (j a))).transitive _ hm
  have h2 : b ⊆ j (hierarchy (rank a)) := by
    rw [h.map_hierarchy (rank a), j.map_rank a]
    exact subset_trans (subset_hierarchy_rank b) (hierarchy_mono h1)
  obtain ⟨c, hc⟩ := h (hierarchy (rank a)) b h2
  exact hb c hc

/-- Enayat, Remark 2.6(e), second half: a rank extension is powerset-preserving. -/
theorem IsRankExtension.isPowersetPreserving {j : MembershipEndExtension V W}
    (h : j.IsRankExtension) : j.IsPowersetPreserving := by
  intro a b hba
  by_contra hcon
  have hnew : ∀ c : V, j c ≠ b := fun c hc ↦ hcon ⟨c, hc⟩
  exact mem_irrefl _ (rank_mono hba _ (h a b hnew))

end MembershipEndExtension
end ZFVP
