import ZFVP.ModelTheory.SuccessorRankSeparation
import ZFVP.ModelTheory.SuccessorRankSetOperations
import ZFVP.SetTheory.WoodinCollapseFormula

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_mem_hierarchy {ρ κ β : V} (hρ : Cn 1 ρ)
    (hβ : IsOrdinal β) (hκV : κ ∈ hierarchy ρ) (hβV : β ∈ hierarchy ρ) :
    woodinCollapse κ β ∈ hierarchy ρ := by
  let := hρ.ordinal
  apply subset_mem_hierarchy_limit hρ.successor_closed
    (power_mem_hierarchy_limit hρ.successor_closed
      (prod_mem_hierarchy_limit hρ.successor_closed
        (prod_mem_hierarchy_limit hρ.successor_closed hκV hβV)
        (hρ.hierarchy_closed hβ hβV)))
  intro p hp
  exact mem_power_iff.mpr ((mem_woodinCollapse _ _ _).mp hp).1

theorem woodinCollapseOrder_mem_hierarchy {ρ κ β : V} (hρ : Cn 1 ρ)
    (hβ : IsOrdinal β) (hκV : κ ∈ hierarchy ρ) (hβV : β ∈ hierarchy ρ) :
    woodinCollapseOrder κ β ∈ hierarchy ρ :=
  reverseInclusionOrder_mem_hierarchy hρ (woodinCollapse_mem_hierarchy hρ hβ hκV hβV)

theorem successorRankEmbedding_value_woodinCollapse {ρ γ e κ β : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (h : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hβ : IsOrdinal β) (hκV : κ ∈ hierarchy ρ) (hβV : β ∈ hierarchy ρ) :
    e ‘ (woodinCollapse κ β) = woodinCollapse (e ‘ κ) (e ‘ β) := by
  let := hρ.ordinal
  let := hβ
  have hH := hρ.hierarchy_closed hβ hβV
  have hprod := prod_mem_hierarchy_limit hρ.successor_closed hκV hβV
  have hprodH := prod_mem_hierarchy_limit hρ.successor_closed hprod hH
  have hbound := power_mem_hierarchy_limit hρ.successor_closed hprodH
  have hP := woodinCollapse_mem_hierarchy hρ hβ hκV hβV
  have hsep (p : V) : p ∈ woodinCollapse κ β ↔
      p ∈ ℘ ((κ ×ˢ β) ×ˢ hierarchy β) ∧
        sigmaOneWoodinConditionFormula.Evalb (p :> ![κ, β, hierarchy β]) := by
    rw [eval_sigmaOneWoodinConditionFormula]
    exact ⟨fun hp ↦ ⟨mem_power_iff.mpr ((mem_woodinCollapse _ _ _).mp hp).1, hp⟩,
      fun hp ↦ hp.2⟩
  have he := successorRankEmbedding_separation hρ hγ h
    sigmaOneWoodinConditionFormula_sigmaOne ![κ, β, hierarchy β]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hκV, hβV, hH]) hP hbound hsep
  have hh := successorRankEmbedding_value_lower_hierarchy hρ hγ h hβ hβV
  let := hh.1
  have hv : (fun i ↦ e ‘ (![κ, β, hierarchy β] i)) = ![e ‘ κ, e ‘ β, e ‘ (hierarchy β)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rw [hv, hh.2] at he
  have hB : e ‘ (℘ ((κ ×ˢ β) ×ˢ hierarchy β)) =
      ℘ (((e ‘ κ) ×ˢ (e ‘ β)) ×ˢ hierarchy (e ‘ β)) := by
    rw [successorRankEmbedding_value_power hρ hγ h hprodH,
      successorRankEmbedding_value_product hρ hγ h hprod hH,
      successorRankEmbedding_value_product hρ hγ h hκV hβV, hh.2]
  rw [hB] at he
  apply mem_ext
  intro z
  rw [he z, eval_sigmaOneWoodinConditionFormula]
  exact ⟨fun hz ↦ hz.2, fun hz ↦
    ⟨mem_power_iff.mpr ((mem_woodinCollapse _ _ _).mp hz).1, hz⟩⟩

theorem successorRankEmbedding_value_woodinCollapseOrder {ρ γ e κ β : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (h : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hβ : IsOrdinal β) (hκV : κ ∈ hierarchy ρ) (hβV : β ∈ hierarchy ρ) :
    e ‘ (woodinCollapseOrder κ β) = woodinCollapseOrder (e ‘ κ) (e ‘ β) := by
  unfold woodinCollapseOrder
  rw [successorRankEmbedding_value_reverseInclusionOrder hρ hγ h
    (woodinCollapse_mem_hierarchy hρ hβ hκV hβV),
    successorRankEmbedding_value_woodinCollapse hρ hγ h hβ hκV hβV]

end ZFVP
