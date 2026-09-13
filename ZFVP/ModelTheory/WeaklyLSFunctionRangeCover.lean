import ZFVP.ModelTheory.ForcingHullValueCover
import ZFVP.SetTheory.SmallCollapseSurjection
import ZFVP.SetTheory.RegularCofinalSurjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.weaklyLS_function_range_cover (M : ForcingContext V) {δ ν B C : V}
    (hδ : IsWeaklyLSCardinal δ) (hsucc : ∀ η ∈ δ, succ η ∈ δ) (hν : ν ∈ δ)
    (hPν : M.P ⊆ hierarchy ν) (hBν : B ⊆ hierarchy ν)
    (F : ForcingName M.P)
    (hB : ∀ b ∈ B, IsForcingName M.P b) (hC : ∀ c ∈ C, IsForcingName M.P c)
    [IsFunction (M.ofName F)]
    (hdom : domain (M.ofName F) ⊆ range (M.evaluationGraph B hB))
    (hran : range (M.ofName F) ⊆ range (M.evaluationGraph C hC))
    (hne : IsNonempty (M.ofName F)) :
    ∃ R, ∃ hRC : R ⊆ C,
      range (M.ofName F) ⊆ range (M.evaluationGraph R (fun c hc ↦ hC c (hRC c hc))) ∧
      ∃ η ∈ δ, ∃ e ∈ R ^ (hierarchy η), range e = R := by
  let := hδ.1.1
  let T := forcingFunctionValueTable M.P M.R F.val B C
  let ρ := rank ({T, δ} : V)
  have hTρ : T ∈ hierarchy ρ := (mem_hierarchy_iff_rank_mem _ _).mpr
    (rank_mem (show T ∈ ({T, δ} : V) by simp))
  have hδρ : δ ∈ ρ := by
    simpa only [rank_of_ordinal] using rank_mem (show δ ∈ ({T, δ} : V) by simp)
  let := hierarchy_transitive ρ
  obtain ⟨Z, hZ, hνZ, hTZ, hsmall⟩ :=
    hδ.2.2 ν hν ρ inferInstance (IsOrdinal.toIsTransitive.transitive _ hδρ) T hTρ
  have hcover := M.range_subset_hull_evaluation F hB hC hZ hTZ
    (subset_trans hPν hνZ) (subset_trans hBν hνZ) hdom hran
  have hRZ : Z ∩ C ⊆ Z := fun _ hz ↦ (mem_inter_iff.mp hz).1
  have hRC : Z ∩ C ⊆ C := fun _ hz ↦ (mem_inter_iff.mp hz).2
  have hRne : IsNonempty (Z ∩ C) := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    obtain ⟨c, hc, _⟩ := (M.mem_range_evaluationGraph_iff (Z ∩ C) _ y).mp
      (hcover y (mem_range_of_kpair_mem hz))
    exact ⟨c, hc⟩
  have hZne : IsNonempty Z := by
    obtain ⟨c, hc⟩ := hRne
    exact ⟨c, hRZ c hc⟩
  obtain ⟨η, hη, e, he, hre⟩ := hsmall.rank_surjection hZne hsucc
  have hrid : range (identity (Z ∩ C)) = Z ∩ C := by
    apply mem_ext
    intro z
    simp [mem_range_iff]
  obtain ⟨q, hq, hrq⟩ := surjection_extension hRZ (identity_mem_function (Z ∩ C)) hrid hRne
  exact ⟨Z ∩ C, hRC, hcover, η, hη, compose e q, compose_function he hq,
    range_compose_surjective he hq hre hrq⟩

end ZFVP
