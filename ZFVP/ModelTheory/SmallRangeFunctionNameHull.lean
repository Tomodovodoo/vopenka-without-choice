import ZFVP.ModelTheory.SmallSupportedNameHull
import ZFVP.ModelTheory.ElementaryPairNameClosure
import ZFVP.ModelTheory.ForcingLowRankAssignments
import ZFVP.ModelTheory.ForcingModelPairs
import ZFVP.SetTheory.SmallPairNameSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem function_pairNameSupport_cover (M : ForcingContext V) (F : ForcingName M.P)
    {B R : V} (hB : ∀ b ∈ B, IsForcingName M.P b) (hR : ∀ r ∈ R, IsForcingName M.P r)
    [IsFunction (M.ofName F)]
    (hdom : domain (M.ofName F) ⊆ range (M.evaluationGraph B hB))
    (hran : range (M.ofName F) ⊆ range (M.evaluationGraph R hR)) :
    ∀ z ∈ M.ofName F, ∃ σ : ForcingName M.P,
      σ.val ∈ orderedPairNameSupport M.one B R ∧ z = M.ofName σ := by
  intro z hz
  obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
  obtain ⟨b, hb, hxb⟩ := (M.mem_range_evaluationGraph_iff B hB x).mp
    (hdom x (mem_domain_iff.mpr ⟨y, hz⟩))
  obtain ⟨r, hr, hyr⟩ := (M.mem_range_evaluationGraph_iff R hR y).mp
    (hran y (mem_range_iff.mpr ⟨x, hz⟩))
  refine ⟨⟨orderedPairName M.one b r, orderedPairName_isName M.top.1 (hB b hb) (hR r hr)⟩,
    (mem_orderedPairNameSupport _ _ _ _).mpr ⟨b, hb, r, hr, rfl⟩, ?_⟩
  exact (congrArg₂ kpair hxb hyr).trans (M.of_orderedPair ⟨b, hB b hb⟩ ⟨r, hR r hr⟩).symm

theorem small_range_function_name_in_hull (M : ForcingContext V)
    {Y α β δ η ν B R e : V} [IsOrdinal α] [IsOrdinal β] [IsOrdinal δ]
    (hY : IsElementaryInclusion Y (hierarchy β))
    (hαβ : succ α ⊆ β) (hα : ∀ ξ ∈ α, succ ξ ∈ α)
    (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ)
    (hclosure : (Y ∩ hierarchy α) ^ hierarchy δ ⊆ Y) (hzero : (∅ : V) ∈ Y)
    (hη : η ∈ δ) (hν : ν ∈ δ) (hνα : ν ⊆ α)
    (hνY : hierarchy ν ⊆ Y) (hBν : B ⊆ hierarchy ν) (hPν : M.P ⊆ hierarchy ν)
    (hRY : R ⊆ Y ∩ hierarchy α)
    (he : e ∈ R ^ hierarchy η) (hre : range e = R)
    (hB : ∀ b ∈ B, IsForcingName M.P b) (hR : ∀ r ∈ R, IsForcingName M.P r)
    (F : ForcingName M.P) [IsFunction (M.ofName F)]
    (hdom : domain (M.ofName F) ⊆ range (M.evaluationGraph B hB))
    (hran : range (M.ofName F) ⊆ range (M.evaluationGraph R hR))
    (hne : IsNonempty (M.ofName F)) :
    ∃ τ : ForcingName M.P, τ.val ∈ Y ∧ M.ofName τ = M.ofName F ∧ τ.val ⊆ hierarchy α := by
  let := IsOrdinal.of_mem hν
  let := hierarchy_transitive β
  have hαβ' : α ⊆ β := subset_trans (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self α)) hαβ
  have hpY : ∀ p ∈ M.P, p ∈ Y ∩ hierarchy α := fun p hp ↦
    mem_inter_iff.mpr ⟨hνY p (hPν p hp), hierarchy_mono hνα p (hPν p hp)⟩
  have hbY : ∀ b ∈ B, b ∈ Y ∩ hierarchy α := fun b hb ↦
    mem_inter_iff.mpr ⟨hνY b (hBν b hb), hierarchy_mono hνα b (hBν b hb)⟩
  have hsupport : orderedPairNameSupport M.one B R ×ˢ M.P ⊆ Y ∩ hierarchy α := by
    intro z hz
    obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨b, hb, r, hr, rfl⟩ := (mem_orderedPairNameSupport _ _ _ _).mp hn
    have hnY := hY.orderedPairName_mem_of_rank hαβ' hα (hpY _ M.top.1) (hbY _ hb) (hRY _ hr)
    have hnα := (mem_inter_iff.mp hnY).2
    have hpα := (mem_inter_iff.mp (hpY p hp)).2
    have hrank := kpair_mem_hierarchy_limit hα hnα hpα
    exact mem_inter_iff.mpr ⟨hY.kpair_mem (mem_inter_iff.mp hnY).1
      (mem_inter_iff.mp (hpY p hp)).1 (hierarchy_mono hαβ' _ hrank), hrank⟩
  have hcover := M.function_pairNameSupport_cover F hB hR hdom hran
  obtain ⟨z, hz⟩ := hne
  obtain ⟨σ, hσ, _⟩ := hcover z hz
  have hsne : IsNonempty (orderedPairNameSupport M.one B R ×ˢ M.P) :=
    ⟨⟨σ.val, M.one⟩ₖ, kpair_mem_iff.mpr ⟨hσ, M.top.1⟩⟩
  obtain ⟨ε, hε, g, hg, hrg⟩ := orderedPairNameSupport_rank_surjection hδ hη hν hBν hPν he hre hsne
  let := IsOrdinal.of_mem hε
  have hamb : forcingSaturatedName M.P M.R (orderedPairNameSupport M.one B R) F.val ∈ hierarchy β := by
    apply hierarchy_mono hαβ
    rw [hierarchy_succ, mem_power_iff]
    intro z hz
    exact (mem_inter_iff.mp (hsupport z (forcingSaturatedName_subset _ _ _ _ z hz))).2
  refine ⟨⟨forcingSaturatedName M.P M.R (orderedPairNameSupport M.one B R) F.val,
    forcingSaturatedName_isName _ _ _ _⟩,
    hY.small_supported_saturatedName_mem hclosure hzero hsupport hε hg hrg hamb,
    M.saturatedName_value _ F hcover, ?_⟩
  intro z hz
  exact (mem_inter_iff.mp (hsupport z (forcingSaturatedName_subset _ _ _ _ z hz))).2

end ForcingContext
end ZFVP
