import ZFVP.ModelTheory.ForcingHullNormalization
import ZFVP.ModelTheory.ForcingWeaklyLSCardinal
import ZFVP.ModelTheory.ElementaryInclusionCollapse
import ZFVP.SetTheory.TransitiveRankSurjection
import ZFVP.SetTheory.SmallCollapseSurjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem smallTransitiveCollapse_of_checked_surjection (A : ForcingContext V) {κ D : V}
    (hκ : IsWeaklyLSCardinal κ) (hP : A.P ∈ hierarchy κ) (hD : D ∈ hierarchy κ)
    {X B e : A.Model} (hX : IsElementaryInclusion X B) (hB : IsTransitive B)
    (he : e ∈ X ^ A.check D) (her : range e = X) :
    HasSmallTransitiveCollapse (A.check κ) X := by
  let := hκ.1.1
  obtain ⟨C, hC, f, hf⟩ : ∃ C : A.Model, IsTransitive C ∧ ∃ f,
      IsTransitiveCollapse (membershipRelation X) X C f :=
    ⟨_, (hX.canonicalCollapse hB).1, _, hX.canonicalCollapse hB⟩
  obtain ⟨r, hr, hrr⟩ := transitive_rank_surjection hC
  have hcomp := compose_function (compose_function he hf.2.1) hr
  have hrcomp := range_compose_surjective (compose_function he hf.2.1) hr
    (range_compose_surjective he hf.2.1 her hf.2.2.1) hrr
  have hrκ : rank C ∈ A.check κ := by
    by_contra hn
    have hle : A.check κ ⊆ rank C := by
      rcases IsOrdinal.mem_trichotomy (rank C) (A.check κ) with h | heq | h
      · exact (hn h).elim
      · exact heq ▸ subset_refl _
      · exact IsOrdinal.toIsTransitive.transitive _ h
    have hne : IsNonempty (A.check κ) := ⟨A.check ω, (A.check_mem_iff _ _).mpr hκ.2.1⟩
    obtain ⟨g, hg, hgr⟩ := surjection_of_injection (cardLE_of_subset hle) hne
    exact A.no_small_surjection_of_weaklyLS hκ hP hD (compose_function hcomp hg)
      (range_compose_surjective hcomp hg hrcomp hgr)
  exact ⟨C, (mem_hierarchy_iff_rank_mem C (A.check κ)).mpr hrκ, f, hf⟩

theorem hullImage_smallTransitiveCollapse (A : ForcingContext V) {κ D X : V}
    (hκ : IsWeaklyLSCardinal κ) (hP : A.P ∈ hierarchy κ)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (hsmall : HasSmallTransitiveCollapse κ X)
    {B : A.Model} (himg : IsElementaryInclusion (A.hullImage D hD X) B)
    (hB : IsTransitive B) :
    HasSmallTransitiveCollapse (A.check κ) (A.hullImage D hD X) := by
  let := hκ.1.1
  have hXne : IsNonempty X := by
    obtain ⟨x, hx⟩ := himg.source_nonempty.nonempty
    obtain ⟨τ, hτ, _⟩ := (A.mem_hullImage_iff D hD X x).mp hx
    exact ⟨τ, (mem_inter_iff.mp hτ).1⟩
  have hs : ∀ β ∈ κ, succ β ∈ κ := fun _ hβ ↦
    initial_succ_mem hκ.1 (IsOrdinal.toIsTransitive.transitive _ hκ.2.1) hβ
  obtain ⟨ρ, hρκ, f, hf, hfr⟩ := hsmall.rank_surjection hXne hs
  have hff := (A.check_function_iff f (hierarchy ρ) X).mpr hf
  have hfrr : range (A.check f) = A.check X := by
    exact (A.checkEmbedding.map_range f).symm.trans (congrArg A.check hfr)
  let hE : ∀ τ ∈ X ∩ D, IsForcingName A.P τ := fun τ hτ ↦ hD τ (mem_inter_iff.mp hτ).2
  have hsub : A.check (X ∩ D) ⊆ A.check X :=
    (A.checkEmbedding.subset_iff _ _).mpr (fun τ hτ ↦ (mem_inter_iff.mp hτ).1)
  obtain ⟨g, hg, hgr⟩ := surjection_extension hsub (A.evaluationGraph_mem_function (X ∩ D) hE)
    rfl himg.source_nonempty
  exact A.smallTransitiveCollapse_of_checked_surjection hκ hP (hierarchy_mem hρκ) himg hB
    (compose_function hff hg) (range_compose_surjective hff hg hfrr hgr)

theorem lowRank_hullImage_elementary_small (A : ForcingContext V) {κ β X B : V}
    (hκ : IsWeaklyLSCardinal κ) (hPκ : A.P ∈ hierarchy κ)
    (hβ : Cn 1 β) [IsTransitive B] (hX : IsElementaryInclusion X B)
    (hlow : hierarchy (succ (ω : V)) ⊆ X)
    (hβX : hierarchy β ∈ X) (hDX : lowRankNameSet A.P β ∈ X)
    (hPβ : A.P ∈ hierarchy β) (hPX : A.P ⊆ X)
    (hTX : internalForcingTruthTable A.P A.R (lowRankNameSet A.P β) ∈ X)
    (hsmall : HasSmallTransitiveCollapse κ X) :
    IsElementaryInclusion (A.hullImage (lowRankNameSet A.P β) (A.lowRankNameSet_names β) X)
      (hierarchy (A.check β)) ∧
    HasSmallTransitiveCollapse (A.check κ)
      (A.hullImage (lowRankNameSet A.P β) (A.lowRankNameSet_names β) X) := by
  let := hβ.ordinal
  have he := A.lowRank_hullImage_elementary hβ hX hlow hβX hDX hPβ hPX hTX
  exact ⟨he, A.hullImage_smallTransitiveCollapse hκ hPκ (A.lowRankNameSet_names β) hsmall
    he (hierarchy_transitive _)⟩

end ForcingContext
end ZFVP
