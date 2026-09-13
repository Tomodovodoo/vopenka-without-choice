import ZFVP.ModelTheory.ForcingSmallFunctions
import ZFVP.SetTheory.WeaklyLSNoSmallSurjection
import ZFVP.SetTheory.InjectionRetraction
import ZFVP.SetTheory.PulledWellOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Rank-small forcing cannot add a surjection from a checked lower-rank
set onto a checked weakly LS cardinal. Possible values form a ground
function indexed by inputs and conditions. -/
theorem no_small_surjection_of_weaklyLS (A : ForcingContext V) {κ X : V}
    (hκ : IsWeaklyLSCardinal κ) (hP : A.P ∈ hierarchy κ) (hX : X ∈ hierarchy κ)
    {f : A.Model} (hf : f ∈ A.check κ ^ A.check X) : range f ≠ A.check κ := by
  intro hr
  let := hκ.1.1
  obtain ⟨τ, rfl⟩ := A.ofName_surjective f
  let g := {z ∈ (X ×ˢ A.P) ×ˢ κ ;
    ForcesCheckedFunctionValue A.P A.R A.one τ.val (kpair.π₂ (kpair.π₁ z))
      (kpair.π₁ (kpair.π₁ z)) (kpair.π₂ z)}
  have hgmem (z y : V) : ⟨z, y⟩ₖ ∈ g ↔ z ∈ X ×ˢ A.P ∧ y ∈ κ ∧
      ForcesCheckedFunctionValue A.P A.R A.one τ.val (kpair.π₂ z) (kpair.π₁ z) y := by
    simp [g, and_assoc]
  have hgfun : g ∈ κ ^ domain g := by
    apply mem_function.intro
    · intro c hc
      obtain ⟨z, _, y, hy, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hc).1
      exact mem_prod_iff.mpr ⟨z, mem_domain_of_kpair_mem hc, y, hy, rfl⟩
    · intro z hz
      obtain ⟨y, hzy⟩ := mem_domain_iff.mp hz
      refine ⟨y, hzy, fun w hzw ↦ ?_⟩
      exact forcesCheckedFunctionValue_unique A.order A.top τ.property
        ((hgmem z w).mp hzw).2.2 ((hgmem z y).mp hzy).2.2
  have hdsub : domain g ⊆ X ×ˢ A.P := by
    intro z hz
    obtain ⟨y, hzy⟩ := mem_domain_iff.mp hz
    exact ((hgmem z y).mp hzy).1
  have hs : ∀ β ∈ κ, succ β ∈ κ :=
    fun _ hβ ↦ initial_succ_mem hκ.1 (IsOrdinal.toIsTransitive.transitive _ hκ.2.1) hβ
  have hd : domain g ∈ hierarchy κ := subset_mem_hierarchy_limit hs
    (prod_mem_hierarchy_limit hs hX hP) hdsub
  apply hκ.no_small_surjection hd hgfun
  apply SetTheory.subset_antisymm (range_subset_of_mem_function hgfun)
  intro y hy
  let := IsFunction.of_mem hf
  obtain ⟨a, hay⟩ := mem_range_iff.mp (hr.symm ▸ ((A.check_mem_iff _ _).mpr hy))
  have ha : a ∈ A.check X := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hay
  obtain ⟨x, hx, rfl⟩ := (A.mem_check_iff X a).mp ha
  have hv : (A.ofName τ) ‘ (A.check x) = A.check y := value_eq_of_kpair_mem hay
  obtain ⟨p, hpG, hpv⟩ := (A.checkedFunctionValue_truth τ x y).mpr ⟨inferInstance, hv⟩
  apply mem_range_iff.mpr
  refine ⟨⟨x, p⟩ₖ, (hgmem _ _).mpr ?_⟩
  exact ⟨kpair_mem_iff.mpr ⟨hx, A.generic.1.1 p hpG⟩, hy, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hpv⟩

theorem check_initial_of_weaklyLS (A : ForcingContext V) {κ : V}
    (hκ : IsWeaklyLSCardinal κ) (hP : A.P ∈ hierarchy κ) : IsInitialOrdinal (A.check κ) := by
  let := hκ.1.1
  refine ⟨inferInstance, ?_⟩
  intro α hα hcard
  obtain ⟨β, hβ, rfl⟩ := (A.mem_check_iff κ α).mp hα
  let := IsOrdinal.of_mem hβ
  have hne : IsNonempty (A.check κ) :=
    ⟨A.check ω, (A.check_mem_iff _ _).mpr hκ.2.1⟩
  obtain ⟨f, hf, hr⟩ := surjection_of_injection hcard hne
  exact A.no_small_surjection_of_weaklyLS hκ hP (ordinal_mem_hierarchy_iff.mpr hβ) hf hr

end ForcingContext
end ZFVP
