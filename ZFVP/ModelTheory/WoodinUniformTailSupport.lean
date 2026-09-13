import ZFVP.ModelTheory.WoodinDirectTailSupport
import ZFVP.ModelTheory.UniformDirectNameSupport
import ZFVP.ModelTheory.WoodinQuotientBoundRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinBoundCoordinateName_isName (θ i f j : V) :
    IsForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (woodinBoundCoordinateName θ i f j) := forcingCompositionName_isName _ _ _ _

set_option maxHeartbeats 600000 in
theorem woodinBound_uniform_direct_support {δ θ i j X : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hi : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hjinac : IsChoicelessInaccessible j)
    (hB : (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i ∈ hierarchy j)
    (hX : X ∈ hierarchy j)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)) :
    ∃ b ∈ j, i ⊆ b ∧
      ∀ (G : Set V) (hG : IsExternalForcingGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G),
      ∀ (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
        (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)),
      let A : ForcingContext V := ⟨_, _, _, G, hR, ho, hG⟩
      A.ofName f ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check X →
        ∀ a ∈ A.check X, ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
          (A.ofName f) ‘ a = A.check d →
            IsThreadSupport j (forcingCodeE (woodinIterationPrefix j)) (d ‘ j) b := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have hRi := (hs i hiθ).code.system.order.preorder i (mem_succ_self i)
  have hoi := (hs i hiθ).code.system.tops.top i (mem_succ_self i)
  have hsj := fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj)
  have hcj := (woodinIterationPrefix_of_stages hsj).code
  let D := forcingInverseCodePoset θ (woodinIterationPrefix θ)
  let C := forcingDirectLimit j (forcingCodeP (woodinIterationPrefix j))
    (forcingCodeπ (woodinIterationPrefix j)) (forcingCodeE (woodinIterationPrefix j))
    (forcingCodeUniverse (woodinIterationPrefix j))
  let ρ := forcingThreadCoordinate D j
  have hρ : ρ ∈ C ^ D := by
    apply definableGraph_mem_function_of_mapsTo
    intro d hd
    exact (woodinThread_direct_coordinate hs hj h0 hlim hinac hd).1
  let := IsFunction.of_mem hρ
  let μ : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :=
    ⟨woodinBoundCoordinateName θ i f.val j, woodinBoundCoordinateName_isName _ _ _ _⟩
  obtain ⟨b, hb, hsupport⟩ := forcingDirectLimit_uniform_name_support hRi hoi hjinac hB hX hcj.system.split μ
  let := IsOrdinal.of_mem hb
  obtain ⟨c, hc, hbc, hic⟩ : ∃ c ∈ j, b ⊆ c ∧ i ⊆ c := by
    rcases IsOrdinal.mem_trichotomy i b with hib | rfl | hbi
    · exact ⟨b, hb, subset_refl _, IsOrdinal.toIsTransitive.transitive _ hib⟩
    · exact ⟨i, hi, subset_refl _, subset_refl _⟩
    · exact ⟨i, hi, IsOrdinal.toIsTransitive.transitive _ hbi, subset_refl _⟩
  refine ⟨c, hc, hic, ?_⟩
  intro G hG hR ho
  let A : ForcingContext V := ⟨_, _, _, G, hR, ho, hG⟩
  dsimp only
  intro hf a ha d hd had
  have hv : A.ofName μ = compose (A.ofName f) (A.check ρ) :=
    A.forcingCompositionName_value f ⟨checkName A.one ρ, checkName_isName ho.1 _⟩
  have hμ : A.ofName μ ∈ A.check C ^ A.check X := by
    rw [hv]
    exact compose_function hf ((A.check_function_iff _ _ _).mpr hρ)
  obtain ⟨e, he, hae, hes⟩ := hsupport G hG hμ a ha
  have hval : (A.ofName μ) ‘ a = A.check (d ‘ j) := by
    rw [hv, value_compose_of_mem_function hf ((A.check_function_iff _ _ _).mpr hρ) ha,
      had, A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hd), forcingThreadCoordinate_value hd]
  have hed : e = d ‘ j := (A.check_eq_iff _ _).mp (hae.symm.trans hval)
  rw [hed] at hes he
  exact hes.raise (P := forcingCodeP (woodinIterationPrefix j))
    (((mem_forcingInverseLimit_iff _ _ _ _ _).mp (forcingDirectLimit_subset _ _ _ _ _ _ he)).2.1)
    hc hbc (fun k hk hck q hq ↦ hcj.system.split.secComp b hb c hc k hk hbc hck q hq)

end ZFVP
