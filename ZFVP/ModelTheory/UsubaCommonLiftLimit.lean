import ZFVP.ModelTheory.UsubaCommonLiftInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaCommonLiftBoundAt_limit {θ i p f c d j : V}
    [IsOrdinal θ] [IsOrdinal i] [IsOrdinal j]
    (hjθ : j ⊆ θ) (hi : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hc : c ∈ (T).P θ) (hd : d ∈ (T).P i)
    (hdc : ⟨d, ((T).projection i θ) ‘ c⟩ₖ ∈ (T).R i)
    (hq : usubaQuotientBoundRec θ i p f j ∈ (T).P j)
    (hprev : ∀ k ∈ j, IsUsubaCommonLiftBoundAt θ i p f c d k) :
    IsUsubaCommonLiftBoundAt θ i p f c d j := by
  intro hij r hr hrq b hb hbr hbd
  have hz : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have hl := usubaTowerLift_spec hij hr hb hbr
  have hcj := (T).projection_mem hjθ hc
  rw [usubaTower_R_limit hz hlim]
  apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
  refine ⟨hl.1, hcj, ?_⟩
  intro k hk
  let := IsOrdinal.of_mem hk
  have hkj : k ⊆ j := IsOrdinal.toIsTransitive.transitive _ hk
  have hproj : ((T).projection k j) ‘ (usubaQuotientBoundRec θ i p f j) =
      usubaQuotientBoundRec θ i p f k := by
    rw [usubaTower_projection_limit hz hlim hk hq, usubaQuotientBoundRec_limit hi hlim,
      usubaQuotientBoundHistory_value hk]
  have hh := usubaCommonLift_project_le hjθ hi hk hc hd hdc hq hproj (hprev k hk)
    hr hrq hb hbr hbd
  rw [usubaIterationPrefix_R hk]
  rw [usubaTower_projection_limit hz hlim hk hl.1] at hh
  have he := (T).projection_comp k j θ inferInstance inferInstance inferInstance hkj hjθ c hc
  rw [usubaTower_projection_limit hz hlim hk hcj] at he
  exact he.symm ▸ hh

end ZFVP
