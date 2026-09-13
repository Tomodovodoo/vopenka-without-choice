import ZFVP.SetTheory.CountingWitness
import ZFVP.SetTheory.EndExtensionWellOrdering
import ZFVP.ModelTheory.GroundRealsHOD
import ZFVP.ModelTheory.LevyCollapseOmegaOne

/-! `κ` is the first uncountable ordinal of the Solovay model `HOD_{V ∪ R}` (lem:Solovay-regularity):
every ordinal below `κ` is collapsed by an injection into `ω` that is itself definable from reals,
while no injection of `κ̌` into `ω` exists in the extension at all. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-- A definable subset of a ground set is hereditarily definable. -/
theorem hereditarily_of_subset_check {x : A.Model} (hx : A.IsGroundRealDefinable x) {a : V}
    (hxa : x ⊆ A.check a) : A.IsHereditarilyGroundRealDefinable x := by
  intro y hy
  have htc : IsTransitive (A.check (transitiveClosure a)) :=
    check_transitive_of_ground (transitiveClosure_transitive a)
  have hsub' : A.check a ⊆ A.check (transitiveClosure a) :=
    (A.checkEmbedding.subset_iff _ _).mpr (subset_transitiveClosure a)
  let T : A.Model := insert x (A.check (transitiveClosure a))
  have hT : IsTransitive T := by
    refine ⟨fun y hy z hz ↦ ?_⟩
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_insert.mpr (Or.inr (hsub' z (hxa z hz)))
    · exact mem_insert.mpr (Or.inr (htc.mem_trans hz hy))
  have hsub : transitiveClosure ({x} : A.Model) ⊆ T :=
    transitiveClosure_minimal _ _ (by rw [singleton_subset_iff_mem]; exact mem_insert.mpr (Or.inl rfl)) hT
  rcases mem_insert.mp (hsub y hy) with rfl | hy'
  · exact hx
  · obtain ⟨b, _, rfl⟩ := (A.mem_check_iff _ _).mp hy'
    exact groundRealDefinable_of_parameter (Or.inl ⟨b, rfl⟩)

/-- An injection of a ground ordinal into `ω` is definable from reals: it is the inverse of the
unique order isomorphism between the real coding its image order and the ordinal. -/
theorem groundRealDefinable_of_injection {β : V} [IsOrdinal β] {e : A.Model}
    (he : e ∈ (ω : A.Model) ^ A.check β) (heinj : Injective e) : A.IsGroundRealDefinable e := by
  obtain ⟨g, hg, hginj⟩ := (omega_prod_cardLE_omega : ((ω : V) ×ˢ (ω : V)) ≤# (ω : V))
  have hcg : A.check g ∈ (ω : A.Model) ^ ((ω : A.Model) ×ˢ (ω : A.Model)) := by
    have := (A.check_function_iff g ((ω : V) ×ˢ (ω : V)) (ω : V)).mpr hg
    have h1 : A.check ((ω : V) ×ˢ (ω : V)) = A.check (ω : V) ×ˢ A.check (ω : V) :=
      A.checkEmbedding.map_prod _ _
    rwa [h1, check_omega_eq] at this
  have hcginj : Injective (A.check g) := (A.checkEmbedding.injective_iff g).mpr hginj
  haveI : IsOrdinal (A.check β) := (A.check_ordinal_iff β).mpr inferInstance
  refine ⟨4, countingWitnessFormula,
    ![A.check β, range e, A.check g, orderReal (A.check g) e (A.check β)], ?_, fun b ↦ ?_⟩
  · intro i
    match i with
    | 0 => exact Or.inl ⟨β, rfl⟩
    | 1 => exact Or.inr (Or.inl (by rw [check_omega_eq]; exact range_subset_of_mem_function he))
    | 2 => exact Or.inl ⟨g, rfl⟩
    | 3 => exact Or.inr (Or.inl (by rw [check_omega_eq]; exact orderReal_subset _ _ _))
  · exact mem_iff_countingWitness hcg hcginj he heinj b

end ForcingContext

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- Every ordinal below `κ` is countable in the Solovay model: the collapsing injection lies in
`HOD_{V ∪ R}`. -/
theorem levy_solovay_countable {β : V} (hβ : β ∈ κ) :
    ∃ e : (levyContext κ hG).SolovayModel,
      e.val ∈ (ω : (levyContext κ hG).Model) ^ (levyContext κ hG).check β ∧ Injective e.val := by
  obtain ⟨e, he, heinj⟩ :=
    (levy_check_countable hG hβ : (levyContext κ hG).check β ≤# (ω : (levyContext κ hG).Model))
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  have hdef := ForcingContext.groundRealDefinable_of_injection he heinj
  have hsub : e ⊆ (levyContext κ hG).check (β ×ˢ (ω : V)) := by
    have h1 : (levyContext κ hG).check (β ×ˢ (ω : V)) =
        (levyContext κ hG).check β ×ˢ (levyContext κ hG).check (ω : V) :=
      (levyContext κ hG).checkEmbedding.map_prod _ _
    rw [h1, ForcingContext.check_omega_eq]
    exact subset_prod_of_mem_function he
  exact ⟨⟨e, ForcingContext.hereditarily_of_subset_check hdef hsub⟩, he, heinj⟩

include hAC hU hc hω hκ in
/-- `κ̌` is uncountable in the Solovay model (indeed in the whole extension). -/
theorem levy_solovay_kappa_uncountable :
    ¬ ∃ e : (levyContext κ hG).SolovayModel,
      e.val ∈ (ω : (levyContext κ hG).Model) ^ (levyContext κ hG).check κ ∧ Injective e.val := by
  rintro ⟨e, he, heinj⟩
  have h := (hartogsNumber_eq_iff _ _).mp (levy_check_hartogs hAC hU hc hω hκ hG)
  exact h.2.1 ⟨e.val, he, heinj⟩

end

end ZFVP
