import ZFVP.ModelTheory.LevySubsetLocalization
import ZFVP.ModelTheory.CohenStage
import ZFVP.ModelTheory.SolovayLocalization
import ZFVP.SetTheory.PerfectSetCore

/-! Localization of subsets of a small checked set: a subset of `Q̌` with `Q ≤# ν < κ` in the Levy
extension lies in a bounded stage, by transporting along a ground injection of `Q` into `ν`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem preimagePredicate_definable (e F Q : V) :
    ℒₛₑₜ-predicate (fun z : V ↦ z ∈ Q ∧ e ‘ z ∈ F) := by
  definability

/-- A subset of `Q̌` is the value of a set of the smaller extension when its image under a checked
ground injection is. -/
theorem exists_preimage_copy {A B : ForcingContext V} (L : ForcingRealization A B.Model)
    (hground : ∀ a : V, L.ground a = B.check a) {Q ν e : V} (he : e ∈ ν ^ Q) (hinj : Injective e)
    {F : B.Model} (hF : F ⊆ B.check Q) {F' : A.Model}
    (hF' : L.value F' = image (B.check e) F) :
    ∃ F₀ : A.Model, L.value F₀ = F := by
  have hvc : ∀ a : V, L.value (A.check a) = B.check a := fun a ↦ (L.value_check a).trans (hground a)
  have hmem : ∀ a b : A.Model, L.value a ∈ L.value b ↔ a ∈ b := fun a b ↦ L.value_mem_iff a b
  have hef : IsFunction e := IsFunction.of_mem he
  have hedom : domain e = Q := domain_eq_of_mem_function he
  have hAe : IsFunction (A.check e) := A.checkEmbedding.map_function e
  have hBe : IsFunction (B.check e) := B.checkEmbedding.map_function e
  have hAedom : domain (A.check e) = A.check Q := by rw [A.check_domain, hedom]
  obtain ⟨cQ, hcQ⟩ : ∃ c : A.Model, c = A.check Q := ⟨_, rfl⟩
  obtain ⟨ce, hce⟩ : ∃ c : A.Model, c = A.check e := ⟨_, rfl⟩
  obtain ⟨dQ, hdQ⟩ : ∃ d : B.Model, d = B.check Q := ⟨_, rfl⟩
  obtain ⟨de, hde⟩ : ∃ d : B.Model, d = B.check e := ⟨_, rfl⟩
  have hvQ : L.value cQ = dQ := by rw [hcQ, hdQ]; exact hvc _
  have hve : L.value ce = de := by rw [hce, hde]; exact hvc _
  have hsep := L.embedding.map_separation cQ (fun z ↦ z ∈ cQ ∧ ce ‘ z ∈ F')
    (fun z ↦ z ∈ dQ ∧ de ‘ z ∈ image (B.check e) F)
    (preimagePredicate_definable ce F' cQ) (preimagePredicate_definable de _ dQ) (by
      intro z hz
      change (z ∈ cQ ∧ ce ‘ z ∈ F') ↔ (L.value z ∈ dQ ∧ de ‘ (L.value z) ∈ image (B.check e) F)
      have hzd : z ∈ domain ce := by rw [hce, hAedom, ← hcQ]; exact hz
      have hcef : IsFunction ce := by rw [hce]; exact hAe
      have hval : L.value (ce ‘ z) = de ‘ (L.value z) := by
        rw [← hve]
        have := L.embedding.map_value ce z hzd
        change L.value (ce ‘ z) = (L.value ce) ‘ (L.value z) at this
        exact this
      constructor
      · rintro ⟨hz', hzF⟩
        exact ⟨by rw [← hvQ]; exact (hmem _ _).mpr hz', by rw [← hval, ← hF']; exact (hmem _ _).mpr hzF⟩
      · rintro ⟨hz', hzF⟩
        refine ⟨(hmem _ _).mp (by rw [hvQ]; exact hz'), ?_⟩
        rw [← hF', ← hval] at hzF
        exact (hmem _ _).mp hzF)
  refine ⟨sep cQ (fun z ↦ z ∈ cQ ∧ ce ‘ z ∈ F') (preimagePredicate_definable ce F' cQ), ?_⟩
  have hsep' : L.value (sep cQ (fun z ↦ z ∈ cQ ∧ ce ‘ z ∈ F') (preimagePredicate_definable ce F' cQ)) =
      sep (L.value cQ) (fun z ↦ z ∈ dQ ∧ de ‘ z ∈ image (B.check e) F)
        (preimagePredicate_definable de _ dQ) := hsep
  rw [hsep', hvQ]
  apply mem_ext
  intro z
  rw [mem_sep_iff]
  constructor
  · rintro ⟨hzQ, _, hz⟩
    rw [hde] at hz
    obtain ⟨w, hw, hwz⟩ := (mem_image_iff' _ _ _).mp hz
    have hwF : w ∈ F := hw
    have hwQ : w ∈ B.check Q := hF w hwF
    have hBedom : domain (B.check e) = B.check Q := by rw [B.check_domain, hedom]
    have hwd : w ∈ domain (B.check e) := by rw [hBedom]; exact hwQ
    have hzd : z ∈ domain (B.check e) := by rw [hBedom, ← hdQ]; exact hzQ
    obtain ⟨w', hw'Q, rfl⟩ := (B.mem_check_iff Q w).mp hwQ
    obtain ⟨z', hz'Q, rfl⟩ := (B.mem_check_iff Q z).mp (by rw [← hdQ]; exact hzQ)
    have hw'd : w' ∈ domain e := by rw [hedom]; exact hw'Q
    have hz'd : z' ∈ domain e := by rw [hedom]; exact hz'Q
    have hval : ⟨w', e ‘ z'⟩ₖ ∈ e := by
      have h1 : (B.check e) ‘ (B.check w') = (B.check e) ‘ (B.check z') := value_eq_of_kpair_mem hwz
      rw [B.check_value hw'd, B.check_value hz'd, B.check_eq_iff] at h1
      rw [← h1]
      exact kpair_value_mem hw'd
    have : w' = z' := hinj w' z' (e ‘ z') hval (kpair_value_mem hz'd)
    rw [← this]
    exact hwF
  · intro hz
    refine ⟨by rw [hdQ]; exact hF z hz, by rw [hdQ]; exact hF z hz, ?_⟩
    rw [hde]
    exact (mem_image_iff' _ _ _).mpr ⟨z, hz, kpair_value_mem (by rw [B.check_domain, hedom]; exact hF z hz)⟩

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- Subsets of the check of a ground set of size below `κ` lie in a bounded stage. -/
theorem levy_subset_check_localized {Q ν : V} (hQ : Q ≤# ν) (hν : ν ∈ κ)
    (F : (levyContext κ hG).Model) (hF : F ⊆ (levyContext κ hG).check Q) : IsLocalized hG F := by
  obtain ⟨e, he, hinj⟩ := hQ
  have hef : IsFunction e := IsFunction.of_mem he
  have hedom : domain e = Q := domain_eq_of_mem_function he
  let W := levyContext κ hG
  have hBedom : domain (W.check e) = W.check Q := by rw [W.check_domain, hedom]
  have hBe : IsFunction (W.check e) := W.checkEmbedding.map_function e
  have himg : image (W.check e) F ⊆ W.check ν := by
    intro y hy
    obtain ⟨w, hw, hwy⟩ := (mem_image_iff' _ _ _).mp hy
    have hwd : w ∈ domain (W.check e) := by rw [hBedom]; exact hF w hw
    obtain ⟨w', hw'Q, rfl⟩ := (W.mem_check_iff Q w).mp (hF w hw)
    have hw'd : w' ∈ domain e := by rw [hedom]; exact hw'Q
    have hval : y = W.check (e ‘ w') := by
      rw [← W.check_value hw'd]
      exact (value_eq_of_kpair_mem hwy).symm
    rw [hval, W.check_mem_iff]
    exact function_value_mem he hw'Q
  obtain ⟨ξ, hξ, y, hy⟩ := levy_subset_localized hAC hU hc hω hκ hG hν (image (W.check e) F) himg
  haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  obtain ⟨F₀, hF₀⟩ := exists_preimage_copy (levySubRealization ξ hξ' hG) (levySubRealization_ground ξ hξ' hG)
    he hinj hF hy
  exact ⟨ξ, hξ, F₀, hF₀⟩

end

end ZFVP
