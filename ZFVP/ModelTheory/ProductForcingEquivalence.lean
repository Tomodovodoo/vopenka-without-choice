import ZFVP.ModelTheory.ProductForcingLemma
import ZFVP.SetTheory.EndExtensionNameAction
import ZFVP.SetTheory.NameValueAction
import ZFVP.ModelTheory.LevyCollapseSubmodel

/-! The product factorization `V[G] ≃ V[G₁][G₂]` for a generic `G` on `P₁ × P₂`, over the
ground model: names over `P₁` are lifted to the product along `p ↦ ⟨p, 1⟩`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The first projection as a set function on the product. -/
noncomputable def firstProjection (P₁ P₂ : V) : V :=
  definableGraph (P₁ ×ˢ P₂) kpair.π₁ (by definability)

/-- The second projection as a set function on the product. -/
noncomputable def secondProjection (P₁ P₂ : V) : V :=
  definableGraph (P₁ ×ˢ P₂) kpair.π₂ (by definability)

/-- The embedding `p ↦ ⟨p, one₂⟩` of the first factor into the product. -/
noncomputable def leftEmbedding (P₁ one₂ : V) : V :=
  definableGraph P₁ (fun p ↦ ⟨p, one₂⟩ₖ) (by definability)

theorem leftEmbedding_mem_function {P₁ P₂ one₂ : V} (h : one₂ ∈ P₂) :
    leftEmbedding P₁ one₂ ∈ (P₁ ×ˢ P₂) ^ P₁ :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun p hp ↦ kpair_mem_iff.mpr ⟨hp, h⟩)

theorem leftEmbedding_injective (P₁ one₂ : V) : Injective (leftEmbedding P₁ one₂) := by
  intro p q z hp hq
  obtain ⟨_, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hp
  obtain ⟨_, hz⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hq
  exact (kpair_iff.mp hz).1

theorem leftEmbedding_value {P₁ one₂ p : V} (hp : p ∈ P₁) : (leftEmbedding P₁ one₂) ‘ p = ⟨p, one₂⟩ₖ :=
  value_definableGraph _ _ _ hp

theorem pair_mem_leftEmbedding_iff (P₁ one₂ a b : V) :
    ⟨a, b⟩ₖ ∈ leftEmbedding P₁ one₂ ↔ a ∈ P₁ ∧ b = ⟨a, one₂⟩ₖ :=
  pair_mem_definableGraph_iff _ _ _ _ _

section

variable {P₁ R₁ one₁ P₂ R₂ one₂ : V} (h₁ : IsForcingPreorder P₁ R₁) (t₁ : IsForcingTop P₁ R₁ one₁)
  (h₂ : IsForcingPreorder P₂ R₂) (t₂ : IsForcingTop P₂ R₂ one₂) {G : Set V}
  (hG : IsExternalForcingGeneric (P₁ ×ˢ P₂) (productOrder P₁ R₁ P₂ R₂) G)

/-- The ground model inside the two-step extension `V[G₁][G₂]`. -/
noncomputable def productGround :
    MembershipEndExtension V (secondFactorContext h₁ t₁ h₂ t₂ hG).Model :=
  (firstFactorContext h₁ t₁ h₂ hG).checkEmbedding.trans (secondFactorContext h₁ t₁ h₂ t₂ hG).checkEmbedding

theorem productGround_apply (x : V) :
    productGround h₁ t₁ h₂ t₂ hG x =
      (secondFactorContext h₁ t₁ h₂ t₂ hG).check ((firstFactorContext h₁ t₁ h₂ hG).check x) :=
  rfl

/-- The generic `G` recovered inside `V[G₁][G₂]`: pairs whose first coordinate lies in `G₁` and
whose second coordinate lies in `G₂`. -/
noncomputable def productRecoveredGeneric : (secondFactorContext h₁ t₁ h₂ t₂ hG).Model :=
  sep (productGround h₁ t₁ h₂ t₂ hG (P₁ ×ˢ P₂))
    (fun x ↦ (productGround h₁ t₁ h₂ t₂ hG (firstProjection P₁ P₂)) ‘ x ∈
        (secondFactorContext h₁ t₁ h₂ t₂ hG).check (firstFactorContext h₁ t₁ h₂ hG).genericSet ∧
      (productGround h₁ t₁ h₂ t₂ hG (secondProjection P₁ P₂)) ‘ x ∈
        (secondFactorContext h₁ t₁ h₂ t₂ hG).genericSet)
    (by definability)

include h₁ t₂ hG in
theorem one₂_mem_secondProjection : one₂ ∈ secondProjectionGeneric G := by
  obtain ⟨z, hz⟩ := hG.1.2.1
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (hG.1.1 z hz)
  exact ⟨p, hG.1.2.2.1 _ hz _ (kpair_mem_iff.mpr ⟨hp, t₂.1⟩)
    ((pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp, hq, hp, t₂.1, h₁.2.1 p hp, t₂.2 q hq⟩)⟩

include t₁ h₂ hG in
theorem one₁_mem_firstProjection : one₁ ∈ firstProjectionGeneric G := by
  obtain ⟨z, hz⟩ := hG.1.2.1
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (hG.1.1 z hz)
  exact ⟨q, hG.1.2.2.1 _ hz _ (kpair_mem_iff.mpr ⟨t₁.1, hq⟩)
    ((pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp, hq, t₁.1, hq, t₁.2 p hp, h₂.2.1 q hq⟩)⟩

theorem productGround_value_first {p q : V} (hp : p ∈ P₁) (hq : q ∈ P₂) :
    (productGround h₁ t₁ h₂ t₂ hG (firstProjection P₁ P₂)) ‘ (productGround h₁ t₁ h₂ t₂ hG ⟨p, q⟩ₖ) =
      productGround h₁ t₁ h₂ t₂ hG p := by
  rw [← (productGround h₁ t₁ h₂ t₂ hG).map_value_total]
  unfold firstProjection
  rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hp, hq⟩), kpair.π₁_kpair]

theorem productGround_value_second {p q : V} (hp : p ∈ P₁) (hq : q ∈ P₂) :
    (productGround h₁ t₁ h₂ t₂ hG (secondProjection P₁ P₂)) ‘ (productGround h₁ t₁ h₂ t₂ hG ⟨p, q⟩ₖ) =
      productGround h₁ t₁ h₂ t₂ hG q := by
  rw [← (productGround h₁ t₁ h₂ t₂ hG).map_value_total]
  unfold secondProjection
  rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hp, hq⟩), kpair.π₂_kpair]

theorem productGround_mem_recovered_iff (z : V) :
    productGround h₁ t₁ h₂ t₂ hG z ∈ productRecoveredGeneric h₁ t₁ h₂ t₂ hG ↔ z ∈ G := by
  let C := firstFactorContext h₁ t₁ h₂ hG
  let Q := secondFactorContext h₁ t₁ h₂ t₂ hG
  unfold productRecoveredGeneric
  rw [mem_sep_iff, (productGround h₁ t₁ h₂ t₂ hG).mem_iff]
  constructor
  · rintro ⟨hz, hfst, hsnd⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    rw [productGround_value_first h₁ t₁ h₂ t₂ hG hp hq, productGround_apply, Q.check_mem_iff,
      C.check_mem_genericSet_iff] at hfst
    rw [productGround_value_second h₁ t₁ h₂ t₂ hG hp hq, productGround_apply, Q.check_mem_genericSet_iff] at hsnd
    exact (pair_mem_product_generic_iff h₁ h₂ hG p q).mpr
      ⟨hfst, (check_mem_secondFactorGeneric_iff h₁ t₁ h₂ hG q).mp hsnd⟩
  · intro hzG
    have hz := hG.1.1 z hzG
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨h1, h2⟩ := (pair_mem_product_generic_iff h₁ h₂ hG p q).mp hzG
    refine ⟨hz, ?_, ?_⟩
    · rw [productGround_value_first h₁ t₁ h₂ t₂ hG hp hq, productGround_apply, Q.check_mem_iff,
        C.check_mem_genericSet_iff]
      exact h1
    · rw [productGround_value_second h₁ t₁ h₂ t₂ hG hp hq, productGround_apply, Q.check_mem_genericSet_iff]
      exact (check_mem_secondFactorGeneric_iff h₁ t₁ h₂ hG q).mpr h2

/-- `V[G]` realized inside `V[G₁][G₂]`. -/
noncomputable def productRealization :
    ForcingRealization (productContext h₁ t₁ h₂ t₂ hG) (secondFactorContext h₁ t₁ h₂ t₂ hG).Model where
  ground := productGround h₁ t₁ h₂ t₂ hG
  genericSet := productRecoveredGeneric h₁ t₁ h₂ t₂ hG
  generic_subset := fun x hx ↦ (mem_sep_iff.mp hx).1
  generic_mem := productGround_mem_recovered_iff h₁ t₁ h₂ t₂ hG

include t₂ in
/-- Names over the first factor lifted to the product. -/
noncomputable def productNameLift (τ : ForcingName (firstFactorContext h₁ t₁ h₂ hG).P) :
    ForcingName (productContext h₁ t₁ h₂ t₂ hG).P :=
  ⟨nameAction (leftEmbedding P₁ one₂) τ.val, nameAction_isName (leftEmbedding_mem_function t₂.1) τ.property⟩

/-- Elements of the check of `G₁` in `V[G₁][G₂]`. -/
theorem mem_check_firstGeneric_iff (x : (secondFactorContext h₁ t₁ h₂ t₂ hG).Model) :
    x ∈ (secondFactorContext h₁ t₁ h₂ t₂ hG).check (firstFactorContext h₁ t₁ h₂ hG).genericSet ↔
      ∃ p ∈ firstProjectionGeneric G, x = productGround h₁ t₁ h₂ t₂ hG p := by
  let C := firstFactorContext h₁ t₁ h₂ hG
  let Q := secondFactorContext h₁ t₁ h₂ t₂ hG
  rw [Q.mem_check_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨p, hp, rfl⟩ := (C.mem_genericSet_iff y).mp hy
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨C.check p, (C.check_mem_genericSet_iff p).mpr hp, rfl⟩

theorem productRecovered_inter_range_eq :
    productRecoveredGeneric h₁ t₁ h₂ t₂ hG ∩ range (productGround h₁ t₁ h₂ t₂ hG (leftEmbedding P₁ one₂)) =
      range ((productGround h₁ t₁ h₂ t₂ hG (leftEmbedding P₁ one₂)) ↾
        ((secondFactorContext h₁ t₁ h₂ t₂ hG).check (firstFactorContext h₁ t₁ h₂ hG).genericSet)) := by
  have hone₂ := one₂_mem_secondProjection h₁ t₂ hG
  have hGmem := mem_check_firstGeneric_iff h₁ t₁ h₂ t₂ hG
  have hrec := productGround_mem_recovered_iff h₁ t₁ h₂ t₂ hG
  have hinj := (productGround h₁ t₁ h₂ t₂ hG).injective
  apply mem_ext
  intro z
  rw [mem_inter_iff, mem_range_iff, mem_range_iff]
  constructor
  · rintro ⟨hz, x, hxz⟩
    obtain ⟨a, b, hab, rfl, rfl⟩ := ((productGround h₁ t₁ h₂ t₂ hG).pair_mem_image_iff _ _ _).mp hxz
    obtain ⟨ha, rfl⟩ := (pair_mem_leftEmbedding_iff _ _ _ _).mp hab
    have haG : a ∈ firstProjectionGeneric G :=
      ((pair_mem_product_generic_iff h₁ h₂ hG a one₂).mp ((hrec _).mp hz)).1
    exact ⟨_, kpair_mem_restrict_iff.mpr ⟨hxz, (hGmem _).mpr ⟨a, haG, rfl⟩⟩⟩
  · rintro ⟨x, hxz⟩
    obtain ⟨hxz, hxG⟩ := kpair_mem_restrict_iff.mp hxz
    obtain ⟨a, b, hab, rfl, rfl⟩ := ((productGround h₁ t₁ h₂ t₂ hG).pair_mem_image_iff _ _ _).mp hxz
    obtain ⟨ha, rfl⟩ := (pair_mem_leftEmbedding_iff _ _ _ _).mp hab
    obtain ⟨p, hp, hpa⟩ := (hGmem _).mp hxG
    have : a = p := hinj hpa
    subst this
    exact ⟨(hrec _).mpr ((pair_mem_product_generic_iff h₁ h₂ hG a one₂).mpr ⟨hp, hone₂⟩), _, hxz⟩

theorem productRealization_value_lift (τ : ForcingName (firstFactorContext h₁ t₁ h₂ hG).P) :
    (productRealization h₁ t₁ h₂ t₂ hG).value
        ((productContext h₁ t₁ h₂ t₂ hG).ofName (productNameLift h₁ t₁ h₂ t₂ hG τ)) =
      (secondFactorContext h₁ t₁ h₂ t₂ hG).check ((firstFactorContext h₁ t₁ h₂ hG).ofName τ) := by
  let C := firstFactorContext h₁ t₁ h₂ hG
  let Q := secondFactorContext h₁ t₁ h₂ t₂ hG
  let j := productGround h₁ t₁ h₂ t₂ hG
  have he := leftEmbedding_mem_function (P₁ := P₁) (P₂ := P₂) t₂.1
  rw [ForcingRealization.value_ofName, ← C.nameValue_genericSet_check τ]
  change nameValue (productRecoveredGeneric h₁ t₁ h₂ t₂ hG) (j (nameAction (leftEmbedding P₁ one₂) τ.val)) =
    Q.checkEmbedding (nameValue C.genericSet (C.check τ.val))
  rw [Q.checkEmbedding.map_nameValue, j.map_nameAction]
  change nameValue (productRecoveredGeneric h₁ t₁ h₂ t₂ hG)
      (nameAction (j (leftEmbedding P₁ one₂)) (j τ.val)) =
    nameValue (Q.check C.genericSet) (j τ.val)
  -- the lifted name lives over the range of the embedding
  have hπ : j (leftEmbedding P₁ one₂) ∈ (j (P₁ ×ˢ P₂)) ^ (j P₁) := (j.function_iff _ _ _).mpr he
  have hπinj : Injective (j (leftEmbedding P₁ one₂)) := (j.injective_iff _).mpr (leftEmbedding_injective P₁ one₂)
  have hjdom : domain (j (leftEmbedding P₁ one₂)) = j P₁ := domain_eq_of_mem_function hπ
  have : IsFunction (j (leftEmbedding P₁ one₂)) := IsFunction.of_mem hπ
  have hπ' : j (leftEmbedding P₁ one₂) ∈ (range (j (leftEmbedding P₁ one₂))) ^ (j P₁) := by
    have := IsFunction.mem_function (j (leftEmbedding P₁ one₂))
    rwa [hjdom] at this
  have hG' : Q.check C.genericSet ⊆ j P₁ := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (mem_check_firstGeneric_iff h₁ t₁ h₂ t₂ hG x).mp hx
    exact (j.mem_iff _ _).mpr ((firstProjection_generic h₁ h₂ hG).1.1 p hp)
  have hτ : IsForcingName (j P₁) (j τ.val) := j.map_forcingName τ.property
  have hN : IsForcingName (range (j (leftEmbedding P₁ one₂)))
      (nameAction (j (leftEmbedding P₁ one₂)) (j τ.val)) := nameAction_isName hπ' hτ
  rw [← nameValue_nameAction hπ hπinj hG' hτ, ← nameValue_inter_of_name hN,
    productRecovered_inter_range_eq h₁ t₁ h₂ t₂ hG]

/-- The generator of the second generic inside `V[G]`: the conditions `q` with `⟨1, q⟩ ∈ G`. -/
noncomputable def secondGenericGenerator : (productContext h₁ t₁ h₂ t₂ hG).Model :=
  sep ((productContext h₁ t₁ h₂ t₂ hG).check P₂)
    (fun z ↦ ⟨(productContext h₁ t₁ h₂ t₂ hG).check one₁, z⟩ₖ ∈ (productContext h₁ t₁ h₂ t₂ hG).genericSet)
    (by definability)

theorem productRealization_value_generator :
    (productRealization h₁ t₁ h₂ t₂ hG).value (secondGenericGenerator h₁ t₁ h₂ t₂ hG) =
      (secondFactorContext h₁ t₁ h₂ t₂ hG).genericSet := by
  let A := productContext h₁ t₁ h₂ t₂ hG
  let C := firstFactorContext h₁ t₁ h₂ hG
  let Q := secondFactorContext h₁ t₁ h₂ t₂ hG
  let L := productRealization h₁ t₁ h₂ t₂ hG
  have hone₁ := one₁_mem_firstProjection t₁ h₂ hG
  unfold secondGenericGenerator
  have hsep := L.embedding.map_separation (A.check P₂)
    (fun z ↦ ⟨A.check one₁, z⟩ₖ ∈ A.genericSet)
    (fun z ↦ ⟨L.value (A.check one₁), z⟩ₖ ∈ L.value A.genericSet) (by definability) (by definability)
    (by
      intro x _
      show ⟨A.check one₁, x⟩ₖ ∈ A.genericSet ↔ ⟨L.embedding (A.check one₁), L.embedding x⟩ₖ ∈ L.embedding A.genericSet
      rw [← L.embedding.map_kpair]
      exact (L.embedding.mem_iff _ _).symm)
  change L.embedding _ = _
  rw [hsep]
  apply mem_ext
  intro z
  rw [mem_sep_iff]
  change z ∈ L.value (A.check P₂) ∧ ⟨L.value (A.check one₁), z⟩ₖ ∈ L.value A.genericSet ↔ _
  rw [L.value_check, L.value_check, L.value_genericSet]
  change z ∈ productGround h₁ t₁ h₂ t₂ hG P₂ ∧
    ⟨productGround h₁ t₁ h₂ t₂ hG one₁, z⟩ₖ ∈ productRecoveredGeneric h₁ t₁ h₂ t₂ hG ↔ z ∈ Q.genericSet
  constructor
  · rintro ⟨hz, hpair⟩
    obtain ⟨q, hq, rfl⟩ := (productGround h₁ t₁ h₂ t₂ hG).endExtension _ z hz
    rw [← (productGround h₁ t₁ h₂ t₂ hG).map_kpair, productGround_mem_recovered_iff] at hpair
    have hq₂ := ((pair_mem_product_generic_iff h₁ h₂ hG one₁ q).mp hpair).2
    rw [productGround_apply, Q.check_mem_genericSet_iff]
    exact (check_mem_secondFactorGeneric_iff h₁ t₁ h₂ hG q).mpr hq₂
  · intro hz
    obtain ⟨y, hy, rfl⟩ := (Q.mem_genericSet_iff z).mp hz
    obtain ⟨q, hq, rfl⟩ := hy
    have hqP : q ∈ P₂ := (secondFactorGeneric_filter h₁ t₁ h₂ hG).1 _ ⟨q, hq, rfl⟩ |> (C.check_mem_iff _ _).mp
    refine ⟨(productGround h₁ t₁ h₂ t₂ hG).mem_iff q P₂ |>.mpr hqP, ?_⟩
    rw [← productGround_apply h₁ t₁ h₂ t₂ hG q, ← (productGround h₁ t₁ h₂ t₂ hG).map_kpair,
      productGround_mem_recovered_iff]
    exact (pair_mem_product_generic_iff h₁ h₂ hG one₁ q).mpr ⟨hone₁, hq⟩

theorem productRealization_surjective : Function.Surjective (productRealization h₁ t₁ h₂ t₂ hG).value :=
  ForcingRealization.value_surjective_of_generators (secondFactorContext h₁ t₁ h₂ t₂ hG)
    (productRealization h₁ t₁ h₂ t₂ hG)
    (fun x ↦ by
      obtain ⟨τ, rfl⟩ := (firstFactorContext h₁ t₁ h₂ hG).ofName_surjective x
      exact ⟨_, productRealization_value_lift h₁ t₁ h₂ t₂ hG τ⟩)
    ⟨_, productRealization_value_generator h₁ t₁ h₂ t₂ hG⟩

/-- The product factorization `V[G] ≃ V[G₁][G₂]`. -/
noncomputable def productEquiv :
    (productContext h₁ t₁ h₂ t₂ hG).Model ≃ (secondFactorContext h₁ t₁ h₂ t₂ hG).Model :=
  Equiv.ofBijective (productRealization h₁ t₁ h₂ t₂ hG).value
    ⟨(productRealization h₁ t₁ h₂ t₂ hG).value_injective, productRealization_surjective h₁ t₁ h₂ t₂ hG⟩

theorem productEquiv_mem_iff (x y : (productContext h₁ t₁ h₂ t₂ hG).Model) :
    productEquiv h₁ t₁ h₂ t₂ hG x ∈ productEquiv h₁ t₁ h₂ t₂ hG y ↔ x ∈ y :=
  (productRealization h₁ t₁ h₂ t₂ hG).value_mem_iff x y

theorem productEquiv_check (x : V) :
    productEquiv h₁ t₁ h₂ t₂ hG ((productContext h₁ t₁ h₂ t₂ hG).check x) =
      (secondFactorContext h₁ t₁ h₂ t₂ hG).check ((firstFactorContext h₁ t₁ h₂ hG).check x) :=
  (productRealization h₁ t₁ h₂ t₂ hG).value_check x

theorem productEquiv_lift (τ : ForcingName (firstFactorContext h₁ t₁ h₂ hG).P) :
    productEquiv h₁ t₁ h₂ t₂ hG ((productContext h₁ t₁ h₂ t₂ hG).ofName (productNameLift h₁ t₁ h₂ t₂ hG τ)) =
      (secondFactorContext h₁ t₁ h₂ t₂ hG).check ((firstFactorContext h₁ t₁ h₂ hG).ofName τ) :=
  productRealization_value_lift h₁ t₁ h₂ t₂ hG τ

end

end ZFVP
