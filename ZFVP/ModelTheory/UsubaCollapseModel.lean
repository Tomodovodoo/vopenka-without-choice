import ZFVP.SetTheory.UsubaCollapse
import ZFVP.ModelTheory.ForcingQuotientGeneric
import ZFVP.ModelTheory.ForcingClosedCardinals
import ZFVP.ModelTheory.ForcingDependentChoiceTransfer

/-! The generic union for Usuba's `Col(κ,S)` is a surjection `κ → S`.
Under `DC_<κ` the forcing adds no shorter sequences of ground-model
elements and preserves regularity of `κ`. These are the collapse and
closure parts of Usuba Proposition 4.7; the LS-dependent `DC_κ` conclusion
requires its separate elementary-hull argument. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def usubaCollapseContext {κ : V} (hκ : IsRegularCardinal κ)
    (S : V) (G : Set V)
    (hG : IsExternalForcingGeneric (usubaCollapse κ S) (usubaCollapseOrder κ S) G) :
    ForcingContext V :=
  ⟨usubaCollapse κ S, usubaCollapseOrder κ S, ∅, G,
    (usubaCollapse_poset κ S).1,
    usubaCollapse_top (hκ.2.1 ∅ (by simp)) S, hG⟩

namespace UsubaCollapseModel

variable {κ S : V} (hκ : IsRegularCardinal κ) {G : Set V}
  (hG : IsExternalForcingGeneric (usubaCollapse κ S) (usubaCollapseOrder κ S) G)

noncomputable def genericSet : (usubaCollapseContext hκ S G hG).Model :=
  forcingGenericSet _ _ G (usubaCollapse_poset κ S).1 hG.1 ∅
    (usubaCollapse_top (hκ.2.1 ∅ (by simp)) S)

theorem mem_genericSet (x : (usubaCollapseContext hκ S G hG).Model) :
    x ∈ genericSet hκ hG ↔
      ∃ p ∈ G, x = (usubaCollapseContext hκ S G hG).check p :=
  forcingGenericSet_mem_iff _ _ G (usubaCollapse_poset κ S).1 hG ∅
    (usubaCollapse_top (hκ.2.1 ∅ (by simp)) S) x

noncomputable def genericFunction : (usubaCollapseContext hκ S G hG).Model :=
  ⋃ˢ genericSet hκ hG

theorem mem_genericFunction (x : (usubaCollapseContext hκ S G hG).Model) :
    x ∈ genericFunction hκ hG ↔
      ∃ p ∈ G, x ∈ (usubaCollapseContext hκ S G hG).check p := by
  simp only [genericFunction, mem_sUnion_iff, mem_genericSet]
  constructor
  · rintro ⟨y, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨_, ⟨p, hp, rfl⟩, hx⟩

instance genericFunction_isFunction : IsFunction (genericFunction hκ hG) := by
  let A := usubaCollapseContext hκ S G hG
  have hfun (p : V) (hp : p ∈ G) : IsFunction (A.check p) := by
    let := ((mem_usubaCollapse _ _ _).mp (hG.1.1 p hp)).2.1
    exact A.check_isFunction p
  apply isFunction_sUnion
  · intro f hf
    obtain ⟨p, hp, rfl⟩ := (mem_genericSet hκ hG f).mp hf
    exact hfun p hp
  · intro f hf g hg x y z hxy hxz
    obtain ⟨p, hp, rfl⟩ := (mem_genericSet hκ hG f).mp hf
    obtain ⟨q, hq, rfl⟩ := (mem_genericSet hκ hG g).mp hg
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
    have hpr : p ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2
    have hqr : q ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2
    let := hfun r hr
    exact IsFunction.unique (f := A.check r)
      ((A.checkEmbedding.subset_iff p r).mpr hpr _ hxy)
      ((A.checkEmbedding.subset_iff q r).mpr hqr _ hxz)

theorem genericFunction_mem_function (hS : IsNonempty S) :
    genericFunction hκ hG ∈
      (usubaCollapseContext hκ S G hG).check S ^
        (usubaCollapseContext hκ S G hG).check κ := by
  let A := usubaCollapseContext hκ S G hG
  apply mem_function.intro
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := (mem_genericFunction hκ hG z).mp hz
    have hpsub := ((mem_usubaCollapse _ _ _).mp (hG.1.1 p hp)).1
    have hh := (A.checkEmbedding.subset_iff p (κ ×ˢ S)).mpr hpsub z hzp
    change z ∈ A.check (κ ×ˢ S) at hh
    rwa [show A.check (κ ×ˢ S) = A.check κ ×ˢ A.check S from
      A.checkEmbedding.map_prod κ S] at hh
  · intro x hx
    obtain ⟨α, hα, rfl⟩ := (A.mem_check_iff κ x).mp hx
    obtain ⟨p, hpG, hp⟩ := hG.2 _ (usubaCollapse_domain_dense hκ hS hα)
    obtain ⟨s, hs⟩ := mem_domain_iff.mp (mem_sep_iff.mp hp).2
    have hpair : ⟨A.check α, A.check s⟩ₖ ∈ genericFunction hκ hG := by
      apply (mem_genericFunction hκ hG _).mpr
      refine ⟨p, hpG, ?_⟩
      rw [← A.check_kpair, A.check_mem_iff]
      exact hs
    exact ⟨A.check s, hpair, fun _ h ↦ IsFunction.unique h hpair⟩

theorem genericFunction_range (hS : IsNonempty S) :
    range (genericFunction hκ hG) = (usubaCollapseContext hκ S G hG).check S := by
  let A := usubaCollapseContext hκ S G hG
  apply SetTheory.subset_antisymm
    (range_subset_of_mem_function (genericFunction_mem_function hκ hG hS))
  intro x hx
  obtain ⟨s, hs, rfl⟩ := (A.mem_check_iff S x).mp hx
  obtain ⟨p, hpG, hp⟩ := hG.2 _ (usubaCollapse_range_dense hκ hs)
  obtain ⟨α, hα⟩ := mem_range_iff.mp (mem_sep_iff.mp hp).2
  apply mem_range_of_kpair_mem (x := A.check α)
  apply (mem_genericFunction hκ hG _).mpr
  refine ⟨p, hpG, ?_⟩
  rw [← A.check_kpair, A.check_mem_iff]
  exact hα

theorem check_wellOrderable (hS : IsNonempty S) :
    IsWellOrderable ((usubaCollapseContext hκ S G hG).check S) := by
  let := hκ.1.1
  exact wellOrderable_of_surjective_function
    (ordinal_wellOrderable ((usubaCollapseContext hκ S G hG).check κ))
    (genericFunction_mem_function hκ hG hS) (genericFunction_range hκ hG hS)

theorem shortFunction_eq_check
    (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ)
    {γ X : V} (hγ : γ ∈ κ) {z : (usubaCollapseContext hκ S G hG).Model}
    (hz : z ∈ (usubaCollapseContext hκ S G hG).check X ^
      (usubaCollapseContext hκ S G hG).check γ) :
    ∃ f ∈ X ^ γ, (usubaCollapseContext hκ S G hG).check f = z := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  apply ForcingContext.function_eq_check_of_closed _ (hDC γ hγ) ?_ hz
  intro α hα hαγ
  let := hα
  have hακ : α ∈ κ := ordinal_mem_of_subset_mem hαγ hγ
  exact usubaCollapse_closedAt hκ hακ (hDC α hακ)

theorem check_regular (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ) :
    IsRegularCardinal ((usubaCollapseContext hκ S G hG).check κ) :=
  ForcingContext.check_regular_of_closed _ hκ hDC (usubaCollapse_closedBelow hκ hDC S)

theorem shortDependentChoice
    (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ) {γ : V} (hγ : γ ∈ κ) :
    InternalDependentChoiceAt ((usubaCollapseContext hκ S G hG).check γ) := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  apply ForcingContext.dependentChoiceAt_of_closed _ (hDC γ hγ)
  intro α hα hαγ
  let := hα
  have hακ : α ∈ κ := ordinal_mem_of_subset_mem hαγ hγ
  exact usubaCollapse_closedAt hκ hακ (hDC α hακ)

theorem dependentChoice_below (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ) :
    ∀ γ ∈ (usubaCollapseContext hκ S G hG).check κ, InternalDependentChoiceAt γ := by
  intro γ hγ
  obtain ⟨α, hα, rfl⟩ :=
    ((usubaCollapseContext hκ S G hG).mem_check_iff κ γ).mp hγ
  exact shortDependentChoice hκ hG hDC hα

end UsubaCollapseModel
end ZFVP
