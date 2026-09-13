import ZFVP.SetTheory.WoodinCollapseCones
import ZFVP.SetTheory.ForcingIsomorphism

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinCollapseCone (κ δ p : V) : V := {r ∈ woodinCollapse κ δ ; p ⊆ r}

theorem mem_woodinCollapseCone (κ δ p r : V) :
    r ∈ woodinCollapseCone κ δ p ↔ r ∈ woodinCollapse κ δ ∧ p ⊆ r := mem_sep_iff

instance woodinCollapseCone_definable : ℒₛₑₜ-function₃[V] woodinCollapseCone := by
  have h : ℒₛₑₜ-relation₄[V] (fun C κ δ p ↦ ∀ r, r ∈ C ↔ r ∈ woodinCollapse κ δ ∧ p ⊆ r) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_woodinCollapseCone]
  rfl

theorem woodinCollapseCone_iff_stronger {κ δ p r : V} (hp : p ∈ woodinCollapse κ δ) :
    r ∈ woodinCollapseCone κ δ p ↔ ⟨r, p⟩ₖ ∈ woodinCollapseOrder κ δ := by
  rw [mem_woodinCollapseCone, woodinCollapseOrder, pair_mem_reverseInclusionOrder]
  simp only [hp, true_and]

theorem woodinCollapseCone_poset (κ δ p : V) :
    IsForcingPoset (woodinCollapseCone κ δ p) (reverseInclusionOrder (woodinCollapseCone κ δ p)) :=
  reverseInclusionOrder_poset _

theorem woodinCollapse_cone_isomorphic {κ δ p q : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hq : q ∈ woodinCollapse κ δ) :
    ∃ f, IsForcingIsomorphism (woodinCollapseCone κ δ p)
      (reverseInclusionOrder (woodinCollapseCone κ δ p))
      (woodinCollapseCone κ δ q) (reverseInclusionOrder (woodinCollapseCone κ δ q)) f := by
  let F : V → V := fun r ↦ collapseConeEncode κ δ q (collapseConeDecode κ δ p r)
  let G : V → V := fun r ↦ collapseConeEncode κ δ p (collapseConeDecode κ δ q r)
  have hF : ℒₛₑₜ-function₁ F := by
    unfold F collapseConeEncode collapseConeDecode
    definability
  have hFP : ∀ r ∈ woodinCollapseCone κ δ p, F r ∈ woodinCollapseCone κ δ q := by
    intro r hr
    exact (mem_woodinCollapseCone _ _ _ _).mpr
      ⟨collapseConeEncode_condition hκ hq
        (collapseConeDecode_condition hκ hp ((mem_woodinCollapseCone _ _ _ _).mp hr).1),
        collapseConeEncode_extends _ _ _ _⟩
  have hGQ : ∀ r ∈ woodinCollapseCone κ δ q, G r ∈ woodinCollapseCone κ δ p := by
    intro r hr
    exact (mem_woodinCollapseCone _ _ _ _).mpr
      ⟨collapseConeEncode_condition hκ hp
        (collapseConeDecode_condition hκ hq ((mem_woodinCollapseCone _ _ _ _).mp hr).1),
        collapseConeEncode_extends _ _ _ _⟩
  have hGF : ∀ r ∈ woodinCollapseCone κ δ p, G (F r) = r := by
    intro r hr
    have hr' := (mem_woodinCollapseCone _ _ _ _).mp hr
    dsimp [F, G]
    rw [collapseConeDecode_encode hκ hq (collapseConeDecode_condition hκ hp hr'.1),
      collapseConeEncode_decode hκ hp hr'.1 hr'.2]
  have hFG : ∀ r ∈ woodinCollapseCone κ δ q, F (G r) = r := by
    intro r hr
    have hr' := (mem_woodinCollapseCone _ _ _ _).mp hr
    dsimp [F, G]
    rw [collapseConeDecode_encode hκ hp (collapseConeDecode_condition hκ hq hr'.1),
      collapseConeEncode_decode hκ hq hr'.1 hr'.2]
  exact ⟨definableGraph _ F hF, reverseInclusion_isomorphism_of_inverse F G hF hFP hGQ hGF hFG
    (fun _ _ _ _ h ↦ collapseConeEncode_mono (collapseConeDecode_mono h))
    (fun _ _ _ _ h ↦ collapseConeEncode_mono (collapseConeDecode_mono h))⟩

end ZFVP
