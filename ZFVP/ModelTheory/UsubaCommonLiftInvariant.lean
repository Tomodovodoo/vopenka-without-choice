import ZFVP.ModelTheory.UsubaBoundInvariant
import ZFVP.ModelTheory.UsubaTowerLifts

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

attribute [local instance] DefinableForcingTower.P_definable DefinableForcingTower.R_definable
  DefinableForcingTower.projection_definable

def IsUsubaCommonLiftBoundAt (θ i p f c d j : V) : Prop :=
  i ⊆ j → ∀ r ∈ (T).P j,
    ⟨r, usubaQuotientBoundRec θ i p f j⟩ₖ ∈ (T).R j →
    ∀ b ∈ (T).P i, ⟨b, ((T).projection i j) ‘ r⟩ₖ ∈ (T).R i →
      ⟨b, d⟩ₖ ∈ (T).R i →
      ⟨(usubaTowerLift i j) ‘ ⟨r, b⟩ₖ, ((T).projection j θ) ‘ c⟩ₖ ∈ (T).R j

instance isUsubaCommonLiftBoundAt_definable (θ i p f c d : V) :
    ℒₛₑₜ-predicate[V] (IsUsubaCommonLiftBoundAt θ i p f c d) := by
  unfold IsUsubaCommonLiftBoundAt
  definability

theorem usubaCommonLiftBoundAt_before {θ i p f c d j : V} [IsOrdinal i]
    (hj : j ∈ i) : IsUsubaCommonLiftBoundAt θ i p f c d j := by
  intro hij
  exact (mem_irrefl j (hij j hj)).elim

theorem usubaCommonLiftBoundAt_base {θ i p f c d : V} [IsOrdinal θ] [IsOrdinal i]
    (hiθ : i ⊆ θ) (hc : c ∈ (T).P θ) (hd : d ∈ (T).P i)
    (hdc : ⟨d, ((T).projection i θ) ‘ c⟩ₖ ∈ (T).R i) :
    IsUsubaCommonLiftBoundAt θ i p f c d i := by
  intro hii r hr _ b hb hbr hbd
  have hl := usubaTowerLift_spec hii hr hb hbr
  have he := ((T).projection_self i inferInstance _ hl.1).symm.trans hl.2.2
  rw [he]
  exact ((T).order i inferInstance).2.2 b hb d hd _ ((T).projection_mem hiθ hc) hbd hdc

theorem usubaCommonLift_project_le {θ i p f c d j r b k : V}
    [IsOrdinal θ] [IsOrdinal i] [IsOrdinal j] [IsOrdinal k]
    (hjθ : j ⊆ θ) (hi : i ∈ j) (hk : k ∈ j)
    (hc : c ∈ (T).P θ) (hd : d ∈ (T).P i)
    (hdc : ⟨d, ((T).projection i θ) ‘ c⟩ₖ ∈ (T).R i)
    (hq : usubaQuotientBoundRec θ i p f j ∈ (T).P j)
    (hproj : ((T).projection k j) ‘ (usubaQuotientBoundRec θ i p f j) =
      usubaQuotientBoundRec θ i p f k)
    (hprev : IsUsubaCommonLiftBoundAt θ i p f c d k)
    (hr : r ∈ (T).P j) (hrq : ⟨r, usubaQuotientBoundRec θ i p f j⟩ₖ ∈ (T).R j)
    (hb : b ∈ (T).P i) (hbr : ⟨b, ((T).projection i j) ‘ r⟩ₖ ∈ (T).R i)
    (hbd : ⟨b, d⟩ₖ ∈ (T).R i) :
    ⟨((T).projection k j) ‘ ((usubaTowerLift i j) ‘ ⟨r, b⟩ₖ),
      ((T).projection k θ) ‘ c⟩ₖ ∈ (T).R k := by
  have hij : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hi
  have hkj : k ⊆ j := IsOrdinal.toIsTransitive.transitive _ hk
  by_cases hki : k ∈ i
  · have hki' : k ⊆ i := IsOrdinal.toIsTransitive.transitive _ hki
    have hl := usubaTowerLift_spec hij hr hb hbr
    rw [← (T).projection_comp k i j inferInstance inferInstance inferInstance hki' hij _ hl.1, hl.2.2]
    have hci := (T).projection_mem (subset_trans hij hjθ) hc
    have hbc := ((T).order i inferInstance).2.2 b hb d hd _ hci hbd hdc
    have hh := (T).projection_mono k i inferInstance inferInstance hki' b hb _ hci hbc
    rwa [(T).projection_comp k i θ inferInstance inferInstance inferInstance hki' (subset_trans hij hjθ) c hc] at hh
  · have hik : i ⊆ k := by
      rcases IsOrdinal.mem_trichotomy k i with hki' | he | hik
      · exact (hki hki').elim
      · subst k; exact subset_refl _
      · exact IsOrdinal.toIsTransitive.transitive _ hik
    rw [usubaTowerLift_commute hik hkj hr hb hbr]
    apply hprev hik _ ((T).projection_mem hkj hr) ?_ b hb ?_ hbd
    · have hh := (T).projection_mono k j inferInstance inferInstance hkj r hr _ hq hrq
      rwa [hproj] at hh
    · rwa [(T).projection_comp i k j inferInstance inferInstance inferInstance hik hkj r hr]

end ZFVP
