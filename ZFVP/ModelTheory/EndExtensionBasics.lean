import ZFVP.SetTheory.MembershipEndExtension
import ZFVP.SetTheory.Rank
import ZFVP.SetTheory.VopenkaScheme

/-! Basic vocabulary for the dead-end models used in Proposition
`prop:countability-essential`: proper end extensions, powerset-preserving and rank
end extensions, the property of having no proper end extension to a model of ZF, and the
transfer of the Vopenka scheme along an elementary map. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W U : Type*} [SetStructure V] [SetStructure W] [SetStructure U]

/-- The identity is an end extension of a model by itself. -/
def refl (V : Type*) [SetStructure V] : MembershipEndExtension V V where
  toFun := id
  injective := fun _ _ h ↦ h
  mem_iff _ _ := Iff.rfl
  endExtension _ y hy := ⟨y, hy, rfl⟩

@[simp] theorem refl_apply (x : V) : refl V x = x := rfl

/-- End extensions compose. -/
def trans (j : MembershipEndExtension V W) (k : MembershipEndExtension W U) :
    MembershipEndExtension V U where
  toFun := k ∘ j
  injective := k.injective.comp j.injective
  mem_iff x y := (k.mem_iff (j x) (j y)).trans (j.mem_iff x y)
  endExtension x y hy := by
    obtain ⟨w, hw, rfl⟩ := k.endExtension (j x) y hy
    obtain ⟨v, hv, rfl⟩ := j.endExtension x w hw
    exact ⟨v, hv, rfl⟩

@[simp] theorem trans_apply (j : MembershipEndExtension V W) (k : MembershipEndExtension W U)
    (x : V) : j.trans k x = k (j x) := rfl

/-- The members of `j x` are exactly the images of the members of `x`. -/
theorem mem_map_iff (j : MembershipEndExtension V W) (x : V) (y : W) :
    y ∈ j x ↔ ∃ z ∈ x, y = j z := by
  constructor
  · exact j.endExtension x y
  · rintro ⟨z, hz, rfl⟩
    exact (j.mem_iff z x).mpr hz

/-- Inclusion between images reflects inclusion. -/
theorem map_subset_iff (j : MembershipEndExtension V W) (x y : V) : j x ⊆ j y ↔ x ⊆ y := by
  constructor
  · intro h z hz
    exact (j.mem_iff z y).mp (h _ ((j.mem_iff z x).mpr hz))
  · intro h z hz
    obtain ⟨w, hw, rfl⟩ := j.endExtension x z hz
    exact (j.mem_iff w y).mpr (h _ hw)

/-- A proper end extension: some element of the larger model is new. -/
def IsProper (j : MembershipEndExtension V W) : Prop := ∃ w : W, ∀ v : V, j v ≠ w

theorem isProper_iff_not_surjective (j : MembershipEndExtension V W) :
    j.IsProper ↔ ¬ Function.Surjective j.toFun := by
  constructor
  · rintro ⟨w, hw⟩ hs
    obtain ⟨v, rfl⟩ := hs w
    exact hw v rfl
  · intro h
    by_contra hp
    exact h fun w ↦ by
      by_contra hv
      exact hp ⟨w, fun v hvw ↦ hv ⟨v, hvw⟩⟩

@[simp] theorem not_isProper_refl : ¬ (refl V).IsProper := by
  rintro ⟨w, hw⟩
  exact hw w rfl

/-- Enayat's powerset-preserving end extension: every subset of an old set, as computed in
the larger model, is already old. -/
def IsPowersetPreserving (j : MembershipEndExtension V W) : Prop :=
  ∀ (a : V) (b : W), b ⊆ j a → ∃ c : V, j c = b

/-- Enayat's rank extension: every new element has rank above the rank of every old set. -/
def IsRankExtension [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (j : MembershipEndExtension V W) : Prop :=
  ∀ (a : V) (b : W), (∀ c : V, j c ≠ b) → rank (j a) ∈ rank b

section ZF

variable [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A powerset-preserving end extension computes the same powersets. -/
theorem IsPowersetPreserving.map_power {j : MembershipEndExtension V W}
    (h : j.IsPowersetPreserving) (a : V) : j (℘ a) = ℘ (j a) := by
  apply mem_ext
  intro y
  rw [mem_power_iff, j.mem_map_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (j.map_subset_iff c a).mpr (mem_power_iff.mp hc)
  · intro hy
    obtain ⟨c, rfl⟩ := h a y hy
    exact ⟨c, mem_power_iff.mpr ((j.map_subset_iff c a).mp hy), rfl⟩

end ZF

end MembershipEndExtension

section DeadEnd

/-- The dead-end property of Enayat's Theorem 5.18: no proper end extension of `V` is a
model of ZF. The larger model ranges over the universe `Type u` that `V` itself lives in. -/
def IsZFDeadEnd (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (j : MembershipEndExtension V W), ¬ j.IsProper

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- In a dead-end model every end extension to a model of ZF is onto. -/
theorem IsZFDeadEnd.surjective (h : IsZFDeadEnd V) (W : Type u) [SetStructure W] [Nonempty W]
    [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (j : MembershipEndExtension V W) : Function.Surjective j.toFun := by
  by_contra hs
  exact h W j ((j.isProper_iff_not_surjective).mpr hs)

/-- An end extension of a dead-end model that adds an element cannot satisfy ZF. This is
the form the paper uses: a quotient-of-names extension adding a set is a proper end
extension, so it fails ZF. -/
theorem IsZFDeadEnd.false_of_new_element (h : IsZFDeadEnd V) {W : Type u} [SetStructure W] [Nonempty W]
    [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (j : MembershipEndExtension V W) (w : W) (hw : ∀ v : V, j v ≠ w) : False :=
  h W j ⟨w, hw⟩

end DeadEnd

namespace ElementaryMap

variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]

/-- An elementary map preserves and reflects the truth of every sentence. -/
theorem models_sentence_iff (j : ElementaryMap V W) (σ : SetTheorySentence) :
    V↓[ℒₛₑₜ] ⊧ σ ↔ W↓[ℒₛₑₜ] ⊧ σ := by
  have h := j.elementary σ (![] : Fin 0 → V) (Empty.elim : Empty → V)
  have hf : j ∘ (Empty.elim : Empty → V) = (Empty.elim : Empty → W) := by
    funext x
    exact Empty.elim x
  have hb : j ∘ (![] : Fin 0 → V) = (![] : Fin 0 → W) := by
    funext i
    exact Fin.elim0 i
  rw [hf, hb] at h
  exact h

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Elementarity transfers a single Vopenka instance. -/
theorem vopenkaInstance_iff (j : ElementaryMap V W) (φ : SetTheorySemisentence 2) :
    VopenkaInstance (V := V) φ ↔ VopenkaInstance (V := W) φ := by
  rw [← eval_vopenkaSentence (V := V) φ, ← eval_vopenkaSentence (V := W) φ]
  exact j.models_sentence_iff (vopenkaSentence φ)

/-- Elementarity transfers the whole Vopenka scheme, instance by instance. -/
theorem vopenkaScheme (j : ElementaryMap V W)
    (h : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (φ : SetTheorySemisentence 2) : VopenkaInstance (V := W) φ :=
  (j.vopenkaInstance_iff φ).mp (h φ)

end ElementaryMap
end ZFVP
