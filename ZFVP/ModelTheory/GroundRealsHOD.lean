import ZFVP.ModelTheory.ForcingModelChecks
import ZFVP.SetTheory.TransitiveClosure
import ZFVP.SetTheory.EndExtensionCoding

/-! The full Solovay model `HOD_{V ∪ R}^{V[G]}` of the paper (eq. full-Solovay): the sets of the
extension that are hereditarily definable from ground-model sets, reals of the extension and
ordinals. Ground sets, reals and ordinals belong to it, and membership is inherited. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A : ForcingContext V)

/-- The parameters allowed in `HOD_{V ∪ R}`: individual ground sets, individual reals of the
extension (coded as subsets of `ω`), and ordinals. -/
def IsSolovayParameter (x : A.Model) : Prop :=
  (∃ a : V, x = A.check a) ∨ x ⊆ A.check (ω : V) ∨ IsOrdinal x

/-- `x` is definable in the extension from allowed parameters. -/
def IsGroundRealDefinable (x : A.Model) : Prop :=
  ∃ (n : ℕ) (φ : SetTheorySemisentence (n + 1)) (v : Fin n → A.Model),
    (∀ i, A.IsSolovayParameter (v i)) ∧ ∀ b, b ∈ x ↔ φ.Evalb (b :> v)

/-- `x` and every member of its transitive closure are definable from allowed parameters. -/
def IsHereditarilyGroundRealDefinable (x : A.Model) : Prop :=
  ∀ y ∈ transitiveClosure ({x} : A.Model), A.IsGroundRealDefinable y

/-- The full Solovay model `HOD_{V ∪ R}^{V[G]}`. -/
def SolovayModel := {x : A.Model // A.IsHereditarilyGroundRealDefinable x}

instance solovayModelSetStructure : SetStructure A.SolovayModel where
  mem y x := x.val ∈ y.val

theorem solovayModel_mem_iff (x y : A.SolovayModel) : x ∈ y ↔ x.val ∈ y.val := Iff.rfl

variable {A}

theorem groundRealDefinable_of_parameter {x : A.Model} (hx : A.IsSolovayParameter x) :
    A.IsGroundRealDefinable x :=
  ⟨1, “b p. b ∈ p”, ![x], fun i ↦ by rw [Fin.fin_one_eq_zero i]; exact hx, fun b ↦ by simp⟩

theorem hereditarilyGroundRealDefinable_of_mem {x y : A.Model}
    (hx : A.IsHereditarilyGroundRealDefinable x) (hy : y ∈ x) :
    A.IsHereditarilyGroundRealDefinable y := by
  intro z hz
  apply hx
  refine transitiveClosure_minimal _ _ ?_ (transitiveClosure_transitive _) z hz
  rw [singleton_subset_iff_mem]
  exact (transitiveClosure_transitive _).mem_trans hy
    (subset_transitiveClosure _ _ (mem_singleton_iff.mpr rfl))

theorem self_mem_transitiveClosure_singleton (x : A.Model) :
    x ∈ transitiveClosure ({x} : A.Model) :=
  subset_transitiveClosure _ _ (mem_singleton_iff.mpr rfl)

theorem groundRealDefinable_of_hereditarily {x : A.Model}
    (hx : A.IsHereditarilyGroundRealDefinable x) : A.IsGroundRealDefinable x :=
  hx x (self_mem_transitiveClosure_singleton x)

/-- The check of a transitive set is transitive. -/
theorem check_transitive_of_ground {T : V} (hT : IsTransitive T) : IsTransitive (A.check T) := by
  refine ⟨fun y hy z hz ↦ ?_⟩
  obtain ⟨b, hb, rfl⟩ := (A.mem_check_iff T y).mp hy
  obtain ⟨c, hc, rfl⟩ := (A.mem_check_iff b z).mp hz
  exact (A.mem_check_iff T _).mpr ⟨c, hT.mem_trans hc hb, rfl⟩

theorem hereditarily_check (a : V) : A.IsHereditarilyGroundRealDefinable (A.check a) := by
  intro y hy
  have hsub : transitiveClosure ({A.check a} : A.Model) ⊆ A.check (transitiveClosure ({a} : V)) := by
    refine transitiveClosure_minimal _ _ ?_ (check_transitive_of_ground (transitiveClosure_transitive _))
    rw [singleton_subset_iff_mem]
    exact (A.mem_check_iff _ _).mpr ⟨a, subset_transitiveClosure _ _ (mem_singleton_iff.mpr rfl), rfl⟩
  obtain ⟨b, _, rfl⟩ := (A.mem_check_iff _ _).mp (hsub y hy)
  exact groundRealDefinable_of_parameter (Or.inl ⟨b, rfl⟩)

theorem check_omega_eq : A.check (ω : V) = (ω : A.Model) := A.checkEmbedding.map_omega

/-- Every natural number of the extension is a check. -/
theorem exists_check_of_mem_omega {n : A.Model} (hn : n ∈ (ω : A.Model)) : ∃ m : V, n = A.check m := by
  rw [← check_omega_eq] at hn
  obtain ⟨m, _, rfl⟩ := (A.mem_check_iff _ _).mp hn
  exact ⟨m, rfl⟩

theorem hereditarily_real {x : A.Model} (hx : x ⊆ A.check (ω : V)) :
    A.IsHereditarilyGroundRealDefinable x := by
  intro y hy
  have hωt : IsTransitive (ω : V) := IsOrdinal.toIsTransitive
  let T : A.Model := insert x (A.check (ω : V))
  have hT : IsTransitive T := by
    refine ⟨fun y hy z hz ↦ ?_⟩
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_insert.mpr (Or.inr (hx z hz))
    · exact mem_insert.mpr (Or.inr ((check_transitive_of_ground hωt).mem_trans hz hy))
  have hsub : transitiveClosure ({x} : A.Model) ⊆ T :=
    transitiveClosure_minimal _ _ (by rw [singleton_subset_iff_mem]; exact mem_insert.mpr (Or.inl rfl)) hT
  rcases mem_insert.mp (hsub y hy) with rfl | hy'
  · exact groundRealDefinable_of_parameter (Or.inr (Or.inl hx))
  · obtain ⟨b, _, rfl⟩ := (A.mem_check_iff _ _).mp hy'
    exact groundRealDefinable_of_parameter (Or.inl ⟨b, rfl⟩)

theorem hereditarily_ordinal {α : A.Model} (hα : IsOrdinal α) :
    A.IsHereditarilyGroundRealDefinable α := by
  intro y hy
  have htr : IsTransitive α := hα.toIsTransitive
  have hT : IsTransitive (insert α α : A.Model) := by
    refine ⟨fun y hy z hz ↦ ?_⟩
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_insert.mpr (Or.inr hz)
    · exact mem_insert.mpr (Or.inr (htr.mem_trans hz hy))
  have hsub : transitiveClosure ({α} : A.Model) ⊆ insert α α :=
    transitiveClosure_minimal _ _ (by rw [singleton_subset_iff_mem]; exact mem_insert.mpr (Or.inl rfl)) hT
  rcases mem_insert.mp (hsub y hy) with rfl | hy'
  · exact groundRealDefinable_of_parameter (Or.inr (Or.inr hα))
  · exact groundRealDefinable_of_parameter (Or.inr (Or.inr (IsOrdinal.of_mem hy')))

theorem hereditarily_of_parameter {x : A.Model} (hx : A.IsSolovayParameter x) :
    A.IsHereditarilyGroundRealDefinable x := by
  rcases hx with ⟨a, rfl⟩ | hx | hx
  · exact hereditarily_check a
  · exact hereditarily_real hx
  · exact hereditarily_ordinal hx

variable (A)

/-- Ground sets inside the Solovay model. -/
noncomputable def solovayCheck (a : V) : A.SolovayModel := ⟨A.check a, hereditarily_check a⟩

instance solovayModelNonempty : Nonempty A.SolovayModel := ⟨A.solovayCheck ∅⟩

theorem solovayCheck_val (a : V) : (A.solovayCheck a).val = A.check a := rfl

theorem solovayCheck_mem_iff (a b : V) : A.solovayCheck a ∈ A.solovayCheck b ↔ a ∈ b :=
  A.check_mem_iff a b

theorem solovayCheck_injective : Function.Injective A.solovayCheck := fun a b h ↦
  (A.check_eq_iff a b).mp (congrArg Subtype.val h)

/-- The inclusion of the Solovay model into the extension preserves and reflects membership. -/
theorem solovayModel_val_mem_iff (x y : A.SolovayModel) : x.val ∈ y.val ↔ x ∈ y := Iff.rfl

theorem solovayModel_val_injective : Function.Injective (Subtype.val : A.SolovayModel → A.Model) :=
  Subtype.val_injective

end ForcingContext

end ZFVP
