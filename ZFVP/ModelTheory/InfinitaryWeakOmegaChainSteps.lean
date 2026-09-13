import ZFVP.ModelTheory.InfinitaryWeakMapComposition

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v

namespace WeakOmegaChain
variable {L : Language.{u}} [L.Eq] {S : Set (TaggedFormula L)}
  (M : ℕ → WeakModel.{u,v} L)
  (step : ∀ i, WeakElementaryMap (FragmentClosure.carrier S) (M i) (M (i + 1)))

/-- The finite composite of the consecutive maps from stage i to stage j. -/
def stepsMap {i j : ℕ} (h : i ≤ j) :
    WeakElementaryMap (FragmentClosure.carrier S) (M i) (M j) :=
  Nat.leRecOn h (fun {k} f ↦ (step k).comp f) (WeakElementaryMap.id (M i))

@[simp] theorem stepsMap_self (i : ℕ) (h : i ≤ i) :
    stepsMap M step h = WeakElementaryMap.id (M i) :=
  Nat.leRecOn_self _

theorem stepsMap_succ {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) :
    stepsMap M step h' = (step j).comp (stepsMap M step h) :=
  Nat.leRecOn_succ h _

@[simp] theorem stepsMap_self_apply (i : ℕ) (h : i ≤ i) (x : (M i).Domain) :
    stepsMap M step h x = x := by
  rw [stepsMap_self]
  rfl

theorem stepsMap_succ_apply {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) (x : (M i).Domain) :
    stepsMap M step h' x = step j (stepsMap M step h x) := by
  rw [stepsMap_succ M step h h']
  rfl

theorem stepsMap_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (x : (M i).Domain) :
    stepsMap M step hjk (stepsMap M step hij x) = stepsMap M step (hij.trans hjk) x := by
  induction k, hjk using Nat.le_induction with
  | base => rw [stepsMap_self_apply]
  | succ k hjk ih =>
    rw [stepsMap_succ_apply M step hjk, stepsMap_succ_apply M step (hij.trans hjk), ih]

variable [L.Encodable]

/-- Consecutive elementary maps determine a coherent omega-chain. -/
def ofSteps : WeakOmegaChain.{u,v} S where
  model := M
  map := stepsMap M step
  identity := stepsMap_self_apply M step
  composition := stepsMap_comp M step

@[simp] theorem ofSteps_model (i : ℕ) : (ofSteps M step).model i = M i := rfl

@[simp] theorem ofSteps_map {i j : ℕ} (h : i ≤ j) :
    (ofSteps M step).map h = stepsMap M step h := rfl

@[simp] theorem ofSteps_map_step (i : ℕ) (h : i ≤ i + 1) (x : (M i).Domain) :
    (ofSteps M step).map h x = step i x := by
  change stepsMap M step h x = _
  rw [stepsMap_succ_apply M step (le_refl i), stepsMap_self_apply]

/-- Freezing each old small fiber at every consecutive step freezes it along
all finite composites, including the identity composite. -/
theorem stepsMap_freezes
    (hf : ∀ i, (step i).FreezesSmallFibers) {i j : ℕ} (h : i ≤ j) :
    (stepsMap M step h).FreezesSmallFibers := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [stepsMap_self]
    exact WeakElementaryMap.id_freezes (M i)
  | succ j h ih =>
    rw [stepsMap_succ M step h]
    exact WeakElementaryMap.comp_freezes (stepsMap M step h) (step j) ih (hf j)

theorem ofSteps_freezes (hf : ∀ i, (step i).FreezesSmallFibers) :
    ∀ i j (h : i ≤ j), ((ofSteps M step).map h).FreezesSmallFibers :=
  fun _ _ h ↦ stepsMap_freezes M step hf h

end WeakOmegaChain
end ZFVP.Infinitary

