import ZFVP.SetTheory.MembershipEndExtension
import Mathlib.Order.Lattice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v

/-- A directed system of membership end-embeddings. -/
structure MembershipDirectedSystem (I : Type u) [Preorder I] where
  Model : I → Type v
  modelStructure : ∀ i, SetStructure (Model i)
  inclusion : (∀ {i j}, i ≤ j →
    @MembershipEndExtension (Model i) (Model j) (modelStructure i) (modelStructure j))
  identity : ∀ i x, inclusion (le_refl i) x = x
  composition : (∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) x,
    inclusion hjk (inclusion hij x) = inclusion (le_trans hij hjk) x)

attribute [instance] MembershipDirectedSystem.modelStructure

namespace MembershipDirectedSystem

variable {I : Type u} [SemilatticeSup I] (S : MembershipDirectedSystem.{u,v} I)

abbrev Point := Σ i, S.Model i

def Equal (x y : S.Point) : Prop :=
  ∃ k, ∃ hx : x.1 ≤ k, ∃ hy : y.1 ≤ k, S.inclusion hx x.2 = S.inclusion hy y.2

def Member (x y : S.Point) : Prop :=
  ∃ k, ∃ hx : x.1 ≤ k, ∃ hy : y.1 ≤ k, S.inclusion hx x.2 ∈ S.inclusion hy y.2

theorem equal_raise {x y : S.Point} {k l : I} (hx : x.1 ≤ k) (hy : y.1 ≤ k)
    (hkl : k ≤ l) (he : S.inclusion hx x.2 = S.inclusion hy y.2) :
    S.inclusion (le_trans hx hkl) x.2 = S.inclusion (le_trans hy hkl) y.2 :=
  (S.composition hx hkl x.2).symm.trans
    ((congrArg (S.inclusion hkl) he).trans (S.composition hy hkl y.2))

theorem member_raise {x y : S.Point} {k l : I} (hx : x.1 ≤ k) (hy : y.1 ≤ k)
    (hkl : k ≤ l) (hm : S.inclusion hx x.2 ∈ S.inclusion hy y.2) :
    S.inclusion (le_trans hx hkl) x.2 ∈ S.inclusion (le_trans hy hkl) y.2 := by
  have hm' := (S.inclusion hkl).mem_iff (S.inclusion hx x.2) (S.inclusion hy y.2) |>.mpr hm
  rwa [S.composition, S.composition] at hm'

theorem equal_iff_at (x y : S.Point) (k : I) (hx : x.1 ≤ k) (hy : y.1 ≤ k) :
    S.Equal x y ↔ S.inclusion hx x.2 = S.inclusion hy y.2 := by
  constructor
  · rintro ⟨l, hxl, hyl, he⟩
    have hm := S.equal_raise hxl hyl (show l ≤ k ⊔ l from le_sup_right) he
    apply (S.inclusion (show k ≤ k ⊔ l from le_sup_left)).injective
    rwa [S.composition, S.composition]
  · exact fun he ↦ ⟨k, hx, hy, he⟩

theorem member_iff_at (x y : S.Point) (k : I) (hx : x.1 ≤ k) (hy : y.1 ≤ k) :
    S.Member x y ↔ S.inclusion hx x.2 ∈ S.inclusion hy y.2 := by
  constructor
  · rintro ⟨l, hxl, hyl, hm⟩
    have hm' := S.member_raise hxl hyl (show l ≤ k ⊔ l from le_sup_right) hm
    apply (S.inclusion (show k ≤ k ⊔ l from le_sup_left)).mem_iff _ _ |>.mp
    rwa [S.composition, S.composition]
  · exact fun hm ↦ ⟨k, hx, hy, hm⟩

def setoid : Setoid S.Point where
  r := S.Equal
  iseqv := {
    refl := fun x ↦ ⟨x.1, le_refl _, le_refl _, rfl⟩
    symm := fun ⟨k, hx, hy, he⟩ ↦ ⟨k, hy, hx, he.symm⟩
    trans := by
      intro x y z hxy hyz
      let k := (x.1 ⊔ y.1) ⊔ z.1
      have hx : x.1 ≤ k := le_trans le_sup_left le_sup_left
      have hy : y.1 ≤ k := le_trans le_sup_right le_sup_left
      have hz : z.1 ≤ k := le_sup_right
      exact ⟨k, hx, hz, ((S.equal_iff_at x y k hx hy).mp hxy).trans
        ((S.equal_iff_at y z k hy hz).mp hyz)⟩ }

theorem member_congr {x x' y y' : S.Point} (hx : S.Equal x x') (hy : S.Equal y y') :
    S.Member x y ↔ S.Member x' y' := by
  let k := (x.1 ⊔ x'.1) ⊔ (y.1 ⊔ y'.1)
  have hxk : x.1 ≤ k := le_trans le_sup_left le_sup_left
  have hx'k : x'.1 ≤ k := le_trans le_sup_right le_sup_left
  have hyk : y.1 ≤ k := le_trans le_sup_left le_sup_right
  have hy'k : y'.1 ≤ k := le_trans le_sup_right le_sup_right
  rw [S.member_iff_at x y k hxk hyk, S.member_iff_at x' y' k hx'k hy'k,
    (S.equal_iff_at x x' k hxk hx'k).mp hx,
    (S.equal_iff_at y y' k hyk hy'k).mp hy]

def Limit := Quotient S.setoid

def ofPoint (x : S.Point) : S.Limit := Quotient.mk _ x

theorem ofPoint_eq_iff (x y : S.Point) : S.ofPoint x = S.ofPoint y ↔ S.Equal x y :=
  ⟨Quotient.exact, fun h ↦ Quotient.sound (s := S.setoid) h⟩

instance limitStructure : SetStructure S.Limit where
  mem y x := Quotient.liftOn₂ x y S.Member
    (fun _ _ _ _ hx hy ↦ propext (S.member_congr hx hy))

theorem ofPoint_mem_iff (x y : S.Point) : S.ofPoint x ∈ S.ofPoint y ↔ S.Member x y := Iff.rfl

def fromStage (i : I) (x : S.Model i) : S.Limit := S.ofPoint ⟨i, x⟩

theorem fromStage_injective (i : I) : Function.Injective (S.fromStage i) := by
  intro x y he
  have hxy := (S.equal_iff_at ⟨i, x⟩ ⟨i, y⟩ i (le_refl i) (le_refl i)).mp
    ((S.ofPoint_eq_iff _ _).mp he)
  simpa only [S.identity] using hxy

theorem fromStage_mem_iff (i : I) (x y : S.Model i) :
    S.fromStage i x ∈ S.fromStage i y ↔ x ∈ y := by
  change S.Member ⟨i, x⟩ ⟨i, y⟩ ↔ _
  rw [S.member_iff_at _ _ i (le_refl i) (le_refl i), S.identity, S.identity]

theorem fromStage_coherent {i j : I} (hij : i ≤ j) (x : S.Model i) :
    S.fromStage j (S.inclusion hij x) = S.fromStage i x := by
  apply Quotient.sound
  exact ⟨j, le_refl j, hij, S.identity j _⟩

theorem fromStage_endExtension (i : I) (x : S.Model i) (y : S.Limit)
    (hy : y ∈ S.fromStage i x) : ∃ z ∈ x, y = S.fromStage i z := by
  induction y using Quotient.inductionOn with
  | _ y =>
    obtain ⟨k, hyk, hik, hym⟩ := hy
    obtain ⟨z, hz, he⟩ := (S.inclusion hik).endExtension x (S.inclusion hyk y.2) hym
    refine ⟨z, hz, ?_⟩
    apply Quotient.sound
    exact ⟨k, hyk, hik, he⟩

def stageEmbedding (i : I) : MembershipEndExtension (S.Model i) S.Limit where
  toFun := S.fromStage i
  injective := S.fromStage_injective i
  mem_iff := S.fromStage_mem_iff i
  endExtension := S.fromStage_endExtension i

theorem stage_cover (x : S.Limit) : ∃ i, ∃ y : S.Model i, x = S.fromStage i y := by
  induction x using Quotient.inductionOn with
  | _ x => exact ⟨x.1, x.2, rfl⟩

instance limitNonempty [Nonempty I] [∀ i, Nonempty (S.Model i)] : Nonempty S.Limit := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact Nonempty.map (S.fromStage i) inferInstance

end MembershipDirectedSystem
end ZFVP
