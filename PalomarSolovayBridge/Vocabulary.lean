import PalomarDCBridge.Vocabulary

/-! Independent membership definitions of signed rational quotients, Dedekind reals,
ordinary interval-cover outer measure, category and the perfect set property.
Every sequence and finite sum is indexed by the model's whole omega. -/
namespace PalomarSolovayBridge
open PalomarBridge
namespace RealCode
open PalomarBridge.Coding
variable {M : Type u} (mem : M → M → Prop) [Nonempty M]
def Subset (A B : M) : Prop := ∀ x, mem x A → mem x B
noncomputable def power (A : M) : M := setValue mem (fun x => Subset mem x A)
noncomputable def intersect (A B : M) : M := setValue mem (fun x => mem x A ∧ mem x B)
noncomputable def difference (A B : M) : M := setValue mem (fun x => mem x A ∧ ¬mem x B)
noncomputable def binaryUnion (A B : M) : M := setValue mem (fun x => mem x A ∨ mem x B)
def Ordinal (a : M) : Prop :=
  (∀ x, mem x a → Subset mem x a) ∧ ∀ x, mem x a → ∀ y, mem y a → mem x y ∨ x = y ∨ mem y x
/-- Transfinite recursion, with the empty-set value off the ordinals. -/
def Attempt (F : M → M) (a f : M) : Prop := Ordinal mem a ∧ IsFunction mem f ∧
  a = domain mem f ∧ ∀ b, mem b a → ∀ y, mem (pair mem b y) f ↔ y = F (restrict mem f b)
noncomputable def recValue (F : M → M) (a : M) : M := Classical.epsilon (fun y =>
  (∃ f, Attempt mem F a f ∧ y = F f) ∨ (¬Ordinal mem a ∧ y = empty mem))
noncomputable def addStep (a f : M) : M := setValue mem (fun x => mem x a ∨
  ∃ y, mem y (range mem f) ∧ mem x (succ mem y))
noncomputable def natAdd (a b : M) : M := recValue mem (addStep mem a) b
noncomputable def iterationStep (F : M → M) (z g : M) : M := by
  classical
  exact if domain mem g = empty mem then z else F (value mem g (union mem (domain mem g)))
noncomputable def natMul (a b : M) : M := recValue mem (iterationStep mem (fun x => natAdd mem x a) (empty mem)) b
/-- A signed fraction ((a,b),d) represents (a-b)/d with d nonzero. -/
noncomputable def fractionCodes : M := setValue mem (fun c =>
  ∃ a, mem a (omega mem) ∧ ∃ b, mem b (omega mem) ∧ ∃ d, mem d (omega mem) ∧
    d ≠ empty mem ∧ c = pair mem (pair mem a b) d)
noncomputable def balance (c e : M) : M := natAdd mem
  (natMul mem (first mem (first mem c)) (second mem e))
  (natMul mem (second mem (first mem e)) (second mem c))
noncomputable def oppositeBalance (c e : M) : M := natAdd mem
  (natMul mem (second mem (first mem c)) (second mem e))
  (natMul mem (first mem (first mem e)) (second mem c))
def FractionEquiv (c e : M) : Prop := balance mem c e = oppositeBalance mem c e
noncomputable def fractionClass (c : M) : M := setValue mem
  (fun e => mem e (fractionCodes mem) ∧ FractionEquiv mem c e)
noncomputable def rationals : M := setValue mem (fun q => ∃ c, mem c (fractionCodes mem) ∧ q = fractionClass mem c)
def RatLT (q r : M) : Prop := ∃ c, mem c q ∧ ∃ e, mem e r ∧ mem (balance mem c e) (oppositeBalance mem c e)
noncomputable def fractionAdd (c e : M) : M := pair mem
  (pair mem
    (natAdd mem (natMul mem (first mem (first mem c)) (second mem e))
      (natMul mem (first mem (first mem e)) (second mem c)))
    (natAdd mem (natMul mem (second mem (first mem c)) (second mem e))
      (natMul mem (second mem (first mem e)) (second mem c))))
  (natMul mem (second mem c) (second mem e))
noncomputable def fractionNeg (c : M) : M :=
  pair mem (pair mem (second mem (first mem c)) (first mem (first mem c))) (second mem c)
noncomputable def ratAdd (q r : M) : M := setValue mem (fun x => mem x (fractionCodes mem) ∧
  ∃ c, mem c q ∧ ∃ e, mem e r ∧ FractionEquiv mem (fractionAdd mem c e) x)
noncomputable def ratNeg (q : M) : M := setValue mem (fun x => mem x (fractionCodes mem) ∧
  ∃ c, mem c q ∧ FractionEquiv mem (fractionNeg mem c) x)
noncomputable def ratZero : M := fractionClass mem (pair mem (pair mem (empty mem) (empty mem)) (numeral mem 1))
noncomputable def ratCut (q : M) : M := setValue mem (fun r => mem r (rationals mem) ∧ RatLT mem r q)
def IsReal (x : M) : Prop := Subset mem x (rationals mem) ∧ (∃ q, mem q x) ∧
  (∃ q, mem q (rationals mem) ∧ ¬mem q x) ∧
  (∀ q, mem q x → ∀ r, mem r (rationals mem) → RatLT mem r q → mem r x) ∧
  ∀ q, mem q x → ∃ r, mem r x ∧ RatLT mem q r
noncomputable def reals : M := setValue mem (IsReal mem)
def RealLT (x y : M) : Prop := Subset mem x y ∧ x ≠ y
noncomputable def interval (a b : M) : M := setValue mem (fun x => IsReal mem x ∧
  RealLT mem (ratCut mem a) x ∧ RealLT mem x (ratCut mem b))
noncomputable def basicCodes : M := setValue mem (fun p =>
  (∃ a, mem a (rationals mem) ∧ ∃ b, mem b (rationals mem) ∧ p = pair mem a b) ∧
  RatLT mem (first mem p) (second mem p))
noncomputable def openFrom (S : M) : M := setValue mem (fun x => IsReal mem x ∧
  ∃ p, mem p S ∧ mem x (interval mem (first mem p) (second mem p)))
noncomputable def closedFrom (S : M) : M := difference mem (reals mem) (openFrom mem S)
def Open (U : M) : Prop := ∃ S, Subset mem S (basicCodes mem) ∧ U = openFrom mem S
noncomputable def length (p : M) : M := ratAdd mem (second mem p) (ratNeg mem (first mem p))
noncomputable def sumNext (f p : M) : M := pair mem (succ mem (first mem p))
  (ratAdd mem (second mem p) (value mem f (first mem p)))
noncomputable def partialSum (f n : M) : M := second mem
  (recValue mem (iterationStep mem (sumNext mem f) (pair mem (empty mem) (ratZero mem))) n)
noncomputable def lengths (d : M) : M := setValue mem (fun p =>
  ∃ n, mem n (omega mem) ∧ p = pair mem n (length mem (value mem d n)))
noncomputable def cost (d n : M) : M := partialSum mem (lengths mem d) n
def IntervalCover (d A : M) : Prop := mem d (functions mem (basicCodes mem) (omega mem)) ∧
  ∀ x, mem x A → ∃ n, mem n (omega mem) ∧ mem x (interval mem (first mem (value mem d n)) (second mem (value mem d n)))
/-- A nonnegative extended real is a lower rational cut; the full cut is infinity.
This is the infimum of the costs of genuine countable rational interval covers. -/
noncomputable def outerMeasure (A : M) : M := setValue mem (fun q => mem q (rationals mem) ∧
  (RatLT mem q (ratZero mem) ∨ ∃ r, mem r (rationals mem) ∧ RatLT mem q r ∧
    ∀ d, IntervalCover mem d A → ∃ n, mem n (omega mem) ∧ RatLT mem r (cost mem d n)))
noncomputable def extendedAdd (u v : M) : M := setValue mem (fun q => mem q (rationals mem) ∧
  ∃ p, mem p u ∧ ∃ r, mem r v ∧ q = ratAdd mem p r)
def LebesgueMeasurable (A : M) : Prop := Subset mem A (reals mem) ∧
  ∀ T, Subset mem T (reals mem) → outerMeasure mem T =
    extendedAdd mem (outerMeasure mem (intersect mem T A)) (outerMeasure mem (difference mem T A))
def NowhereDense (P : M) : Prop := Subset mem P (reals mem) ∧
  ∀ a, mem a (rationals mem) → ∀ b, mem b (rationals mem) → RatLT mem a b →
    ∃ r, mem r (rationals mem) ∧ ∃ t, mem t (rationals mem) ∧
      RatLT mem a r ∧ RatLT mem r t ∧ RatLT mem t b ∧ ∀ x, mem x (interval mem r t) → ¬mem x P
def Meagre (A : M) : Prop := ∃ f, mem f (functions mem (power mem (basicCodes mem)) (omega mem)) ∧
  (∀ n, mem n (omega mem) → NowhereDense mem (closedFrom mem (value mem f n))) ∧
  ∀ x, mem x A → ∃ n, mem n (omega mem) ∧ mem x (closedFrom mem (value mem f n))
def BaireProperty (A : M) : Prop := ∃ U, Open mem U ∧
  Meagre mem (binaryUnion mem (difference mem A U) (difference mem U A))
def Perfect (P : M) : Prop := (∃ S, Subset mem S (basicCodes mem) ∧ P = closedFrom mem S) ∧
  (∃ x, mem x P) ∧ ∀ x, mem x P → ∀ a, mem a (rationals mem) → ∀ b, mem b (rationals mem) →
    mem x (interval mem a b) → ∃ y, mem y P ∧ mem y (interval mem a b) ∧ y ≠ x
def Injective (f : M) : Prop := ∀ x y z, mem (pair mem x z) f → mem (pair mem y z) f → x = y
def CardLE (A B : M) : Prop := ∃ f, mem f (functions mem B A) ∧ Injective mem f
def PerfectSetProperty (A : M) : Prop := CardLE mem A (omega mem) ∨ ∃ P, Perfect mem P ∧ Subset mem P A
/-- The least ordinal without an injection into the internal natural numbers. -/
def IsOmegaOne (k : M) : Prop := Ordinal mem k ∧ ¬CardLE mem k (omega mem) ∧
  ∀ a, Ordinal mem a → ¬CardLE mem a (omega mem) → Subset mem k a
noncomputable def omegaOne : M := Classical.epsilon (IsOmegaOne mem)
noncomputable def indexedIntersection (K I g : M) : M := setValue mem
  (fun x => mem x K ∧ ∀ i, mem i I → mem x (value mem g i))
def Ultrafilter (K U : M) : Prop := Subset mem U (power mem K) ∧ mem K U ∧ ¬mem (empty mem) U ∧
  (∀ X, mem X U → ∀ Y, Subset mem Y K → Subset mem X Y → mem Y U) ∧
  (∀ X, mem X U → ∀ Y, mem Y U → mem (intersect mem X Y) U) ∧
  ∀ X, Subset mem X K → mem X U ∨ mem (difference mem K X) U
def OmegaOneMeasure : Prop := ∃ U, Ultrafilter mem (omegaOne mem) U ∧
  (∀ x, mem x (omegaOne mem) → ¬mem (unordered mem x x) U) ∧
  ∀ a, mem a (omegaOne mem) → ∀ g, mem g (functions mem U a) →
    mem (indexedIntersection mem (omegaOne mem) a g) U
end RealCode
/-- All conjunctions of the ordinary-real Solovay target: ZF, full VP, DC,
failure of AC, Lebesgue measurability, Baire property, PSP, and the
omega-one-complete nonprincipal ultrafilter on omega one. -/
def SolovayModel {M : Type u} (mem : M → M → Prop) [Nonempty M] : Prop :=
  PalomarBridge.IsZF mem ∧ PalomarBridge.Coding.Vopenka mem ∧
  PalomarDCBridge.DependentChoice mem ∧ PalomarDCBridge.FailureOfChoice mem ∧
  (∀ A, RealCode.Subset mem A (RealCode.reals mem) → RealCode.LebesgueMeasurable mem A) ∧
  (∀ A, RealCode.Subset mem A (RealCode.reals mem) → RealCode.BaireProperty mem A) ∧
  (∀ A, RealCode.Subset mem A (RealCode.reals mem) → RealCode.PerfectSetProperty mem A) ∧
  RealCode.OmegaOneMeasure mem
def HasSolovayModel : Prop :=
  ∃ (M : Type) (mem : M → M → Prop) (hne : Nonempty M), @SolovayModel M mem hne
end PalomarSolovayBridge
