import Blotto.PlayerSpecificSturmRootCount

/-! Stored Sturm rows and endpoint values for actual rational bisection.
Preparing the sequence happens once. A split evaluates its midpoint once,
then reuses that variation value in the two child records. -/
namespace Blotto.PlayerSpecificIsolationState
open PlayerSpecificDensePolynomial
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Prepared (p : Data) where
  sequence : List Data
  correct : sequence=PlayerSpecificSturmRootCount.rows p

def prepare (p : Data) : Prepared p := ⟨PlayerSpecificSturmRootCount.rows p,rfl⟩

def variations {p : Data} (prepared : Prepared p) (x : ℚ) : ℕ :=
  PlayerSpecificSturmSequence.variations prepared.sequence x

theorem variations_eq {p : Data} (prepared : Prepared p) (x : ℚ) :
    variations prepared x=PlayerSpecificSturmSequence.variations (PlayerSpecificSturmRootCount.rows p) x := by
  rw [variations,prepared.correct]

structure Interval where
  lo : ℚ
  hi : ℚ
  loValue : ℕ
  hiValue : ℕ

def Interval.count (node : Interval) : ℕ := node.loValue-node.hiValue
def Interval.width (node : Interval) : ℚ := node.hi-node.lo
def Interval.midpoint (node : Interval) : ℚ := (node.lo+node.hi)/2
def Interval.Contains (node : Interval) (x : ℝ) : Prop := (node.lo : ℝ)<x ∧ x≤(node.hi : ℝ)
def Valid {p : Data} (prepared : Prepared p) (node : Interval) : Prop :=
  node.lo<node.hi ∧ node.loValue=variations prepared node.lo ∧ node.hiValue=variations prepared node.hi

def initial {p : Data} (prepared : Prepared p) (a b : ℚ) : Interval :=
  ⟨a,b,variations prepared a,variations prepared b⟩

theorem initial_valid {p : Data} (prepared : Prepared p) (a b : ℚ) (h : a<b) : Valid prepared (initial prepared a b) :=
  ⟨h,rfl,rfl⟩

def split {p : Data} (prepared : Prepared p) (node : Interval) : Interval×Interval :=
  let middle := node.midpoint
  let value := variations prepared middle
  (⟨node.lo,middle,node.loValue,value⟩,⟨middle,node.hi,value,node.hiValue⟩)

theorem midpoint_between (node : Interval) (h : node.lo<node.hi) : node.lo<node.midpoint ∧ node.midpoint<node.hi := by
  unfold Interval.midpoint
  constructor <;> linarith

theorem split_valid {p : Data} (prepared : Prepared p) (node : Interval) (h : Valid prepared node) :
    Valid prepared (split prepared node).1 ∧ Valid prepared (split prepared node).2 := by
  have hm := midpoint_between node h.1
  exact ⟨⟨hm.1,h.2.1,rfl⟩,⟨hm.2,rfl,h.2.2⟩⟩

theorem count_eq {p : Data} (prepared : Prepared p) (node : Interval) (h : Valid prepared node) :
    node.count=PlayerSpecificSturmRootCount.count p node.lo node.hi := by
  rw [Interval.count,h.2.1,h.2.2,variations_eq,variations_eq]
  rfl

theorem split_counts {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (node : Interval) (h : Valid prepared node) :
    node.count=(split prepared node).1.count+(split prepared node).2.count := by
  have hv := split_valid prepared node h
  have hm := midpoint_between node h.1
  calc
    node.count=PlayerSpecificSturmRootCount.count p node.lo node.hi := count_eq prepared node h
    _ = PlayerSpecificSturmRootCount.count p node.lo node.midpoint+
        PlayerSpecificSturmRootCount.count p node.midpoint node.hi :=
      PlayerSpecificSturmRootCount.additive p hp _ _ _ hm.1.le hm.2.le
    _ = _ := congrArg₂ Nat.add (count_eq prepared (split prepared node).1 hv.1).symm
      (count_eq prepared (split prepared node).2 hv.2).symm

theorem split_width {p : Data} (prepared : Prepared p) (node : Interval) :
    (split prepared node).1.width=node.width/2 ∧ (split prepared node).2.width=node.width/2 := by
  constructor <;> dsimp only [split,Interval.width,Interval.midpoint] <;> ring

theorem split_cover {p : Data} (prepared : Prepared p) (node : Interval) (h : node.lo<node.hi) (x : ℝ) :
    node.Contains x ↔ (split prepared node).1.Contains x ∨ (split prepared node).2.Contains x := by
  have hm := midpoint_between node h
  have hl : (node.lo : ℝ)<(node.midpoint : ℝ) := by exact_mod_cast hm.1
  have hh : (node.midpoint : ℝ)<(node.hi : ℝ) := by exact_mod_cast hm.2
  change (node.lo : ℝ)<x ∧ x≤(node.hi : ℝ) ↔
    ((node.lo : ℝ)<x ∧ x≤(node.midpoint : ℝ)) ∨ ((node.midpoint : ℝ)<x ∧ x≤(node.hi : ℝ))
  constructor
  · rintro ⟨hx,hx'⟩
    by_cases he : x≤(node.midpoint : ℝ)
    · exact Or.inl ⟨hx,he⟩
    · exact Or.inr ⟨lt_of_not_ge he,hx'⟩
  · rintro (⟨hx,hx'⟩ | ⟨hx,hx'⟩)
    · exact ⟨hx,hx'.trans hh.le⟩
    · exact ⟨hl.trans hx,hx'⟩

theorem split_disjoint {p : Data} (prepared : Prepared p) (node : Interval) (x : ℝ) :
    ¬((split prepared node).1.Contains x ∧ (split prepared node).2.Contains x) := by
  rintro ⟨hl,hr⟩
  exact (not_lt_of_ge hl.2) hr.1

theorem positive_iff {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (node : Interval) (h : Valid prepared node) :
    0<node.count ↔ ∃ x : ℝ,PlayerSpecificSturmVariations.realEvaluate p x=0 ∧ node.Contains x := by
  rw [count_eq prepared node h]
  exact PlayerSpecificSturmRootCount.positive_iff p hp node.lo node.hi h.1.le

end Blotto.PlayerSpecificIsolationState
