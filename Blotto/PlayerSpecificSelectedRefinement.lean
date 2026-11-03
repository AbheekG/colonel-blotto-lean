import Blotto.PlayerSpecificAlgebraicSignMagnitude

/-! Computable single-root refinement retains the chosen conjugate. Each
step uses the actual cached midpoint count; positivity selects its left
child, otherwise the right. No supplied root comparison is executed. -/
namespace Blotto.PlayerSpecificSelectedRefinement
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Unique (p : Data) (node : Interval) (x : ℝ) : Prop :=
  realEvaluate p x=0 ∧ node.Contains x ∧ ∀ y : ℝ,realEvaluate p y=0 → node.Contains y → y=x
def step {p : Data} (prepared : Prepared p) (node : Interval) : Interval :=
  let parts:=split prepared node
  if 0<parts.1.count then parts.1 else parts.2
def run {p : Data} (prepared : Prepared p) : ℕ → Interval → Interval
  | 0,node => node
  | fuel+1,node => run prepared fuel (step prepared node)

theorem step_valid {p : Data} (prepared : Prepared p) (node : Interval) (hv : Valid prepared node) :
    Valid prepared (step prepared node) := by
  have hs:=split_valid prepared node hv
  rw [step]
  split
  · exact hs.1
  · exact hs.2

theorem step_contained {p : Data} (prepared : Prepared p) (node : Interval) (hv : Valid prepared node) :
    ∀ x : ℝ,(step prepared node).Contains x → node.Contains x := by
  intro x hx
  rw [step] at hx
  split at hx
  · exact (split_cover prepared node hv.1 x).mpr (Or.inl hx)
  · exact (split_cover prepared node hv.1 x).mpr (Or.inr hx)

theorem step_unique {p : Data} (prepared : Prepared p) (hp : semantics p≠0)
    (node : Interval) (hv : Valid prepared node) (x : ℝ) (hu : Unique p node x) :
    Unique p (step prepared node) x := by
  have hs:=split_valid prepared node hv
  have hx : (step prepared node).Contains x := by
    rw [step]
    split
    · rename_i hpositive
      obtain ⟨y,hy,hynode⟩:=(positive_iff prepared hp (split prepared node).1 hs.1).mp hpositive
      have he:=hu.2.2 y hy ((split_cover prepared node hv.1 y).mpr (Or.inl hynode))
      simpa only [he] using hynode
    · rename_i hnegative
      rcases (split_cover prepared node hv.1 x).mp hu.2.1 with hleft | hright
      · exact (hnegative ((positive_iff prepared hp (split prepared node).1 hs.1).mpr ⟨x,hu.1,hleft⟩)).elim
      · exact hright
  exact ⟨hu.1,hx,fun y hy hynode => hu.2.2 y hy (step_contained prepared node hv y hynode)⟩

theorem step_width {p : Data} (prepared : Prepared p) (node : Interval) :
    (step prepared node).width=node.width/2 := by
  have hs:=split_width prepared node
  rw [step]
  split
  · exact hs.1
  · exact hs.2

theorem run_valid {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) (hv : Valid prepared node) :
    Valid prepared (run prepared fuel node) := by
  induction fuel generalizing node with
  | zero => exact hv
  | succ fuel ih => exact ih (step prepared node) (step_valid prepared node hv)

theorem run_unique {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (fuel : ℕ)
    (node : Interval) (hv : Valid prepared node) (x : ℝ) (hu : Unique p node x) :
    Unique p (run prepared fuel node) x := by
  induction fuel generalizing node with
  | zero => exact hu
  | succ fuel ih => exact ih (step prepared node) (step_valid prepared node hv) (step_unique prepared hp node hv x hu)

theorem run_width {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) :
    (run prepared fuel node).width=node.width/(2:ℚ)^fuel := by
  induction fuel generalizing node with
  | zero => simp only [run,pow_zero,div_one]
  | succ fuel ih =>
    rw [run,ih,step_width,pow_succ]
    ring

theorem run_contained {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) (hv : Valid prepared node) :
    ∀ x : ℝ,(run prepared fuel node).Contains x → node.Contains x := by
  induction fuel generalizing node with
  | zero => exact fun _ hx => hx
  | succ fuel ih =>
    intro x hx
    exact step_contained prepared node hv x (ih (step prepared node) (step_valid prepared node hv) x hx)

end Blotto.PlayerSpecificSelectedRefinement
