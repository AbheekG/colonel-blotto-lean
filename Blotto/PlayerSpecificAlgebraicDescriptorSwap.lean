import Blotto.PlayerSpecificAlgebraicNestedInteriorLinear

/-! A native coordinate swap works for any cached three-coordinate
descriptor and preserves coefficient sizes without arithmetic. -/
namespace Blotto.PlayerSpecificAlgebraicDescriptorSwap
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

def row (a : FixedArrayTable 3 Data) : FixedArrayTable 3 Data :=
  FixedArrayTable.ofFn ![a.read 1,a.read 0,a.read 2]

def swap {slots : ℕ} (d : Descriptor 3 slots) : Descriptor 3 slots :=
  ⟨d.weights,FixedArrayTable.ofFn (fun slot => row (d.first.read slot)),
    FixedArrayTable.ofFn (fun slot => row (d.second.read slot))⟩

theorem row_value (a : FixedArrayTable 3 Data) (x : ℝ) : values (row a) x=swapFirst (values a x) := by
  funext j
  fin_cases j <;> simp [row,values,FixedArrayTable.read_ofFn,swapFirst]

theorem refines {slots : ℕ} (d : Descriptor 3 slots) (x : ℝ) (l : SegmentLottery 3 slots) (hr : Refines d x l) :
    Refines (swap d) x (l.mapped AffineAllocation.swapFirst) := by
  refine ⟨hr.weights,?_,?_⟩
  · intro slot
    rw [swap,FixedArrayTable.read_ofFn,row_value,hr.first slot]
    rfl
  · intro slot
    rw [swap,FixedArrayTable.read_ofFn,row_value,hr.second slot]
    rfl

theorem bounds {slots : ℕ} (root : Candidate) (d : Descriptor 3 slots) (T : ℕ) (h : Bounds root d T) :
    Bounds root (swap d) T := by
  refine ⟨h.weights,?_,?_⟩
  · intro slot j
    fin_cases j <;> simp only [swap,row,FixedArrayTable.read_ofFn]
    · exact h.first slot 1
    · exact h.first slot 0
    · exact h.first slot 2
  · intro slot j
    fin_cases j <;> simp only [swap,row,FixedArrayTable.read_ofFn]
    · exact h.second slot 1
    · exact h.second slot 0
    · exact h.second slot 2

theorem box {a d c : ℝ} {y : Allocation 3} (hy : InBox ![a,d,c] y) : InBox ![d,a,c] (swapFirst y) := by
  intro j
  fin_cases j
  · exact hy 1
  · exact hy 0
  · exact hy 2

end Blotto.PlayerSpecificAlgebraicDescriptorSwap
