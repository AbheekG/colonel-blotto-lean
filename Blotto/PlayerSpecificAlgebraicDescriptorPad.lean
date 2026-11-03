import Blotto.PlayerSpecificSegmentAssemblyReference

/-! Actual padded algebraic arrays reuse feasible fallback endpoints
and store literal reduced zero weights in the added slots. -/
namespace Blotto.PlayerSpecificAlgebraicDescriptorPad
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def pad {N k : ℕ} (d : Descriptor N k) (m : ℕ) (fallback : Fin k) : Descriptor N (k+m) :=
  ⟨FixedArrayTable.ofFn (Fin.addCases d.weights.read (fun _ => [])),
    FixedArrayTable.ofFn (Fin.addCases d.first.read (fun _ => d.first.read fallback)),
    FixedArrayTable.ofFn (Fin.addCases d.second.read (fun _ => d.second.read fallback))⟩

theorem refines {N k : ℕ} (d : Descriptor N k) (m : ℕ) (fallback : Fin k) (x : ℝ)
    (l : SegmentLottery N k) (hr : Refines d x l) : Refines (pad d m fallback) x (PlayerSpecificSegmentAssemblyReference.pad l m fallback) := by
  constructor
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [pad,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.pad,Fin.addCases_left] using hr.weights j
    · intro j; simp only [pad,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.pad,Fin.addCases_right]; rfl
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [pad,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.pad,Fin.addCases_left] using hr.first j
    · intro j; simpa only [pad,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.pad,Fin.addCases_right] using hr.first fallback
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [pad,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.pad,Fin.addCases_left] using hr.second j
    · intro j; simpa only [pad,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.pad,Fin.addCases_right] using hr.second fallback

theorem bounds {N k : ℕ} (root : Candidate) (d : Descriptor N k) (m : ℕ) (fallback : Fin k) (T : ℕ)
    (hm0 : root.polynomial≠[]) (hd : Bounds root d T) : Bounds root (pad d m fallback) T := by
  constructor
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [pad,FixedArrayTable.read_ofFn,Fin.addCases_left] using hd.weights j
    · intro j; simp only [pad,FixedArrayTable.read_ofFn,Fin.addCases_right]; exact ⟨nil_reduced _ hm0,nil_height _⟩
  · intro slot j
    refine Fin.addCases ?_ ?_ slot
    · intro slot; simpa only [pad,FixedArrayTable.read_ofFn,Fin.addCases_left] using hd.first slot j
    · intro slot; simpa only [pad,FixedArrayTable.read_ofFn,Fin.addCases_right] using hd.first fallback j
  · intro slot j
    refine Fin.addCases ?_ ?_ slot
    · intro slot; simpa only [pad,FixedArrayTable.read_ofFn,Fin.addCases_left] using hd.second slot j
    · intro slot; simpa only [pad,FixedArrayTable.read_ofFn,Fin.addCases_right] using hd.second fallback j

end Blotto.PlayerSpecificAlgebraicDescriptorPad
