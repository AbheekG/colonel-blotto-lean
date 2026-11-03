import Blotto.PlayerSpecificAlgebraicDescriptorPad

/-! Actual binary descriptor assembly caches the algebraic complement
once and multiplies each component weight once. Endpoints are reused. -/
namespace Blotto.PlayerSpecificAlgebraicDescriptorBinary
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorReference
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def binary {N k m : ℕ} (root : Candidate) (p : Data) (l : Descriptor N k) (r : Descriptor N m) : Descriptor N (k+m) :=
  let complement:=PlayerSpecificAlgebraicField.minus root.polynomial (PlayerSpecificAlgebraicField.constant root.polynomial 1) p
  ⟨FixedArrayTable.ofFn (Fin.addCases
      (fun j => PlayerSpecificAlgebraicField.times root.polynomial p (l.weights.read j))
      (fun j => PlayerSpecificAlgebraicField.times root.polynomial complement (r.weights.read j))),
    FixedArrayTable.ofFn (Fin.addCases l.first.read r.first.read),
    FixedArrayTable.ofFn (Fin.addCases l.second.read r.second.read)⟩

theorem refines {N k m : ℕ} (root : Candidate) (p : Data) (l : Descriptor N k) (r : Descriptor N m)
    (x : ℝ) (hx : realEvaluate root.polynomial x=0) (hp : 0≤realEvaluate p x ∧ realEvaluate p x≤1)
    (lref : SegmentLottery N k) (rref : SegmentLottery N m) (hl : Refines l x lref) (hr : Refines r x rref) :
    Refines (binary root p l r) x (PlayerSpecificSegmentAssemblyReference.binary (realEvaluate p x) hp lref rref) := by
  constructor
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j
      simp only [binary,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.binary,Fin.addCases_left,
        PlayerSpecificAlgebraicField.times_value _ _ _ x hx,hl.weights j]
    · intro j
      simp only [binary,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.binary,Fin.addCases_right,
        PlayerSpecificAlgebraicField.times_value _ _ _ x hx,PlayerSpecificAlgebraicField.minus_value _ _ _ x hx,
        PlayerSpecificAlgebraicField.constant_value _ _ x hx,Rat.cast_one,hr.weights j]
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [binary,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.binary,Fin.addCases_left] using hl.first j
    · intro j; simpa only [binary,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.binary,Fin.addCases_right] using hr.first j
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [binary,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.binary,Fin.addCases_left] using hl.second j
    · intro j; simpa only [binary,FixedArrayTable.read_ofFn,PlayerSpecificSegmentAssemblyReference.binary,Fin.addCases_right] using hr.second j

end Blotto.PlayerSpecificAlgebraicDescriptorBinary
