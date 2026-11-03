import Blotto.GeneralPaperEqualRouteCopyLifetime

/-! All weights and both nested endpoint matrices of the actual retained
segment-descriptor copy, including parent work fields and record references.
One conservative reserve covers every combination of child cursors. -/
namespace Blotto.GeneralPaperEqualSegmentCopyLifetime
open GeneralPaperEncodedScalarStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def parentCap (S A m r P : ℕ) : ℕ := GeneralPaperEqualRationalCopy.segmentsPrice S A m r P + m + r + S + A

def window {m r : ℕ} {l : RationalSegmentLottery m r} (S A : ℕ) (source : PreparedSegmentDescriptor l)
    (i : ℕ) (hi : i ≤ r) (j : ℕ) (hj : j ≤ m) : ℕ :=
  GeneralPaperScalarTableCopyLifetime.window S A rationalWordWidth source.weights i hi +
    GeneralPaperMatrixCopyLifetime.window S A source.left i hi j hj +
    GeneralPaperMatrixCopyLifetime.window S A source.right i hi j hj + 32 * (S + A) +
    fields S [m,r,S,A,(GeneralPaperScalarTableCopy.run S A rationalWordWidth source.weights).2,
      (GeneralPaperScalarTableCopy.matrix S A source.left).2,(GeneralPaperScalarTableCopy.matrix S A source.right).2,
      (GeneralPaperEqualRationalCopy.segments S A source).2] + 256 * (S + A + 1)

def profile (S A m r P : ℕ) : ℕ :=
  GeneralPaperScalarTableCopyLifetime.profile S A r (r * P) P +
    2 * GeneralPaperMatrixCopyLifetime.profile S A m r P + 32 * (S + A) +
    8 * (natBits (parentCap S A m r P) + S) + 32 * S + 256 * (S + A + 1)

theorem all_cursors {m r P : ℕ} {l : RationalSegmentLottery m r} (S A : ℕ)
    (source : PreparedSegmentDescriptor l) (hw : ∀ i,rationalWordWidth (source.weights.read i) ≤ P)
    (hl : ∀ i j,rationalWordWidth ((source.left.read i).read j) ≤ P)
    (hr : ∀ i j,rationalWordWidth ((source.right.read i).read j) ≤ P)
    (hA : 1 ≤ A) (hIndexM : binaryWordWidth (m + 1) ≤ A) (hIndexR : binaryWordWidth (r + 1) ≤ A)
    (i : ℕ) (hi : i ≤ r) (j : ℕ) (hj : j ≤ m) :
    window S A source i hi j hj ≤ profile S A m r P := by
  have hB := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hw i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hB
  have hWeights := GeneralPaperScalarTableCopyLifetime.all_cursors S A (r * P) P rationalWordWidth
    source.weights hB hw hA hIndexR i hi
  have hLeft := GeneralPaperMatrixCopyLifetime.all_cursors S A P source.left hl hA hIndexM hIndexR i hi j hj
  have hRight := GeneralPaperMatrixCopyLifetime.all_cursors S A P source.right hr hA hIndexM hIndexR i hi j hj
  have hWork := GeneralPaperEqualRationalCopy.segments_work S A source hw hl hr
  have hReturn : (GeneralPaperEqualRationalCopy.segments S A source).2 =
      (GeneralPaperScalarTableCopy.run S A rationalWordWidth source.weights).2 +
      (GeneralPaperScalarTableCopy.matrix S A source.left).2 +
      (GeneralPaperScalarTableCopy.matrix S A source.right).2 + 128 * (S + A + 1) := rfl
  have hf := fields_bound S (natBits (parentCap S A m r P))
    [m,r,S,A,(GeneralPaperScalarTableCopy.run S A rationalWordWidth source.weights).2,
      (GeneralPaperScalarTableCopy.matrix S A source.left).2,(GeneralPaperScalarTableCopy.matrix S A source.right).2,
      (GeneralPaperEqualRationalCopy.segments S A source).2] (by
        intro a ha
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals unfold parentCap; omega)
  change fields S _ ≤ 8 * (natBits (parentCap S A m r P) + S) + 32 * S at hf
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperEqualSegmentCopyLifetime
