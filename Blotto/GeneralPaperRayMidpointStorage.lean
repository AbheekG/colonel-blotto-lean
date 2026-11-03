import Blotto.GeneralPaperAffineInitialStorage

/-! Literal rational bracket midpoint scratch, distinct from rank/index
midpoints. Counts both endpoints, sum, constant two, result, all three
primitive reservations and encoded actual work/partial-work metadata. -/
namespace Blotto.GeneralPaperRayMidpointStorage
open RationalOrderCell GeneralPaperRationalPrimitivePrice GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def cap (model : RationalCostModel) (W R : ℕ) : ℕ := 16*W+5*model.rat (4*R+7)
def window (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) : ℕ :=
  let literal := model.rat (rationalWordWidth (2:ℚ))
  let add := binary model.rat (·+·) lo hi
  let divide := binary model.rat (·/·) (lo+hi) 2
  let result := GeneralPaperRayMidpointPrice.run model.rat W lo hi
  rationalWordWidth lo+rationalWordWidth hi+rationalWordWidth (lo+hi)+rationalWordWidth (2:ℚ)+rationalWordWidth result.1+
    literal+add+divide+fields W [16*W,literal,add,divide,16*W+literal,16*W+literal+add,result.2]+256*W

def profile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  5*(4*R+7)+5*model.rat (4*R+7)+7*(natBits (1+cap model W R)+W)+288*W

theorem bounded (model : RationalCostModel) (W R : ℕ) (lo hi : ℚ)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) : window model W lo hi≤profile model W R := by
  let literal := model.rat (rationalWordWidth (2:ℚ))
  let add := binary model.rat (·+·) lo hi
  let divide := binary model.rat (·/·) (lo+hi) 2
  let result := GeneralPaperRayMidpointPrice.run model.rat W lo hi
  have hTwo : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hL := rationalWordWidth_of_height (hl.mono (show R≤2*R+3 by omega))
  have hH := rationalWordWidth_of_height (hh.mono (show R≤2*R+3 by omega))
  have hS := rationalWordWidth_of_height ((hl.add hh).mono (show R+R+1≤2*R+3 by omega))
  have h2 := rationalWordWidth_of_height (hTwo.mono (show 2≤2*R+3 by omega))
  have hM := rationalWordWidth_of_height (GeneralPaperRayAffineBound.midpoint_height hl hh)
  have he : 1+2*(2*R+3)=4*R+7 := by ring
  rw [he] at hL hH hS h2 hM
  have hLiteral : literal≤model.rat (4*R+7) := model.monotone h2
  have hAdd : add≤2*model.rat (4*R+7) := binary_le model.rat model.monotone (·+·) lo hi _ hL hH hS
  have hDivide : divide≤2*model.rat (4*R+7) := binary_le model.rat model.monotone (·/·) (lo+hi) 2 _ hS h2 hM
  have hWork := GeneralPaperRayMidpointPrice.work model.rat model.monotone W R lo hi hl hh
  change result.2≤cap model W R at hWork
  have hShape : result.2=16*W+literal+add+divide := rfl
  have hf := fields_bound W (natBits (1+cap model W R)) [16*W,literal,add,divide,16*W+literal,16*W+literal+add,result.2] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (1+cap model W R)+W)+32*W at hf
  change rationalWordWidth lo+rationalWordWidth hi+rationalWordWidth (lo+hi)+rationalWordWidth (2:ℚ)+rationalWordWidth result.1+
    literal+add+divide+GeneralPaperEncodedScalarStorage.fields W [16*W,literal,add,divide,16*W+literal,16*W+literal+add,result.2]+256*W≤_
  unfold profile
  change rationalWordWidth result.1≤4*R+7 at hM
  omega

end Blotto.GeneralPaperRayMidpointStorage
