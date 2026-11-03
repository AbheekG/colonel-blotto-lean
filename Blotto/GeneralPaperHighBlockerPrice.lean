import Blotto.GeneralPaperNativeFixedScanPrice

/-! Complete original high-blocker recovery: priced rational midpoint,
early-exit scan of the fixed affine table, and one original-row decode.
The table invariant supplies the returned label length; no new DP is run.
-/
namespace Blotto.GeneralPaperHighBlockerPrice
open GeneralPaperRayAffineScoreStep GeneralPaperRayAffineDPSize GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {S K : ℕ} (primitive indexPrimitive : ℕ → ℕ) (W m : ℕ)
    (table : Table S K) (h : ℕ) (beta lo hi : ℚ) : Option (FixedArrayTable m (Fin K)) × ℕ :=
  let midpoint := GeneralPaperRayMidpointPrice.run primitive W lo hi
  let found := GeneralPaperFixedViolationPrice.run primitive W table h beta midpoint.1
  match found.value with
  | none => (none,midpoint.2+found.work+8*W)
  | some entry =>
    let row := GeneralPaperFixedTupleDecodePrice.run indexPrimitive W m entry.2
    (row.1,midpoint.2+found.work+row.2+16*W)

theorem data {S K : ℕ} (primitive indexPrimitive : ℕ → ℕ) (W m : ℕ)
    (table : Table S K) (h : ℕ) (beta lo hi : ℚ) :
    (run primitive indexPrimitive W m table h beta lo hi).1=GeneralPaperRayHighBlocker.extract m table h beta lo hi := by
  unfold run GeneralPaperRayHighBlocker.extract
  simp only [GeneralPaperRayMidpointPrice.data,GeneralPaperFixedViolationPrice.data]
  cases (GeneralPaperRayFixedViolation.run table h beta ((lo+hi)/2)).value <;>
    simp only [GeneralPaperFixedTupleDecodePrice.data,Option.bind_none,Option.bind_some]

def profile (m S W P : ℕ) : ℕ :=
  GeneralPaperFixedViolationPrice.profile S W P+96*(m+1)*W+32*W+5*P

theorem bit_work {S K : ℕ} (model : RationalCostModel) (W D E m X V P : ℕ)
    (hD : 0<D) (hE : 0<E) (table : Table S K) (hp : TableBounded D E X V m table)
    (h : ℕ) (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hIndex : binaryWordWidth (m+1)≤W) :
    (run model.rat (fun w => w) W m table h beta lo hi).2≤profile m S W (model.rat (6*width D E m X V P+9)) := by
  let R := width D E m X V P
  let Q := model.rat (6*R+9)
  let midpoint := GeneralPaperRayMidpointPrice.run model.rat W lo hi
  let found := GeneralPaperFixedViolationPrice.run model.rat W table h beta midpoint.1
  have hMid := GeneralPaperRayMidpointPrice.work model.rat model.monotone W R lo hi hl hh
  have hMono := model.monotone (show 4*R+7≤6*R+9 by omega)
  have hMid' : midpoint.2≤16*W+5*Q := by nlinarith only [hMid,hMono]
  have hHeight := GeneralPaperRayAffineBound.midpoint_height hl hh
  have hFound : found.work≤GeneralPaperFixedViolationPrice.profile S W Q :=
    GeneralPaperNativeFixedScanPrice.work model.rat model.monotone W D E m X V P m hD hE le_rfl
      table hp h beta hb ((lo+hi)/2) hHeight
  change _≤profile m S W Q
  rw [run]
  change (match found.value with
    | none => (none,midpoint.2+found.work+8*W)
    | some entry =>
      let row := GeneralPaperFixedTupleDecodePrice.run (fun w => w) W m entry.2
      (row.1,midpoint.2+found.work+row.2+16*W)).2≤_
  cases he : found.value with
  | none =>
    dsimp only
    unfold profile
    nlinarith only [hMid',hFound,Nat.zero_le (96*(m+1)*W)]
  | some entry =>
    have hLength := GeneralPaperNativeFixedScanPrice.selected_length model.rat W D E X V m table hp h beta midpoint.1 entry he
    have hi' : binaryWordWidth (entry.2.labels.length+1)≤W := by rw [hLength]; exact hIndex
    have hDecode := GeneralPaperFixedTupleDecodePrice.bit_work W m entry.2 hW hi'
    rw [hLength] at hDecode
    dsimp only
    unfold profile
    nlinarith only [hMid',hFound,hDecode]

theorem arithmetic_work {S K : ℕ} (D E m X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (table : Table S K) (hp : TableBounded D E X V m table) (h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    (run (fun _ => 1) (fun _ => 1) 1 m table h beta lo hi).2≤profile m S 1 1 := by
  let R := width D E m X V P
  let midpoint := GeneralPaperRayMidpointPrice.run (fun _ => 1) 1 lo hi
  let found := GeneralPaperFixedViolationPrice.run (fun _ => 1) 1 table h beta midpoint.1
  have hMid := GeneralPaperRayMidpointPrice.work (fun _ => 1) (fun _ _ _ => le_rfl) 1 R lo hi hl hh
  have hMid' : midpoint.2≤16+5 := hMid
  have hHeight := GeneralPaperRayAffineBound.midpoint_height hl hh
  have hFound : found.work≤GeneralPaperFixedViolationPrice.profile S 1 1 :=
    GeneralPaperNativeFixedScanPrice.work (fun _ => 1) (fun _ _ _ => le_rfl) 1 D E m X V P m hD hE le_rfl
      table hp h beta hb ((lo+hi)/2) hHeight
  rw [run]
  change (match found.value with
    | none => (none,midpoint.2+found.work+8*1)
    | some entry =>
      let row := GeneralPaperFixedTupleDecodePrice.run (fun _ => 1) 1 m entry.2
      (row.1,midpoint.2+found.work+row.2+16*1)).2≤_
  cases he : found.value with
  | none =>
    dsimp only
    unfold profile
    nlinarith only [hMid',hFound]
  | some entry =>
    have hLength := GeneralPaperNativeFixedScanPrice.selected_length (fun _ => 1) 1 D E X V m table hp h beta midpoint.1 entry he
    have hDecode := GeneralPaperFixedTupleDecodePrice.arithmetic_work m entry.2
    rw [hLength] at hDecode
    dsimp only
    unfold profile
    nlinarith only [hMid',hFound,hDecode]

end Blotto.GeneralPaperHighBlockerPrice
