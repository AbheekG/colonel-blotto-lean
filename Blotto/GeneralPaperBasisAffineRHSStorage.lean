import Blotto.GeneralPaperSourceBasisAdvanceStorageReachedRates

/-! Literal final affine RHS copy pass. Integer payload/copy scratch,
branch/index/native price fields, full fill buffers and returned vector
are owned. The full retained input basis is owned once by the caller. -/
namespace Blotto.GeneralPaperBasisAffineRHSStorage
open GeneralPaperBasisState GeneralPaperBasisStoredProducts GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def value {d : ℕ} (state : State d d) (useSlope : Bool) (i : Fin d) : ℤ :=
  if useSlope then (state.rows.read i).slope else (state.rows.read i).constant
def callbackPrice (model : RationalCostModel) (W R : ℕ) : ℕ := 16*W+model.rat R
def callbackCap (model : RationalCostModel) (W d R : ℕ) : ℕ := d+2+3*callbackPrice model W R
def callbackWindow {d : ℕ} (model : RationalCostModel) (W : ℕ) (state : State d d) (useSlope : Bool) (i : Fin d) : ℕ :=
  let a := value state useSlope i
  let c := model.rat (GeneralPaperIntegerPrimitivePrice.word a)
  integerBits a+c+fields W [d,i.val,useSlope.toNat,16*W,c,16*W+c]+128*W
def callbackProfile (model : RationalCostModel) (W d R : ℕ) : ℕ :=
  R+model.rat R+6*(natBits (callbackCap model W d R)+W)+160*W

theorem callback_bound {d : ℕ} (model : RationalCostModel) (W C R : ℕ) (state : State d d) (useSlope : Bool)
    (hc : ∀ i,(value state useSlope i).natAbs≤C) (hR : 1+binaryWordWidth C≤R) (i : Fin d) :
    callbackWindow model W state useSlope i≤callbackProfile model W d R := by
  let a := value state useSlope i
  let c := model.rat (GeneralPaperIntegerPrimitivePrice.word a)
  have hValue : integerBits a≤R := (Nat.add_le_add_left (binaryWordWidth_mono (hc i)) 1).trans hR
  have hCopy : c≤model.rat R := model.monotone hValue
  have hBool : useSlope.toNat≤1 := by cases useSlope <;> decide
  have hf := fields_bound W (natBits (callbackCap model W d R)) [d,i.val,useSlope.toNat,16*W,c,16*W+c] (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold callbackCap callbackPrice
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (callbackCap model W d R)+W)+32*W at hf
  unfold callbackWindow callbackProfile
  dsimp only
  dsimp only [a,c] at hValue hCopy hf
  omega

def callerCap (model : RationalCostModel) (W d R : ℕ) : ℕ :=
  d+2+3*GeneralPaperNativePayloadFillStorage.workCap W d (callbackPrice model W R)+16*W
def window {d : ℕ} (model : RationalCostModel) (W copied : ℕ) (state : State d d) (useSlope : Bool) : ℕ :=
  let callback := fun i => (value state useSlope i,16*W+model.rat (GeneralPaperIntegerPrimitivePrice.word (value state useSlope i)))
  let result := GeneralPaperBasisAffineBits.rhsRun model.rat W state useSlope
  GeneralPaperNativePayloadFillStorage.window W integerBits callback (callbackWindow model W state useSlope)
    (min copied d) (Nat.min_le_right _ _)+fields W [d,useSlope.toNat,result.2,16*W]+128*W
def profile (model : RationalCostModel) (W d R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W R d (callbackPrice model W R) (callbackProfile model W d R)+
    4*(natBits (callerCap model W d R)+W)+160*W

theorem bounded {d : ℕ} (model : RationalCostModel) (W copied C R : ℕ) (state : State d d) (useSlope : Bool)
    (hc : ∀ i,(value state useSlope i).natAbs≤C) (hR : 1+binaryWordWidth C≤R)
    (hW : 1≤W) (hD : binaryWordWidth (d+1)≤W) : window model W copied state useSlope≤profile model W d R := by
  let callback := fun i => (value state useSlope i,16*W+model.rat (GeneralPaperIntegerPrimitivePrice.word (value state useSlope i)))
  have hp (i) : integerBits (callback i).1≤R := (Nat.add_le_add_left (binaryWordWidth_mono (hc i)) 1).trans hR
  have hC (i) : (callback i).2≤callbackPrice model W R := Nat.add_le_add_left (model.monotone (hp i)) (16*W)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (callbackPrice model W R) (callbackProfile model W d R)
    integerBits callback (callbackWindow model W state useSlope) hp hC
    (callback_bound model W C R state useSlope hc hR) hW hD (min copied d) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (callbackPrice model W R) callback hC hW hD d le_rfl
  change (GeneralPaperBasisAffineBits.rhsRun model.rat W state useSlope).2≤GeneralPaperNativePayloadFillStorage.workCap W d (callbackPrice model W R) at hWork
  have hBool : useSlope.toNat≤1 := by cases useSlope <;> decide
  have hf := fields_bound W (natBits (callerCap model W d R)) [d,useSlope.toNat,(GeneralPaperBasisAffineBits.rhsRun model.rat W state useSlope).2,16*W] (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold callerCap
    rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (callerCap model W d R)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [callback] at hFill
  omega

end Blotto.GeneralPaperBasisAffineRHSStorage
