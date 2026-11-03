import Blotto.GeneralPaperLightFieldScanConstructionStorage

/-! Literal reduced rational-array construction. Each original heavy
weight is cast/divided; the common representative is built once and then
referenced. All buffers, scalar operands, scratch and native work fields
are bounded from retained short integer values. -/
namespace Blotto.GeneralPaperReducedValueArrayConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperReducedValueArrayPrice GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

def ratioPrice (model : RationalCostModel) (A Q R : ℕ) : ℕ := 3*model.rat (width Q R)+32*A
def ratioWindow (model : RationalCostModel) (A Q w : ℕ) : ℕ :=
  let cast := model.rat (rationalWordWidth (w:ℚ))
  let divide := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) w Q
  rationalWordWidth (w:ℚ)+rationalWordWidth (Q:ℚ)+rationalWordWidth ((w:ℚ)/Q)+cast+divide+
    fields A [Q,w,cast,divide,32*A,cast+divide,cast+divide+32*A]+128*A
def ratioProfile (model : RationalCostModel) (A Q R : ℕ) : ℕ :=
  3*width Q R+3*model.rat (width Q R)+7*(natBits (Q+ratioPrice model A Q R+1)+A)+160*A

theorem ratio_work (model : RationalCostModel) (A Q R w : ℕ) (hw : w≤Q) :
    model.rat (rationalWordWidth (w:ℚ))+
      GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) w Q+32*A≤ratioPrice model A Q R := by
  have hc := model.monotone (cast_width w Q R hw)
  have hd := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) w Q _
    (cast_width w Q R hw) (cast_width Q Q R le_rfl) (ratio_width w Q R hw)
  unfold ratioPrice
  omega

theorem ratio_bounded (model : RationalCostModel) (A Q R w : ℕ) (hw : w≤Q) :
    ratioWindow model A Q w≤ratioProfile model A Q R := by
  let cast := model.rat (rationalWordWidth (w:ℚ))
  let divide := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) w Q
  have hCast := cast_width w Q R hw
  have hQ := cast_width Q Q R le_rfl
  have hRatio := ratio_width w Q R hw
  have hp : cast≤model.rat (width Q R) := model.monotone hCast
  have hd : divide≤2*model.rat (width Q R) :=
    GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) w Q _ hCast hQ hRatio
  have hWork := ratio_work model A Q R w hw
  change cast+divide+32*A≤ratioPrice model A Q R at hWork
  have hf := fields_bound A (natBits (Q+ratioPrice model A Q R+1)) [Q,w,cast,divide,32*A,cast+divide,cast+divide+32*A] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields A _≤7*(natBits (Q+ratioPrice model A Q R+1)+A)+32*A at hf
  change rationalWordWidth (w:ℚ)+rationalWordWidth (Q:ℚ)+rationalWordWidth ((w:ℚ)/Q)+cast+divide+
    fields A [Q,w,cast,divide,32*A,cast+divide,cast+divide+32*A]+128*A≤_
  unfold ratioProfile
  omega

def identityCallback {n : ℕ} (model : RationalCostModel) (A Q : ℕ) (weights : FixedArrayTable n ℕ) (j : Fin n) : ℚ×ℕ :=
  let w := weights.read j
  ((w:ℚ)/Q,model.rat (rationalWordWidth (w:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) w Q+32*A)
def identityScalar {n : ℕ} (model : RationalCostModel) (A Q : ℕ) (weights : FixedArrayTable n ℕ) (j : Fin n) : ℕ :=
  ratioWindow model A Q (weights.read j)+fields A [j.val]+64*A
def identityScalarProfile (model : RationalCostModel) (A n Q : ℕ) : ℕ := ratioProfile model A Q 1+(natBits n+A)+96*A

theorem identity_scalar {n : ℕ} (model : RationalCostModel) (A Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hw : ∀ j,weights.read j≤Q) (j : Fin n) :
    identityScalar model A Q weights j≤ identityScalarProfile model A n Q := by
  have hr := ratio_bounded model A Q 1 (weights.read j) (hw j)
  have hf := fields_bound A (natBits n) [j.val] (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    subst z
    exact Nat.add_le_add_left (binaryWordWidth_mono j.isLt.le) 1)
  change fields A _≤1*(natBits n+A)+32*A at hf
  unfold identityScalar identityScalarProfile
  omega

def identityPrice (model : RationalCostModel) (W n Q : ℕ) : ℕ :=
  let A := arrayWord W n
  GeneralPaperNativePayloadFillStorage.workCap A n (ratioPrice model A Q 1)+model.rat (width Q 1)+128*A
def identityCap (model : RationalCostModel) (W n Q : ℕ) : ℕ := n+Q+arrayWord W n+identityPrice model W n Q+128*arrayWord W n+1

def identityWindow {n : ℕ} (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) : ℕ :=
  let A := arrayWord W n
  let stored := PaperIndexedArrayConstruction.run (fun w => w) A (identityCallback model A Q weights)
  let cast := model.rat (rationalWordWidth (Q:ℚ))
  let made := GeneralPaperReducedValueArray.identity true model W Q weights
  arrayFootprint A natBits weights+rationalWordWidth (Q:ℚ)+cast+
    GeneralPaperNativePayloadFillStorage.window A rationalWordWidth (identityCallback model A Q weights) (identityScalar model A Q weights) count hc+
    fields A [n,Q,A,stored.2,cast,128*A,stored.2+cast,made.2]+128*A

def identityProfile (model : RationalCostModel) (W n Q : ℕ) : ℕ :=
  let A := arrayWord W n
  arrayProfile A n (natBits Q)+width Q 1+model.rat (width Q 1)+
    GeneralPaperNativePayloadFillStorage.profile A (width Q 1) n (ratioPrice model A Q 1) (identityScalarProfile model A n Q)+
    8*(natBits (identityCap model W n Q)+A)+160*A

theorem identity_work {n : ℕ} (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hw : ∀ j,weights.read j≤Q) : (GeneralPaperReducedValueArray.identity true model W Q weights).2≤ identityPrice model W n Q := by
  let A := arrayWord W n
  have hFill := GeneralPaperNativePayloadFillStorage.prefix_work A (ratioPrice model A Q 1) (identityCallback model A Q weights)
    (fun j => ratio_work model A Q 1 _ (hw j)) (GeneralPaperSummaryArrayControls.array_word_positive W n)
    (GeneralPaperSummaryArrayControls.array_index W n n le_rfl) n le_rfl
  change (PaperIndexedArrayConstruction.run (fun w => w) A (identityCallback model A Q weights)).2≤
    GeneralPaperNativePayloadFillStorage.workCap A n (ratioPrice model A Q 1) at hFill
  have hCast := model.monotone (cast_width Q Q 1 le_rfl)
  change (PaperIndexedArrayConstruction.run (fun w => w) A (identityCallback model A Q weights)).2+
    model.rat (rationalWordWidth (Q:ℚ))+128*A≤_
  unfold identityPrice
  change _≤GeneralPaperNativePayloadFillStorage.workCap A n (ratioPrice model A Q 1)+model.rat (width Q 1)+128*A
  omega

theorem identity_bounded {n : ℕ} (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hw : ∀ j,weights.read j≤Q) (count : ℕ) (hc : count≤n) :
    identityWindow model W Q weights count hc≤ identityProfile model W n Q := by
  let A := arrayWord W n
  have hInput := array_bound A (natBits Q) natBits weights (fun j => Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded A (width Q 1) (ratioPrice model A Q 1) (identityScalarProfile model A n Q)
    rationalWordWidth (identityCallback model A Q weights) (identityScalar model A Q weights)
    (fun j => ratio_width _ Q 1 (hw j)) (fun j => ratio_work model A Q 1 _ (hw j)) (identity_scalar model A Q weights hw)
    (GeneralPaperSummaryArrayControls.array_word_positive W n) (GeneralPaperSummaryArrayControls.array_index W n n le_rfl) count hc
  have hWork := identity_work model W Q weights hw
  have hShape : (GeneralPaperReducedValueArray.identity true model W Q weights).2=
      (PaperIndexedArrayConstruction.run (fun w => w) A (identityCallback model A Q weights)).2+
      model.rat (rationalWordWidth (Q:ℚ))+128*A := rfl
  have hQ := cast_width Q Q 1 le_rfl
  have hCast := model.monotone hQ
  have hf := fields_bound A (natBits (identityCap model W n Q))
    [n,Q,A,(PaperIndexedArrayConstruction.run (fun w => w) A (identityCallback model A Q weights)).2,
      model.rat (rationalWordWidth (Q:ℚ)),128*A,
      (PaperIndexedArrayConstruction.run (fun w => w) A (identityCallback model A Q weights)).2+model.rat (rationalWordWidth (Q:ℚ)),
      (GeneralPaperReducedValueArray.identity true model W Q weights).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold identityCap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [A] at * <;> omega)
  change fields A _≤8*(natBits (identityCap model W n Q)+A)+32*A at hf
  unfold identityWindow identityProfile
  dsimp only [A] at *
  omega

def replacedCallback {n : ℕ} (model : RationalCostModel) (A Q R L : ℕ) (weights : FixedArrayTable n ℕ)
    (heavy : Array (Fin n)) (j : Fin (heavy.size+R)) : ℚ×ℕ :=
  GeneralPaperReducedValueArray.coordinate true model A Q ((L:ℚ)/(Q*R:ℕ)) weights heavy j

def sourceWindow {n R : ℕ} (model : RationalCostModel) (A Q : ℕ) (weights : FixedArrayTable n ℕ)
    (heavy : Array (Fin n)) (j : Fin (heavy.size+R)) : ℕ :=
  if hj : j.val<heavy.size then ratioWindow model A Q (weights.read heavy[j.val])+fields A [heavy[j.val].val]+64*A else 0
def sourceProfile (model : RationalCostModel) (A n Q R : ℕ) : ℕ := ratioProfile model A Q R+(natBits n+A)+96*A

theorem source_bounded {n R : ℕ} (model : RationalCostModel) (A Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hw : ∀ j,weights.read j≤Q) (heavy : Array (Fin n)) (j : Fin (heavy.size+R)) :
    sourceWindow model A Q weights heavy j≤sourceProfile model A n Q R := by
  unfold sourceWindow
  split_ifs with hj
  · have hr := ratio_bounded model A Q R (weights.read heavy[j.val]) (hw _)
    have hf := fields_bound A (natBits n) [heavy[j.val].val] (by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      subst z
      exact Nat.add_le_add_left (binaryWordWidth_mono heavy[j.val].isLt.le) 1)
    change fields A _≤1*(natBits n+A)+32*A at hf
    unfold sourceProfile
    omega
  · exact Nat.zero_le _

def coordinatePrice (model : RationalCostModel) (A Q R : ℕ) : ℕ := 3*model.rat (width Q R)+64*A
def coordinateCap (model : RationalCostModel) (A n h Q R : ℕ) : ℕ := n+h+R+coordinatePrice model A Q R+64*A+1

def replacedScalar {n : ℕ} (model : RationalCostModel) (W Q R L : ℕ) (weights : FixedArrayTable n ℕ)
    (heavy : Array (Fin n)) (j : Fin (heavy.size+R)) : ℕ :=
  let A := arrayWord W (n+heavy.size+R)
  let compare := GeneralPaperIntegerWordPrice.compare (fun w => w) j.val heavy.size
  rationalWordWidth ((L:ℚ)/(Q*R:ℕ))+compare+sourceWindow model A Q weights heavy j+
    fields A [n,heavy.size,R,j.val,compare,32*A,(replacedCallback model A Q R L weights heavy j).2]+128*A
def replacedScalarProfile (model : RationalCostModel) (W n h Q R : ℕ) : ℕ :=
  let A := arrayWord W (n+h+R)
  width Q R+A+sourceProfile model A n Q R+7*(natBits (coordinateCap model A n h Q R)+A)+160*A

theorem replaced_payload {n : ℕ} (model : RationalCostModel) (A Q R L : ℕ) (weights : FixedArrayTable n ℕ)
    (hw : ∀ j,weights.read j≤Q) (heavy : Array (Fin n)) (hL : L≤Q) (j : Fin (heavy.size+R)) :
    rationalWordWidth (replacedCallback model A Q R L weights heavy j).1≤width Q R := by
  unfold replacedCallback GeneralPaperReducedValueArray.coordinate
  split_ifs
  · exact ratio_width _ Q R (hw _)
  · exact representative_width L Q R hL

theorem replaced_scalar {n : ℕ} (model : RationalCostModel) (W Q R L : ℕ) (weights : FixedArrayTable n ℕ)
    (hw : ∀ j,weights.read j≤Q) (heavy : Array (Fin n)) (hL : L≤Q) (j : Fin (heavy.size+R)) :
    replacedScalar model W Q R L weights heavy j≤replacedScalarProfile model W n heavy.size Q R := by
  let A := arrayWord W (n+heavy.size+R)
  let compare := GeneralPaperIntegerWordPrice.compare (fun w => w) j.val heavy.size
  have hCompare : compare≤A := GeneralPaperIntegerWordPrice.compare_le (fun w => w) (fun _ _ h => h) j.val heavy.size A
    (control_word W _ _ (by omega)) (control_word W _ _ (by omega))
  have hWork := coordinate_bit_work model W Q R ((L:ℚ)/(Q*R:ℕ)) weights hw heavy j
  change (replacedCallback model A Q R L weights heavy j).2≤coordinatePrice model A Q R at hWork
  have hSource := source_bounded model A Q weights hw heavy j
  have hPayload := representative_width L Q R hL
  have hj := j.isLt.le
  have hf := fields_bound A (natBits (coordinateCap model A n heavy.size Q R))
    [n,heavy.size,R,j.val,compare,32*A,(replacedCallback model A Q R L weights heavy j).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold coordinateCap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields A _≤7*(natBits (coordinateCap model A n heavy.size Q R)+A)+32*A at hf
  change rationalWordWidth ((L:ℚ)/(Q*R:ℕ))+compare+sourceWindow model A Q weights heavy j+
    fields A [n,heavy.size,R,j.val,compare,32*A,(replacedCallback model A Q R L weights heavy j).2]+128*A≤_
  unfold replacedScalarProfile
  change _≤width Q R+A+sourceProfile model A n Q R+7*(natBits (coordinateCap model A n heavy.size Q R)+A)+160*A
  omega

def replacedPrice (model : RationalCostModel) (W n h Q R : ℕ) : ℕ :=
  let A := arrayWord W (n+h+R)
  GeneralPaperNativePayloadFillStorage.workCap A (h+R) (coordinatePrice model A Q R)+7*model.rat (width Q R)+128*A
def replacedCap (model : RationalCostModel) (W n h Q R L : ℕ) : ℕ :=
  n+h+R+Q+L+Q*R+arrayWord W (n+h+R)+replacedPrice model W n h Q R+128*arrayWord W (n+h+R)+1

def replacedControls {n : ℕ} (model : RationalCostModel) (W Q R L : ℕ) (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n)) : List ℕ :=
  let A := arrayWord W (n+heavy.size+R)
  let stored := PaperIndexedArrayConstruction.run (fun w => w) A (replacedCallback model A Q R L weights heavy)
  let multiply := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) Q R
  let castDen := model.rat (rationalWordWidth ((Q*R:ℕ):ℚ))
  let castL := model.rat (rationalWordWidth (L:ℚ))
  let castQ := model.rat (rationalWordWidth (Q:ℚ))
  let divide := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) L (Q*R:ℕ)
  let made := GeneralPaperReducedValueArray.replaced true model W Q R L weights heavy
  [n,heavy.size,R,Q,L,Q*R,A,stored.2,multiply,castDen,castL,castQ,divide,128*A,made.2,
    stored.2+multiply,stored.2+multiply+castDen,stored.2+multiply+castDen+castL,
    stored.2+multiply+castDen+castL+castQ,stored.2+multiply+castDen+castL+castQ+divide]

def replacedWindow {n : ℕ} (model : RationalCostModel) (W Q R L : ℕ) (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n))
    (count : ℕ) (hc : count≤heavy.size+R) : ℕ :=
  let A := arrayWord W (n+heavy.size+R)
  arrayFootprint A natBits weights+
    GeneralPaperEncodedReferenceVector.footprint A (fun j : Fin n => natBits j.val) heavy+
    rationalWordWidth (Q:ℚ)+rationalWordWidth ((Q*R:ℕ):ℚ)+rationalWordWidth (L:ℚ)+rationalWordWidth ((L:ℚ)/(Q*R:ℕ))+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) Q R+
    model.rat (rationalWordWidth ((Q*R:ℕ):ℚ))+model.rat (rationalWordWidth (L:ℚ))+model.rat (rationalWordWidth (Q:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) L (Q*R:ℕ)+
    GeneralPaperNativePayloadFillStorage.window A rationalWordWidth (replacedCallback model A Q R L weights heavy)
      (replacedScalar model W Q R L weights heavy) count hc+fields A (replacedControls model W Q R L weights heavy)+128*A

def replacedProfile (model : RationalCostModel) (W n h Q R : ℕ) : ℕ :=
  let A := arrayWord W (n+h+R)
  arrayProfile A n (natBits Q)+(h*(natBits n+A)+64*A)+4*width Q R+replacedPrice model W n h Q R+
    GeneralPaperNativePayloadFillStorage.profile A (width Q R) (h+R) (coordinatePrice model A Q R) (replacedScalarProfile model W n h Q R)+
    20*(natBits (replacedCap model W n h Q R Q)+A)+160*A

theorem replaced_work {n : ℕ} (model : RationalCostModel) (W Q R L : ℕ) (weights : FixedArrayTable n ℕ)
    (hw : ∀ j,weights.read j≤Q) (heavy : Array (Fin n)) (hL : L≤Q) :
    (GeneralPaperReducedValueArray.replaced true model W Q R L weights heavy).2≤replacedPrice model W n heavy.size Q R := by
  have h := replaced_bit_work model W Q R L weights hw heavy hL
  unfold replacedPrice GeneralPaperNativePayloadFillStorage.workCap coordinatePrice
  dsimp only
  nlinarith only [h,Nat.zero_le ((heavy.size+R+1)*arrayWord W (n+heavy.size+R))]

theorem replaced_bounded {n : ℕ} (model : RationalCostModel) (W Q R L : ℕ) (weights : FixedArrayTable n ℕ)
    (hw : ∀ j,weights.read j≤Q) (heavy : Array (Fin n)) (hL : L≤Q) (count : ℕ) (hc : count≤heavy.size+R) :
    replacedWindow model W Q R L weights heavy count hc≤replacedProfile model W n heavy.size Q R := by
  let A := arrayWord W (n+heavy.size+R)
  let stored := PaperIndexedArrayConstruction.run (fun w => w) A (replacedCallback model A Q R L weights heavy)
  let multiply := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) Q R
  let castDen := model.rat (rationalWordWidth ((Q*R:ℕ):ℚ))
  let castL := model.rat (rationalWordWidth (L:ℚ))
  let castQ := model.rat (rationalWordWidth (Q:ℚ))
  let divide := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) L (Q*R:ℕ)
  have hInput := array_bound A (natBits Q) natBits weights (fun j => Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1)
  have hHeavy := GeneralPaperEncodedReferenceVector.bounded A (natBits n) (fun j : Fin n => natBits j.val) heavy
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono heavy[i.val].isLt.le) 1)
  have hA := GeneralPaperSummaryArrayControls.array_word_positive W (n+heavy.size+R)
  have hIndex : binaryWordWidth (heavy.size+R+1)≤A := GeneralPaperSummaryArrayControls.array_index W _ _ (by omega)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded A (width Q R) (coordinatePrice model A Q R) (replacedScalarProfile model W n heavy.size Q R)
    rationalWordWidth (replacedCallback model A Q R L weights heavy) (replacedScalar model W Q R L weights heavy)
    (replaced_payload model A Q R L weights hw heavy hL) (coordinate_bit_work model W Q R _ weights hw heavy)
    (replaced_scalar model W Q R L weights hw heavy hL) hA hIndex count hc
  have hWork := replaced_work model W Q R L weights hw heavy hL
  have hShape : (GeneralPaperReducedValueArray.replaced true model W Q R L weights heavy).2=
      stored.2+multiply+castDen+castL+castQ+divide+128*A := rfl
  have hQ := cast_width Q Q R le_rfl
  have hDen := denominator_width Q R
  have hL' := cast_width L Q R hL
  have hRep := representative_width L Q R hL
  have hScratch : multiply+castDen+castL+castQ+divide≤replacedPrice model W n heavy.size Q R := by omega
  have hf := fields_bound A (natBits (replacedCap model W n heavy.size Q R Q)) (replacedControls model W Q R L weights heavy) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [replacedControls,List.mem_cons,List.not_mem_nil,or_false] at hz
    change z=n ∨ z=heavy.size ∨ z=R ∨ z=Q ∨ z=L ∨ z=Q*R ∨ z=A ∨ z=stored.2 ∨ z=multiply ∨ z=castDen ∨
      z=castL ∨ z=castQ ∨ z=divide ∨ z=128*A ∨ z=(GeneralPaperReducedValueArray.replaced true model W Q R L weights heavy).2 ∨
      z=stored.2+multiply ∨ z=stored.2+multiply+castDen ∨ z=stored.2+multiply+castDen+castL ∨
      z=stored.2+multiply+castDen+castL+castQ ∨ z=stored.2+multiply+castDen+castL+castQ+divide at hz
    unfold replacedCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [A] at * <;> omega)
  change fields A _≤20*(natBits (replacedCap model W n heavy.size Q R Q)+A)+32*A at hf
  change arrayFootprint A natBits weights+GeneralPaperEncodedReferenceVector.footprint A (fun j : Fin n => natBits j.val) heavy+
    rationalWordWidth (Q:ℚ)+rationalWordWidth ((Q*R:ℕ):ℚ)+rationalWordWidth (L:ℚ)+rationalWordWidth ((L:ℚ)/(Q*R:ℕ))+
    multiply+castDen+castL+castQ+divide+
    GeneralPaperNativePayloadFillStorage.window A rationalWordWidth (replacedCallback model A Q R L weights heavy)
      (replacedScalar model W Q R L weights heavy) count hc+fields A (replacedControls model W Q R L weights heavy)+128*A≤_
  unfold replacedProfile
  dsimp only [A] at *
  omega

def prefixPeak (n : ℕ) (f : (count : ℕ) → count≤n → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin (n+1))).sup (fun j => f j.val (Nat.le_of_lt_succ j.isLt))

theorem prefix_peak_bound (n P : ℕ) (f : (count : ℕ) → count≤n → ℕ) (hf : ∀ count hc,f count hc≤P) : prefixPeak n f≤P := by
  apply Finset.sup_le
  intro j _
  exact hf j.val _

theorem prefix_le_peak (n : ℕ) (f : (count : ℕ) → count≤n → ℕ) (count : ℕ) (hc : count≤n) :
    f count hc≤prefixPeak n f :=
  Finset.le_sup (f:=fun j : Fin (n+1) => f j.val (Nat.le_of_lt_succ j.isLt))
    (Finset.mem_univ (⟨count,by omega⟩:Fin (n+1)))

@[fun_prop]
theorem identity_scaling (model : RationalCostModel) (n Q : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => identityProfile model W n Q) := by
  unfold identityProfile identityScalarProfile identityCap identityPrice ratioProfile ratioPrice
    GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap arrayProfile arrayWord
  dsimp only
  fun_prop

@[fun_prop]
theorem replaced_scaling (model : RationalCostModel) (n h Q R : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => replacedProfile model W n h Q R) := by
  unfold replacedProfile replacedScalarProfile sourceProfile coordinateCap coordinatePrice replacedCap replacedPrice ratioProfile ratioPrice
    GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap arrayProfile arrayWord
  dsimp only [coordinatePrice]
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem identity_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n Q : Input → ℕ) (hW : Tight W) (hn : Small n) (hQ : Small Q) :
    Linear (fun x => identityProfile model (W x) (n x) (Q x)) n := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  have hWidth : Polylog (fun x => width (Q x) 1) := by unfold width;fun_prop
  have hWidthSmall := small_of_poly hWidth
  have hRat : Polylog (fun x => model.rat (width (Q x) 1)) := primitive_preserves hg hWidth hWidthSmall
  have hRatSmall := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hWidthSmall
  have hWL : Linear (fun x => width (Q x) 1) n := linear_poly _ n hWidth
  have hRL : Linear (fun x => model.rat (width (Q x) 1)) n := linear_poly _ n hRat
  unfold identityProfile identityScalarProfile identityCap identityPrice ratioProfile ratioPrice
    GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap arrayProfile arrayWord natBits
  dsimp only
  fun_prop (config := {maxSteps := 4000})

theorem replaced_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n h Q R : Input → ℕ) (hW : Tight W) (hn : Small n) (hh : Small h) (hQ : Small Q) (hR : Small R) :
    Linear (fun x => replacedProfile model (W x) (n x) (h x) (Q x) (R x)) (fun x => n x+h x+R x) := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  have hWidth : Polylog (fun x => width (Q x) (R x)) := by unfold width;fun_prop
  have hWidthSmall := small_of_poly hWidth
  have hRat : Polylog (fun x => model.rat (width (Q x) (R x))) := primitive_preserves hg hWidth hWidthSmall
  have hRatSmall := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hWidthSmall
  have hWL : Linear (fun x => width (Q x) (R x)) (fun x => n x+h x+R x) := linear_poly _ _ hWidth
  have hRL : Linear (fun x => model.rat (width (Q x) (R x))) (fun x => n x+h x+R x) := linear_poly _ _ hRat
  have hNL : Linear n (fun x => n x+h x+R x) := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by dsimp only;omega)
  have hHL : Linear h (fun x => n x+h x+R x) := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by dsimp only;omega)
  have hReL : Linear R (fun x => n x+h x+R x) := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by dsimp only;omega)
  unfold replacedProfile replacedScalarProfile sourceProfile coordinateCap coordinatePrice replacedCap replacedPrice ratioProfile ratioPrice
    GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap arrayProfile arrayWord natBits
  dsimp only [coordinatePrice]
  fun_prop (config := {maxSteps := 4000})

end Blotto.GeneralPaperReducedValueArrayConstructionStorage
