import Blotto.GeneralPaperSourceBasisDenseConstructionReachedRates

/-! Literal integer dot-loop storage before cancellation: every visited
operand/product/accumulator/result, primitive scratch and encoded native
spent/partial return. Whole reader arrays are retained by the caller once.
No integer magnitude or metadata observer executes in the algorithm. -/
namespace Blotto.GeneralPaperIntegerDotStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def stepCap (model : RationalCostModel) (W R : ℕ) : ℕ := 48*W+4*model.rat R
def metadataCap (model : RationalCostModel) (W n R B : ℕ) : ℕ := n+1+3*(B+2*W)+stepCap model W R+48*W

theorem value_bound {i : Type*} (model : RationalCostModel) (W X Y : ℕ) (f g : i → ℤ) (xs : List i) (a : ℤ) (spent : ℕ)
    (hf : ∀ j∈xs,(f j).natAbs≤X) (hg : ∀ j∈xs,(g j).natAbs≤Y) :
    (GeneralPaperIntegerDotPrice.loop model.rat W f g xs a spent).value.natAbs≤a.natAbs+xs.length*X*Y := by
  rw [GeneralPaperIntegerDotPrice.loop_data model.rat W f g xs a spent 0]
  exact GeneralPaperIntegerDotSize.loop_bound f g xs a 0 X Y hf hg

def frame {n : ℕ} (model : RationalCostModel) (W : ℕ) (f g : Fin n → ℤ) (xs : List (Fin n)) (a : ℤ) (spent : ℕ) : ℕ :=
  let result := GeneralPaperIntegerDotPrice.loop model.rat W f g xs a spent
  match xs with
  | [] => integerBits a+integerBits result.value+fields W [n,0,spent,result.work,2*W]+128*W
  | j::rest =>
    let product := f j*g j
    let sum := a+product
    let mul := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) (f j) (g j)
    let add := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x+y) a product
    integerBits (f j)+integerBits (g j)+integerBits a+integerBits product+integerBits sum+integerBits result.value+mul+add+
      fields W [n,(j::rest).length,j.val,spent,mul,add,result.work,spent+48*W+mul+add,mul+add,48*W]+256*W

def frameProfile (model : RationalCostModel) (W n R B : ℕ) : ℕ :=
  6*R+4*model.rat R+10*(natBits (metadataCap model W n R B)+W)+288*W

theorem frame_bound {n : ℕ} (model : RationalCostModel) (W X Y M R B : ℕ) (hX : X≤M) (hY : Y≤M)
    (hR : 1+binaryWordWidth M≤R) (f g : Fin n → ℤ) (xs : List (Fin n)) (a : ℤ) (spent : ℕ)
    (hf : ∀ j∈xs,(f j).natAbs≤X) (hg : ∀ j∈xs,(g j).natAbs≤Y) (hn : xs.length≤n)
    (hm : a.natAbs+xs.length*X*Y≤M) (hb : spent+xs.length*stepCap model W R≤B) :
    frame model W f g xs a spent≤frameProfile model W n R B := by
  let result := GeneralPaperIntegerDotPrice.loop model.rat W f g xs a spent
  have hA : integerBits a≤R := (Nat.add_le_add_left (binaryWordWidth_mono (show a.natAbs≤M by omega)) 1).trans hR
  have hResult : integerBits result.value≤R := (Nat.add_le_add_left (binaryWordWidth_mono
    ((value_bound model W X Y f g xs a spent hf hg).trans hm)) 1).trans hR
  have hRawWork := GeneralPaperIntegerDotPrice.loop_work model.rat model.monotone W X Y M hX hY f g xs hf hg a spent hm
  change result.work≤spent+xs.length*(48*W+4*model.rat (1+binaryWordWidth M))+2*W at hRawWork
  have hPay := Nat.mul_le_mul_left xs.length (Nat.add_le_add_left (Nat.mul_le_mul_left 4 (model.monotone hR)) (48*W))
  have hWork : result.work≤B+2*W := by unfold stepCap at hb; omega
  cases xs with
  | nil =>
    have hf' := fields_bound W (natBits (metadataCap model W n R B)) [n,0,spent,result.work,2*W] (by
      intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; simp only [List.length_nil,Nat.zero_mul,Nat.add_zero] at hb; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (metadataCap model W n R B)+W)+32*W at hf'
    unfold frame frameProfile
    dsimp only
    dsimp only [result] at hResult hf'
    omega
  | cons j rest =>
    have hF := (hf j List.mem_cons_self).trans hX
    have hG := (hg j List.mem_cons_self).trans hY
    have hProduct : (f j*g j).natAbs≤X*Y := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hf j List.mem_cons_self) (hg j List.mem_cons_self)
    have hSplit : a.natAbs+rest.length*X*Y+X*Y≤M := by simpa only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hm
    have hP : (f j*g j).natAbs≤M := by omega
    have hSum : (a+f j*g j).natAbs≤M := ((Int.natAbs_add_le _ _).trans (Nat.add_le_add_left hProduct _)).trans (by omega)
    have hFW : integerBits (f j)≤R := (Nat.add_le_add_left (binaryWordWidth_mono hF) 1).trans hR
    have hGW : integerBits (g j)≤R := (Nat.add_le_add_left (binaryWordWidth_mono hG) 1).trans hR
    have hPW : integerBits (f j*g j)≤R := (Nat.add_le_add_left (binaryWordWidth_mono hP) 1).trans hR
    have hSW : integerBits (a+f j*g j)≤R := (Nat.add_le_add_left (binaryWordWidth_mono hSum) 1).trans hR
    have hMul := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x*y) (f j) (g j) M hF hG hP).trans (Nat.mul_le_mul_left 2 (model.monotone hR))
    have hAdd := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x+y) a (f j*g j) M (by omega) hP hSum).trans (Nat.mul_le_mul_left 2 (model.monotone hR))
    let mul := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) (f j) (g j)
    let add := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x+y) a (f j*g j)
    have hNextSpent : spent+48*W+mul+add≤B := by
      have h := Nat.le_mul_of_pos_left (stepCap model W R) (show 0<(j::rest).length by simp)
      unfold stepCap at hb h
      omega
    have hf' := fields_bound W (natBits (metadataCap model W n R B))
      [n,(j::rest).length,j.val,spent,mul,add,result.work,spent+48*W+mul+add,mul+add,48*W] (by
        intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤10*(natBits (metadataCap model W n R B)+W)+32*W at hf'
    unfold frame frameProfile
    dsimp only
    dsimp only [result,mul,add] at hResult hf' hNextSpent
    omega

def loopWindow {n : ℕ} (model : RationalCostModel) (W : ℕ) (f g : Fin n → ℤ) : List (Fin n) → ℤ → ℕ → ℕ
  | [],a,spent => frame model W f g [] a spent
  | j::rest,a,spent => frame model W f g (j::rest) a spent+
      loopWindow model W f g rest (a+f j*g j) (spent+48*W+
        GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) (f j) (g j)+
        GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x+y) a (f j*g j))

theorem loop_bound {n : ℕ} (model : RationalCostModel) (W X Y M R B : ℕ) (hX : X≤M) (hY : Y≤M)
    (hR : 1+binaryWordWidth M≤R) (f g : Fin n → ℤ) (xs : List (Fin n)) (a : ℤ) (spent : ℕ)
    (hf : ∀ j∈xs,(f j).natAbs≤X) (hg : ∀ j∈xs,(g j).natAbs≤Y) (hn : xs.length≤n)
    (hm : a.natAbs+xs.length*X*Y≤M) (hb : spent+xs.length*stepCap model W R≤B) :
    loopWindow model W f g xs a spent≤(xs.length+1)*frameProfile model W n R B := by
  induction xs generalizing a spent with
  | nil => simpa only [loopWindow,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound model W X Y M R B hX hY hR f g [] a spent hf hg hn hm hb
  | cons j rest ih =>
    have hFrame := frame_bound model W X Y M R B hX hY hR f g (j::rest) a spent hf hg hn hm hb
    have hProduct : (f j*g j).natAbs≤X*Y := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hf j List.mem_cons_self) (hg j List.mem_cons_self)
    have hSplit : a.natAbs+rest.length*X*Y+X*Y≤M := by simpa only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hm
    have hSum : (a+f j*g j).natAbs≤a.natAbs+X*Y := (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left hProduct _)
    have hMul := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x*y) (f j) (g j) M
      ((hf j List.mem_cons_self).trans hX) ((hg j List.mem_cons_self).trans hY) (hProduct.trans (by omega))).trans (Nat.mul_le_mul_left 2 (model.monotone hR))
    have hAdd := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x+y) a (f j*g j) M
      (by omega) (hProduct.trans (by omega)) (hSum.trans (by omega))).trans (Nat.mul_le_mul_left 2 (model.monotone hR))
    have hBudget : spent+48*W+GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) (f j) (g j)+
        GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x+y) a (f j*g j)+rest.length*stepCap model W R≤B := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hb
      unfold stepCap at hb ⊢
      omega
    have hRest := ih (a+f j*g j) (spent+48*W+
      GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) (f j) (g j)+
      GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x+y) a (f j*g j))
      (fun j hj => hf j (List.mem_cons_of_mem _ hj)) (fun j hj => hg j (List.mem_cons_of_mem _ hj))
      (by simp only [List.length_cons] at hn; omega) (by nlinarith only [hSum,hSplit]) hBudget
    exact (Nat.add_le_add hFrame hRest).trans_eq (by simp only [List.length_cons]; ring)

def callerCap (model : RationalCostModel) (W n R : ℕ) : ℕ := n+1+3*(n*stepCap model W R+2*W+16*(n+1)*W)+16*(n+1)*W
def window {n : ℕ} (model : RationalCostModel) (W copied : ℕ) (f g : Fin n → ℤ) : ℕ :=
  let inner := GeneralPaperIntegerDotPrice.loop model.rat W f g (List.finRange n) 0 0
  let result := GeneralPaperIntegerDotPrice.run model.rat W f g
  GeneralPaperFinRangeStorage.window W n copied+loopWindow model W f g (List.finRange n) 0 0+integerBits result.value+
    fields W [n,inner.work,result.work,inner.work+16*(n+1)*W,16*(n+1)*W]+192*W
def profile (model : RationalCostModel) (W n R : ℕ) : ℕ := GeneralPaperFinRangeStorage.profile W n+
  (n+1)*frameProfile model W n R (n*stepCap model W R)+R+5*(natBits (callerCap model W n R)+W)+224*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W copied X Y R : ℕ) (f g : Fin n → ℤ)
    (hf : ∀ j,(f j).natAbs≤X) (hg : ∀ j,(g j).natAbs≤Y)
    (hR : 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n X Y)≤R) :
    window model W copied f g≤profile model W n R := by
  let M := GeneralPaperIntegerDotPrice.cap n X Y
  let inner := GeneralPaperIntegerDotPrice.loop model.rat W f g (List.finRange n) 0 0
  let result := GeneralPaperIntegerDotPrice.run model.rat W f g
  change 1+binaryWordWidth M≤R at hR
  have hCaps := GeneralPaperIntegerDotPrice.cap_bounds n X Y
  have hLoop := loop_bound model W X Y M R (n*stepCap model W R) hCaps.1 hCaps.2.1 hR f g (List.finRange n) 0 0
    (fun j _ => hf j) (fun j _ => hg j) (by simp only [List.length_finRange,le_refl])
    (by simpa only [Int.natAbs_zero,Nat.zero_add,List.length_finRange] using hCaps.2.2)
    (by simp only [List.length_finRange,Nat.zero_add,le_refl])
  rw [List.length_finRange] at hLoop
  have hIterator := GeneralPaperFinRangeStorage.bounded W n copied
  have hValue : integerBits result.value≤R := (Nat.add_le_add_left (binaryWordWidth_mono
    ((by rw [GeneralPaperIntegerDotPrice.data]; exact GeneralPaperIntegerDotSize.run_bound f g X Y hf hg : result.value.natAbs≤n*X*Y).trans hCaps.2.2)) 1).trans hR
  have hInnerRaw := GeneralPaperIntegerDotPrice.loop_work model.rat model.monotone W X Y M hCaps.1 hCaps.2.1 f g (List.finRange n)
    (fun j _ => hf j) (fun j _ => hg j) 0 0 (by simpa only [Int.natAbs_zero,Nat.zero_add,List.length_finRange] using hCaps.2.2)
  simp only [List.length_finRange,Nat.zero_add] at hInnerRaw
  change inner.work≤n*(48*W+4*model.rat (1+binaryWordWidth M))+2*W at hInnerRaw
  have hPay := Nat.mul_le_mul_left n (Nat.add_le_add_left (Nat.mul_le_mul_left 4 (model.monotone hR)) (48*W))
  have hInner : inner.work≤n*stepCap model W R+2*W := by unfold stepCap; omega
  have hShape : result.work=inner.work+16*(n+1)*W := rfl
  have hf' := fields_bound W (natBits (callerCap model W n R))
    [n,inner.work,result.work,inner.work+16*(n+1)*W,16*(n+1)*W] (by
      intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl
      all_goals unfold callerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (callerCap model W n R)+W)+32*W at hf'
  unfold window profile
  dsimp only
  dsimp only [inner,result] at hValue hf'
  omega

end Blotto.GeneralPaperIntegerDotStorage
