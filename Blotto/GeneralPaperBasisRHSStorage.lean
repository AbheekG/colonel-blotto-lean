import Blotto.GeneralPaperBasisProductStorage

/-! Actual fresh original-grid RHS storage. Tail selection guards, integer
dot prefixes, casts/products/sum/subtraction operands/results and native
partial-work fields are owned. Indexed fill retains complete RHS buffers
and returned values with one active scalar callback reservation. -/
namespace Blotto.GeneralPaperBasisRHSStorage
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisDenseRow
open GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def operands {d : ℕ} (model : RationalCostModel) (W N : ℕ) (betaN : ℤ) (j : ℕ) (row : Dense d) (initial : Vector d) : List ℤ :=
  let dot := GeneralPaperIntegerDotPrice.run model.rat W row.coefficients.read (tailVector j initial)
  [(N:ℤ),betaN,row.constant,row.slope,(N:ℤ)*row.constant,betaN*row.slope,
    (N:ℤ)*row.constant+betaN*row.slope,dot.value,(GeneralPaperBasisRHSBits.scalar model.rat W N betaN j row initial).1]

theorem operand_caps {d : ℕ} (model : RationalCostModel) (W C N B : ℕ) (betaN : ℤ) (j : ℕ) (row : Dense d) (initial : Vector d)
    (hBeta : betaN.natAbs≤B) (hc : row.constant.natAbs≤C) (hs : row.slope.natAbs≤C)
    (hr : ∀ i,(row.coefficients.read i).natAbs≤C) (hi : ∀ i,(initial.read i).natAbs≤N) :
    ∀ z∈operands model W N betaN j row initial,z.natAbs≤GeneralPaperBasisRHSBits.coreCap d C N B := by
  have hDot : (GeneralPaperIntegerDotPrice.run model.rat W row.coefficients.read (tailVector j initial)).value.natAbs≤d*C*N := by
    rw [GeneralPaperIntegerDotPrice.data]
    exact GeneralPaperIntegerDotSize.run_bound _ _ C N hr (GeneralPaperBasisRHSBits.tail_bound j N initial hi)
  have hA : ((N:ℤ)*row.constant).natAbs≤N*C := by rw [Int.natAbs_mul,Int.natAbs_natCast]; exact Nat.mul_le_mul_left N hc
  have hB : (betaN*row.slope).natAbs≤B*C := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul hBeta hs
  have hSum := (Int.natAbs_add_le ((N:ℤ)*row.constant) (betaN*row.slope)).trans (Nat.add_le_add hA hB)
  have hResult := GeneralPaperBasisRHSBits.scalar_bound model.rat W C N B betaN j row initial hBeta hc hs hr hi
  have hMass : N*C+B*C+d*C*N=GeneralPaperBasisRHSBits.bound d C N B := by unfold GeneralPaperBasisRHSBits.bound; ring
  have hNat : (N:ℤ).natAbs=N := Int.natAbs_natCast N
  intro z hz
  simp only [operands,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold GeneralPaperBasisRHSBits.coreCap; omega

def tailFrames (W j d : ℕ) : ℕ := ∑ i : Fin d, (fields W [j,i.val,if j ≤ i.val then 1 else 0]+128*W)
def tailProfile (W d : ℕ) : ℕ := d*(3*(natBits (d+1)+W)+160*W)

theorem tail_bound (W j d : ℕ) (hj : j≤d) : tailFrames W j d≤tailProfile W d := by
  have he (i : Fin d) : fields W [j,i.val,if j ≤ i.val then 1 else 0]+128*W≤3*(natBits (d+1)+W)+160*W := by
    have hf := fields_bound W (natBits (d+1)) [j,i.val,if j ≤ i.val then 1 else 0] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl
      · omega
      · omega
      · split <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (d+1)+W)+32*W at hf
    omega
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => he i)
  simpa only [tailFrames,tailProfile,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h

def scalarPrice (model : RationalCostModel) (W d R : ℕ) : ℕ := 512*(d+1)*(W+model.rat R)
def scalarCap (model : RationalCostModel) (W d R : ℕ) : ℕ := d+1+3*scalarPrice model W d R+32*W
def scalarWindow {d : ℕ} (model : RationalCostModel) (W copied N : ℕ) (betaN : ℤ) (j : ℕ) (row : Dense d) (initial : Vector d) : ℕ :=
  let dot := GeneralPaperIntegerDotPrice.run model.rat W row.coefficients.read (tailVector j initial)
  let a := (N:ℤ)*row.constant
  let b := betaN*row.slope
  let cast := model.rat (GeneralPaperIntegerPrimitivePrice.word (N:ℤ))
  let p := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) (N:ℤ) row.constant
  let q := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) betaN row.slope
  let s := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x+y) a b
  let t := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x-y) (a+b) dot.value
  let result := GeneralPaperBasisRHSBits.scalar model.rat W N betaN j row initial
  GeneralPaperIntegerDotStorage.window model W copied row.coefficients.read (tailVector j initial)+tailFrames W j d+
    listFootprint W integerBits (operands model W N betaN j row initial)+cast+p+q+s+t+
    fields W [d,j,dot.work,result.2,cast,p,q,s,t,32*W,dot.work+32*W,dot.work+32*W+cast,
      dot.work+32*W+cast+p,dot.work+32*W+cast+p+q,dot.work+32*W+cast+p+q+s,dot.work+32*W+cast+p+q+s+t]+256*W
def scalarProfile (model : RationalCostModel) (W d R : ℕ) : ℕ :=
  GeneralPaperIntegerDotStorage.profile model W d R+tailProfile W d+9*(R+2*W)+32*W+9*model.rat R+
    16*(natBits (scalarCap model W d R)+W)+288*W

theorem scalar_bound {d : ℕ} (model : RationalCostModel) (W copied C N B R : ℕ) (betaN : ℤ) (j : ℕ) (hj : j≤d)
    (row : Dense d) (initial : Vector d) (hBeta : betaN.natAbs≤B) (hc : row.constant.natAbs≤C) (hs : row.slope.natAbs≤C)
    (hr : ∀ i,(row.coefficients.read i).natAbs≤C) (hi : ∀ i,(initial.read i).natAbs≤N)
    (hR : GeneralPaperBasisRHSBits.width d C N B≤R) : scalarWindow model W copied N betaN j row initial≤scalarProfile model W d R := by
  let M := GeneralPaperBasisRHSBits.coreCap d C N B
  let dot := GeneralPaperIntegerDotPrice.run model.rat W row.coefficients.read (tailVector j initial)
  let a := (N:ℤ)*row.constant
  let b := betaN*row.slope
  let cast := model.rat (GeneralPaperIntegerPrimitivePrice.word (N:ℤ))
  let p := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) (N:ℤ) row.constant
  let q := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) betaN row.slope
  let s := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x+y) a b
  let t := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x-y) (a+b) dot.value
  let result := GeneralPaperBasisRHSBits.scalar model.rat W N betaN j row initial
  have hCore : 1+binaryWordWidth M≤R := by unfold M; unfold GeneralPaperBasisRHSBits.width at hR; omega
  have hDotWord : 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap d C N)≤R := by unfold GeneralPaperBasisRHSBits.width at hR; omega
  have hCaps := operand_caps model W C N B betaN j row initial hBeta hc hs hr hi
  have capAt (z : ℤ) (hz : z∈operands model W N betaN j row initial) : z.natAbs≤M := hCaps z hz
  have hN := capAt (N:ℤ) (by simp only [operands,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hBeta' := capAt betaN (by simp only [operands,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hC := capAt row.constant (by simp only [operands,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hS := capAt row.slope (by simp only [operands,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hA := capAt a (by simp only [operands,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hB := capAt b (by simp only [operands,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hAB := capAt (a+b) (by simp only [operands,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hDotV := capAt dot.value (by simp only [operands,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hOut := capAt result.1 (by simp only [operands,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hOut' : (a+b-dot.value).natAbs≤M := hOut
  have hCast : cast≤model.rat R := model.monotone ((GeneralPaperIntegerPrimitivePrice.word_bound (N:ℤ) M hN).trans hCore)
  have hP := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x*y) (N:ℤ) row.constant M hN hC hA).trans (Nat.mul_le_mul_left 2 (model.monotone hCore))
  have hQ := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x*y) betaN row.slope M hBeta' hS hB).trans (Nat.mul_le_mul_left 2 (model.monotone hCore))
  have hAdd := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x+y) a b M hA hB hAB).trans (Nat.mul_le_mul_left 2 (model.monotone hCore))
  have hSub := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x-y) (a+b) dot.value M hAB hDotV hOut').trans (Nat.mul_le_mul_left 2 (model.monotone hCore))
  have hOperands := list_bound W R integerBits (operands model W N betaN j row initial)
    (fun z hz => (Nat.add_le_add_left (binaryWordWidth_mono (hCaps z hz)) 1).trans hCore)
  change listFootprint W integerBits (operands model W N betaN j row initial)≤9*(R+2*W)+32*W at hOperands
  have hDot := GeneralPaperIntegerDotStorage.bounded model W copied C N R row.coefficients.read (tailVector j initial) hr
    (GeneralPaperBasisRHSBits.tail_bound j N initial hi) hDotWord
  have hTail := tail_bound W j d hj
  have hWork := (GeneralPaperBasisRHSBits.scalar_work model.rat model.monotone W C N B betaN j row initial hBeta hc hs hr hi).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  change result.2≤scalarPrice model W d R at hWork
  have hShape : result.2=dot.work+32*W+cast+p+q+s+t := rfl
  have hf' := fields_bound W (natBits (scalarCap model W d R))
    [d,j,dot.work,result.2,cast,p,q,s,t,32*W,dot.work+32*W,dot.work+32*W+cast,
      dot.work+32*W+cast+p,dot.work+32*W+cast+p+q,dot.work+32*W+cast+p+q+s,dot.work+32*W+cast+p+q+s+t] (by
      intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold scalarCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤16*(natBits (scalarCap model W d R)+W)+32*W at hf'
  unfold scalarWindow scalarProfile
  dsimp only
  dsimp only [dot,a,b,cast,p,q,s,t,result] at hCast hP hQ hAdd hSub hf'
  omega

def callerCap (model : RationalCostModel) (W j d R : ℕ) : ℕ := j+d+1+3*GeneralPaperNativePayloadFillStorage.workCap W j (scalarPrice model W d R)+32*W
def window {j d : ℕ} (model : RationalCostModel) (W copied N : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) : ℕ :=
  let result := GeneralPaperBasisRHSBits.run model.rat W N betaN rows initial
  GeneralPaperNativePayloadFillStorage.window W integerBits (fun i => GeneralPaperBasisRHSBits.scalar model.rat W N betaN j (rows.read i) initial)
    (fun i => scalarWindow model W copied N betaN j (rows.read i) initial) (min copied j) (Nat.min_le_right _ _)+
    fields W [j,d,result.2,32*W]+128*W
def profile (model : RationalCostModel) (W j d R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W R j (scalarPrice model W d R) (scalarProfile model W d R)+
    4*(natBits (callerCap model W j d R)+W)+160*W

theorem bounded {j d : ℕ} (model : RationalCostModel) (W copied C N B R : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d)
    (hj : j≤d) (hBeta : betaN.natAbs≤B) (hc : ∀ i,(rows.read i).constant.natAbs≤C) (hs : ∀ i,(rows.read i).slope.natAbs≤C)
    (hr : ∀ i k,((rows.read i).coefficients.read k).natAbs≤C) (hi : ∀ i,(initial.read i).natAbs≤N)
    (hR : GeneralPaperBasisRHSBits.width d C N B≤R) (hW : 1≤W) (hIndex : binaryWordWidth (j+1)≤W) :
    window model W copied N betaN rows initial≤profile model W j d R := by
  let callback := fun i => GeneralPaperBasisRHSBits.scalar model.rat W N betaN j (rows.read i) initial
  have hCore : 1+binaryWordWidth (GeneralPaperBasisRHSBits.coreCap d C N B)≤R := by unfold GeneralPaperBasisRHSBits.width at hR; omega
  have hC (i) : (callback i).2≤scalarPrice model W d R :=
    (GeneralPaperBasisRHSBits.scalar_work model.rat model.monotone W C N B betaN j (rows.read i) initial hBeta (hc i) (hs i) (hr i) hi).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (scalarPrice model W d R) (scalarProfile model W d R) integerBits callback
    (fun i => scalarWindow model W copied N betaN j (rows.read i) initial) (by
      intro i
      apply (Nat.add_le_add_left (binaryWordWidth_mono _) 1).trans hCore
      exact (GeneralPaperBasisRHSBits.scalar_bound model.rat W C N B betaN j (rows.read i) initial hBeta (hc i) (hs i) (hr i) hi).trans
        (by unfold GeneralPaperBasisRHSBits.coreCap; omega)) hC
    (fun i => scalar_bound model W copied C N B R betaN j hj (rows.read i) initial hBeta (hc i) (hs i) (hr i) hi hR)
    hW hIndex (min copied j) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (scalarPrice model W d R) callback hC hW hIndex j le_rfl
  change (GeneralPaperBasisRHSBits.run model.rat W N betaN rows initial).2≤GeneralPaperNativePayloadFillStorage.workCap W j (scalarPrice model W d R) at hWork
  have hf' := fields_bound W (natBits (callerCap model W j d R)) [j,d,(GeneralPaperBasisRHSBits.run model.rat W N betaN rows initial).2,32*W] (by
    intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals unfold callerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (callerCap model W j d R)+W)+32*W at hf'
  unfold window profile
  dsimp only
  dsimp only [callback] at hFill
  omega

end Blotto.GeneralPaperBasisRHSStorage
