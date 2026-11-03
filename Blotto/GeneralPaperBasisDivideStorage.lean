import Blotto.GeneralPaperSourceBasisRHSProductReachedRates

/-! Literal fresh-prefix rational division storage: original integers,
casts, unreduced N*D denominator, quotient/result and primitive scratch.
Full numerator and rational-return arrays, native fill/control/partial
fields and one active division callback coexist. No cancellation oracle. -/
namespace Blotto.GeneralPaperBasisDivideStorage
open GeneralPaperBasisStoredProducts GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile array_bound)
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def scalarPrice (model : RationalCostModel) (W R : ℕ) : ℕ := 32*W+7*model.rat R
def scalarCap (model : RationalCostModel) (W R : ℕ) : ℕ := 1+3*scalarPrice model W R+32*W
def scalarWindow (model : RationalCostModel) (W N : ℕ) (D numerator : ℤ) : ℕ :=
  let denominator := (N:ℚ)*(D:ℚ)
  let castN := model.rat (rationalWordWidth (N:ℚ))
  let castD := model.rat (rationalWordWidth (D:ℚ))
  let castU := model.rat (rationalWordWidth (numerator:ℚ))
  let mul := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) (N:ℚ) (D:ℚ)
  let div := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (numerator:ℚ) denominator
  let result := GeneralPaperBasisDivideBits.scalar model.rat W N D numerator
  listFootprint W rationalWordWidth [(N:ℚ),(D:ℚ),(numerator:ℚ),denominator,result.1]+natBits N+integerBits D+integerBits numerator+
    castN+castD+castU+mul+div+
    fields W [32*W,castN,castD,castU,mul,div,result.2,32*W+castN,32*W+castN+castD,
      32*W+castN+castD+castU,32*W+castN+castD+castU+mul,32*W+castN+castD+castU+mul+div]+256*W
def scalarProfile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  5*(R+2*W)+32*W+3*R+7*model.rat R+12*(natBits (scalarCap model W R)+W)+288*W

theorem scalar_bound (model : RationalCostModel) (W N H U R : ℕ) (D numerator : ℤ)
    (hD : D.natAbs≤H) (hU : numerator.natAbs≤U) (hR : 1+2*GeneralPaperBasisDivideBits.height N H U≤R) :
    scalarWindow model W N D numerator≤scalarProfile model W R := by
  let denominator := (N:ℚ)*(D:ℚ)
  let castN := model.rat (rationalWordWidth (N:ℚ))
  let castD := model.rat (rationalWordWidth (D:ℚ))
  let castU := model.rat (rationalWordWidth (numerator:ℚ))
  let mul := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) (N:ℚ) (D:ℚ)
  let div := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (numerator:ℚ) denominator
  let result := GeneralPaperBasisDivideBits.scalar model.rat W N D numerator
  have hh := GeneralPaperBasisDivideBits.heights N H U D numerator hD hU
  have hN := (rationalWordWidth_of_height hh.1).trans hR
  have hDw := (rationalWordWidth_of_height hh.2.1).trans hR
  have hUw := (rationalWordWidth_of_height hh.2.2.1).trans hR
  have hDen := (rationalWordWidth_of_height hh.2.2.2.1).trans hR
  have hOut := (rationalWordWidth_of_height hh.2.2.2.2).trans hR
  have hOperands := list_bound W R rationalWordWidth [(N:ℚ),(D:ℚ),(numerator:ℚ),denominator,result.1] (by
    intro q hq; simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl
    · exact hN
    · exact hDw
    · exact hUw
    · exact hDen
    · exact hOut)
  change listFootprint W rationalWordWidth _≤5*(R+2*W)+32*W at hOperands
  have hRawN : natBits N≤R := by unfold natBits GeneralPaperBasisDivideBits.height at *; omega
  have hRawD : integerBits D≤R := by have h := binaryWordWidth_mono hD; unfold integerBits GeneralPaperBasisDivideBits.height at *; omega
  have hRawU : integerBits numerator≤R := by have h := binaryWordWidth_mono hU; unfold integerBits GeneralPaperBasisDivideBits.height at *; omega
  have hCastN := model.monotone hN
  have hCastD := model.monotone hDw
  have hCastU := model.monotone hUw
  have hMul := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) (N:ℚ) (D:ℚ) R hN hDw hDen
  have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (numerator:ℚ) denominator R hUw hDen hOut
  have hWork := (GeneralPaperBasisDivideBits.scalar_work model.rat model.monotone W N H U D numerator hD hU).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 7 (model.monotone hR)) (32*W))
  change result.2≤scalarPrice model W R at hWork
  have hShape : result.2=32*W+castN+castD+castU+mul+div := rfl
  have hf := fields_bound W (natBits (scalarCap model W R))
    [32*W,castN,castD,castU,mul,div,result.2,32*W+castN,32*W+castN+castD,
      32*W+castN+castD+castU,32*W+castN+castD+castU+mul,32*W+castN+castD+castU+mul+div] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold scalarCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤12*(natBits (scalarCap model W R)+W)+32*W at hf
  unfold scalarWindow scalarProfile
  dsimp only
  dsimp only [denominator,castN,castD,castU,mul,div,result] at hOperands hDiv hf
  omega

def callerCap (model : RationalCostModel) (W j R : ℕ) : ℕ := j+1+3*GeneralPaperNativePayloadFillStorage.workCap W j (scalarPrice model W R)+32*W
def window {j : ℕ} (model : RationalCostModel) (W copied N : ℕ) (D : ℤ) (numerators : Vector j) : ℕ :=
  let result := GeneralPaperBasisDivideBits.run model.rat W N D numerators
  arrayFootprint W integerBits numerators+natBits N+integerBits D+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth (fun i => GeneralPaperBasisDivideBits.scalar model.rat W N D (numerators.read i))
      (fun i => scalarWindow model W N D (numerators.read i)) (min copied j) (Nat.min_le_right _ _)+
    fields W [j,result.2,32*W]+128*W
def profile (model : RationalCostModel) (W j R : ℕ) : ℕ := arrayProfile W j R+2*R+
  GeneralPaperNativePayloadFillStorage.profile W R j (scalarPrice model W R) (scalarProfile model W R)+
    3*(natBits (callerCap model W j R)+W)+160*W

theorem bounded {j : ℕ} (model : RationalCostModel) (W copied N H U R : ℕ) (D : ℤ) (numerators : Vector j)
    (hD : D.natAbs≤H) (hU : ∀ i,(numerators.read i).natAbs≤U) (hR : 1+2*GeneralPaperBasisDivideBits.height N H U≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (j+1)≤W) : window model W copied N D numerators≤profile model W j R := by
  have hRawN : natBits N≤R := by unfold natBits GeneralPaperBasisDivideBits.height at *; omega
  have hRawD : integerBits D≤R := by have h := binaryWordWidth_mono hD; unfold integerBits GeneralPaperBasisDivideBits.height at *; omega
  have hNumerators := array_bound W R integerBits numerators (by
    intro i; have h := binaryWordWidth_mono (hU i); unfold integerBits GeneralPaperBasisDivideBits.height at *; omega)
  let callback := fun i => GeneralPaperBasisDivideBits.scalar model.rat W N D (numerators.read i)
  have hC (i) : (callback i).2≤scalarPrice model W R :=
    (GeneralPaperBasisDivideBits.scalar_work model.rat model.monotone W N H U D (numerators.read i) hD (hU i)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 7 (model.monotone hR)) (32*W))
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (scalarPrice model W R) (scalarProfile model W R)
    rationalWordWidth callback (fun i => scalarWindow model W N D (numerators.read i))
    (fun i => (rationalWordWidth_of_height (GeneralPaperBasisDivideBits.heights N H U D (numerators.read i) hD (hU i)).2.2.2.2).trans hR)
    hC (fun i => scalar_bound model W N H U R D (numerators.read i) hD (hU i) hR) hW hIndex (min copied j) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (scalarPrice model W R) callback hC hW hIndex j le_rfl
  change (GeneralPaperBasisDivideBits.run model.rat W N D numerators).2≤GeneralPaperNativePayloadFillStorage.workCap W j (scalarPrice model W R) at hWork
  have hf := fields_bound W (natBits (callerCap model W j R)) [j,(GeneralPaperBasisDivideBits.run model.rat W N D numerators).2,32*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals unfold callerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (callerCap model W j R)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [callback] at hFill
  omega

end Blotto.GeneralPaperBasisDivideStorage
