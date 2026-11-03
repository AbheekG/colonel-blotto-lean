import Blotto.GeneralPaperSourceBasisPreparationStorageReachedRates

/-! Once-per-stage original betaN/N scalar construction. Raw integers,
casts, quotient/result, primitive scratch and all native partial-work
fields are owned. Original selected-grid/auxiliary bounds supply the word. -/
namespace Blotto.GeneralPaperBasisBudgetStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W R : ℕ) : ℕ := 24*W+4*model.rat R
def metadataCap (model : RationalCostModel) (W R : ℕ) : ℕ := 1+3*price model W R+24*W
def window (model : RationalCostModel) (W N : ℕ) (betaN : ℤ) : ℕ :=
  let b := model.rat (rationalWordWidth (betaN:ℚ))
  let n := model.rat (rationalWordWidth (N:ℚ))
  let div := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (betaN:ℚ) (N:ℚ)
  let result := GeneralPaperBasisBudgetBits.run model.rat W N betaN
  listFootprint W rationalWordWidth [(betaN:ℚ),(N:ℚ),result.1]+integerBits betaN+natBits N+b+n+div+
    fields W [24*W,b,n,div,result.2,24*W+b,24*W+b+n,24*W+b+n+div]+192*W
def profile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  3*(R+2*W)+32*W+2*R+4*model.rat R+8*(natBits (metadataCap model W R)+W)+224*W

theorem bounded (model : RationalCostModel) (W N B R : ℕ) (betaN : ℤ) (hB : betaN.natAbs≤B)
    (hR : GeneralPaperBasisBudgetBits.width N B≤R) : window model W N betaN≤profile model W R := by
  let b := model.rat (rationalWordWidth (betaN:ℚ))
  let n := model.rat (rationalWordWidth (N:ℚ))
  let div := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (betaN:ℚ) (N:ℚ)
  let result := GeneralPaperBasisBudgetBits.run model.rat W N betaN
  have hb := GeneralPaperBasisStageSize.int_height betaN B hB
  have hn := GeneralPaperBasisDivideBits.nat_height N
  have hv := hb.div hn
  have hBeta : rationalWordWidth (betaN:ℚ)≤R := (rationalWordWidth_of_height hb).trans (by unfold GeneralPaperBasisBudgetBits.width at hR; omega)
  have hN : rationalWordWidth (N:ℚ)≤R := (rationalWordWidth_of_height hn).trans (by unfold GeneralPaperBasisBudgetBits.width at hR; omega)
  have hV : rationalWordWidth ((betaN:ℚ)/(N:ℚ))≤R := (rationalWordWidth_of_height hv).trans (by unfold GeneralPaperBasisBudgetBits.width at hR; omega)
  have hOperands := list_bound W R rationalWordWidth [(betaN:ℚ),(N:ℚ),result.1] (by
    intro q hq; simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    · exact hBeta
    · exact hN
    · exact hV)
  change listFootprint W rationalWordWidth _≤3*(R+2*W)+32*W at hOperands
  have hRawB : integerBits betaN≤R := by have h := binaryWordWidth_mono hB; unfold integerBits GeneralPaperBasisBudgetBits.width at *; omega
  have hRawN : natBits N≤R := by unfold natBits GeneralPaperBasisBudgetBits.width at *; omega
  have hCastB := model.monotone hBeta
  have hCastN := model.monotone hN
  have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (betaN:ℚ) (N:ℚ) R hBeta hN hV
  have hWork := (GeneralPaperBasisBudgetBits.work model.rat model.monotone W N B betaN hB).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 4 (model.monotone hR)) (24*W))
  change result.2≤price model W R at hWork
  have hShape : result.2=24*W+b+n+div := rfl
  have hf := fields_bound W (natBits (metadataCap model W R)) [24*W,b,n,div,result.2,24*W+b,24*W+b+n,24*W+b+n+div] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (metadataCap model W R)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [b,n,div,result] at hOperands hf
  omega

end Blotto.GeneralPaperBasisBudgetStorage
