import Blotto.PlayerSpecificReconstructionForestCost

/-! Actual cached polynomial/integer source for rational reconstruction.
The longer depth, normalized denominator, grid size and source word are
computed from measured input and cached isolation fields, without oracles. -/
namespace Blotto.PlayerSpecificReconstructionCache
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificNaturalExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

structure Result where
  isolation : PlayerSpecificIntegerPreparation.Result
  inputHeight : ℕ
  denominator : ℕ
  depth : ℕ
  buckets : ℕ
  lambda : ℕ
  word : ℕ

def run (model : RationalCostModel) (p : Data) : Result×ℕ :=
  let prepared:=PlayerSpecificIntegerPreparation.run model p
  let measured:=PlayerSpecificInputWidthExecution.run model p
  let seven:=binary model (fun a b => a*b) 7 measured.1
  let denominatorExponent:=binary model (fun a b => a+b) seven.1 3
  let denominator:=power model 2 denominatorExponent.1
  let fourteen:=binary model (fun a b => a*b) 14 measured.1
  let extra:=binary model (fun a b => a+b) fourteen.1 12
  let depth:=binary model (fun a b => a+b) prepared.1.depth extra.1
  let buckets:=power model 2 depth.1
  let lambda:=binary model (fun a b => a+b) depth.1 3
  let denominatorWidth:=binary model (fun a b => a+b) denominatorExponent.1 1
  let firstSum:=binary model (fun a b => a+b) measured.1 lambda.1
  let secondSum:=binary model (fun a b => a+b) firstSum.1 denominatorWidth.1
  let padded:=binary model (fun a b => a+b) secondSum.1 1
  let word:=binary model (fun a b => a*b) 4096 padded.1
  let result : Result:=⟨prepared.1,measured.1,denominator.1,depth.1,buckets.1,lambda.1,word.1⟩
  (result,prepared.2+measured.2+seven.2+denominatorExponent.2+denominator.2+fourteen.2+extra.2+depth.2+
    buckets.2+lambda.2+denominatorWidth.2+firstSum.2+secondSum.2+padded.2+word.2+
    price model (copyRow prepared.1.polynomials.polynomial++copyRow prepared.1.polynomials.unitRight++
      PlayerSpecificSturmExecution.copyRows prepared.1.polynomials.rows)+
    64*(([prepared.1.magnitude,prepared.1.separation,prepared.1.depth,result.inputHeight,result.denominator,result.depth,
      result.buckets,result.lambda,result.word].map (fun n => 1+binaryWordWidth n)).sum))

theorem input_value (model : RationalCostModel) (p : Data) :
    (run model p).1.inputHeight=PlayerSpecificRationalMagnitude.inputHeight p := PlayerSpecificInputWidthExecution.value model p

theorem isolation_value (model : RationalCostModel) (p : Data) :
    (run model p).1.isolation=(PlayerSpecificIntegerPreparation.run model p).1 := rfl

theorem denominator_value (model : RationalCostModel) (p : Data) :
    (run model p).1.denominator=PlayerSpecificReconstructionPrecision.denominator p := by
  simp only [run,power_value,binary_value,PlayerSpecificInputWidthExecution.value,
    PlayerSpecificReconstructionPrecision.denominator_power]

theorem depth_formula (p : Data) : PlayerSpecificReconstructionPrecision.depth p=
    PlayerSpecificRootIsolation.depth p+14*PlayerSpecificRationalMagnitude.inputHeight p+12 := by
  rw [PlayerSpecificReconstructionPrecision.depth,PlayerSpecificReconstructionPrecision.denominator_width]
  ring

theorem depth_value (model : RationalCostModel) (p : Data) :
    (run model p).1.depth=PlayerSpecificReconstructionPrecision.depth p := by
  simp only [run,binary_value,PlayerSpecificInputWidthExecution.value,PlayerSpecificIntegerPreparation.depth_value,depth_formula]
  ring

theorem buckets_value (model : RationalCostModel) (p : Data) :
    (run model p).1.buckets=2^PlayerSpecificReconstructionPrecision.depth p := by
  change (power model 2 (run model p).1.depth).1=_
  rw [power_value,depth_value]

theorem lambda_value (model : RationalCostModel) (p : Data) :
    (run model p).1.lambda=PlayerSpecificReconstructionPrecision.depth p+3 := by
  change (run model p).1.depth+3=_
  rw [depth_value]

theorem word_value (model : RationalCostModel) (p : Data) :
    (run model p).1.word=4096*(PlayerSpecificRationalMagnitude.inputHeight p+
      (PlayerSpecificReconstructionPrecision.depth p+3)+binaryWordWidth (PlayerSpecificReconstructionPrecision.denominator p)+1) := by
  change 4096*((run model p).1.inputHeight+(run model p).1.lambda+(7*(run model p).1.inputHeight+3+1)+1)=_
  rw [input_value,lambda_value,PlayerSpecificReconstructionPrecision.denominator_width]

end Blotto.PlayerSpecificReconstructionCache
