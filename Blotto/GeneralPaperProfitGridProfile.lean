import Blotto.GeneralPaperMaterializedGridCache

/-! Simplify the explicit full-grid ledger. Only grid size and logarithmic
control factors remain. Actual source parameters discharge the bit operand
and word premises; arithmetic uses its own unit index interpretation.
-/
namespace Blotto.GeneralPaperProfitGridProfile
set_option autoImplicit false
set_option maxHeartbeats 8000000

def sizeFactor (w B : ℕ) : ℕ := (w+B+1)*(B+1)
def logFactor (w B : ℕ) : ℕ := binaryWordWidth (GeneralPaperProfitGridPrice.count w B+1)+2
def bound (w B : ℕ) : ℕ := 65536*sizeFactor w B*(logFactor w B)^2

theorem scaling (P q w B : ℕ) :
    GeneralPaperProfitGridPrice.profile (fun _ => P) P q w B=
      GeneralPaperProfitGridPrice.profile (fun _ => 1) 1 q w B*P := by
  unfold GeneralPaperProfitGridPrice.profile GeneralPaperProfitGridPrice.depthProfile
    GeneralPaperProfitOrderConstruction.profile GeneralPaperProfitPointPrice.profile
    GeneralPaperProfitPointPrice.bandProfile GeneralPaperNaturalOrderPrice.profile GeneralPaperPricedSort.profile
  dsimp only
  ring

theorem dominate (primitive : ℕ → ℕ) (W q w B P : ℕ) (hW : W≤P)
    (hPoint : primitive (GeneralPaperProfitPointPrice.width w B)≤P)
    (hScale : primitive (GeneralPaperProfitScalePrice.width q w B)≤P)
    (hOrder : primitive (1+binaryWordWidth (2*GeneralPaperProfitGridPoints.denominator w B))≤P)
    (hDepth : primitive (1+binaryWordWidth (2*(GeneralPaperProfitGridPrice.count w B+2)))≤P)
    (hMeta : primitive (2*GeneralPaperProfitOrderPrice.word w B)≤P) :
    GeneralPaperProfitGridPrice.profile primitive W q w B≤GeneralPaperProfitGridPrice.profile (fun _ => P) P q w B := by
  unfold GeneralPaperProfitGridPrice.profile GeneralPaperProfitGridPrice.depthProfile
    GeneralPaperProfitOrderConstruction.profile GeneralPaperProfitPointPrice.profile
    GeneralPaperProfitPointPrice.bandProfile GeneralPaperNaturalOrderPrice.profile GeneralPaperPricedSort.profile
  dsimp only
  gcongr

theorem arithmetic_profile (q w B : ℕ) : GeneralPaperProfitGridPrice.profile (fun _ => 1) 1 q w B≤bound w B := by
  let A := sizeFactor w B
  let N := GeneralPaperProfitGridPrice.count w B
  let s := binaryWordWidth (N+1)
  let J := s+2
  have hA : 1≤A := by dsimp [A,sizeFactor]; nlinarith only [Nat.zero_le (w*B),Nat.zero_le (B*B)]
  have hY : B+1≤A := by dsimp [A,sizeFactor]; nlinarith only [Nat.zero_le (w*B),Nat.zero_le (B*B)]
  have hN : N+1≤4*A := by dsimp [N,GeneralPaperProfitGridPrice.count,A,sizeFactor]; nlinarith only [Nat.zero_le (w*B),Nat.zero_le (B*B)]
  have hJ : 2≤J := by dsimp [J]; omega
  have hPoint : GeneralPaperProfitPointPrice.profile (fun _ => 1) 1 w B≤256*A := by
    unfold GeneralPaperProfitPointPrice.profile GeneralPaperProfitPointPrice.bandProfile
    dsimp only [A,sizeFactor]
    nlinarith only [Nat.zero_le (w*B),Nat.zero_le (B*B)]
  have hOrder : GeneralPaperNaturalOrderPrice.profile ((B+1)*w) 1 1≤1024*(N+1)*J^2 := by
    unfold GeneralPaperNaturalOrderPrice.profile GeneralPaperPricedSort.profile
    change N*(s+2)*(1+(152+24*s)*1)+(12*s+8*N+20)*1+(3*1+48*1)*N+20*1≤1024*(N+1)*J^2
    dsimp only [J]
    nlinarith only [Nat.zero_le (N*s*s),Nat.zero_le (N*s),Nat.zero_le (s*s)]
  have hOrderBound := Nat.mul_le_mul_right (J^2) (Nat.mul_le_mul_left 1024 hN)
  have hAJ : A≤A*J^2 := by
    simpa only [mul_one] using Nat.mul_le_mul_left A (show 1≤J^2 by nlinarith only [hJ])
  have hJJ : J≤A*J^2 := by
    have hSquare : J≤J^2 := by nlinarith only [hJ]
    have hm := Nat.mul_le_mul_right (J^2) hA
    nlinarith only [hm,hSquare]
  change _≤65536*A*J^2
  unfold GeneralPaperProfitGridPrice.profile GeneralPaperProfitGridPrice.depthProfile
    GeneralPaperProfitOrderConstruction.profile
  change 64*(B+1)*(1+1)+GeneralPaperProfitPointPrice.profile (fun _ => 1) 1 w B+
    GeneralPaperNaturalOrderPrice.profile ((B+1)*w) 1 1+4*1+64*1+
    252*(N+1)*1+N*(2*1)+64*(s+1)*(1+1)+6*1≤65536*A*J^2
  have hJDef : J=s+2 := rfl
  nlinarith only [hPoint,hOrder,hOrderBound,hY,hN,hAJ,hJJ,hA,hJDef]

theorem profile_bound (primitive : ℕ → ℕ) (W q w B P : ℕ) (hW : W≤P)
    (hPoint : primitive (GeneralPaperProfitPointPrice.width w B)≤P)
    (hScale : primitive (GeneralPaperProfitScalePrice.width q w B)≤P)
    (hOrder : primitive (1+binaryWordWidth (2*GeneralPaperProfitGridPoints.denominator w B))≤P)
    (hDepth : primitive (1+binaryWordWidth (2*(GeneralPaperProfitGridPrice.count w B+2)))≤P)
    (hMeta : primitive (2*GeneralPaperProfitOrderPrice.word w B)≤P) :
    GeneralPaperProfitGridPrice.profile primitive W q w B≤bound w B*P := by
  exact (dominate primitive W q w B P hW hPoint hScale hOrder hDepth hMeta).trans
    (by rw [scaling]; exact Nat.mul_le_mul_right P (arithmetic_profile q w B))

theorem bit_profile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    GeneralPaperProfitGridPrice.profile model.rat (GeneralPaperProfitOrderPrice.word p.width p.exponent)
      p.qProf p.width p.exponent≤bound p.width p.exponent*
        model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hs := GeneralPaperProfitGridEnvelope.widths m lambda k Qv
  have hW : GeneralPaperProfitOrderPrice.word p.width p.exponent≤H := by
    have hh:=hs.2.2.1
    change 2*GeneralPaperProfitOrderPrice.word p.width p.exponent≤H at hh
    omega
  exact profile_bound model.rat _ _ _ _ _ (hW.trans (model.word_le H))
    (model.monotone hs.1) (model.monotone hs.2.1) (model.monotone hs.2.2.2.1)
    (model.monotone hs.2.2.2.2) (model.monotone hs.2.2.1)

end Blotto.GeneralPaperProfitGridProfile
