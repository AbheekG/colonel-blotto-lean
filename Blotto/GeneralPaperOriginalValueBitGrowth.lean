import Blotto.GeneralPaperOriginalValueBitEnvelope

/-! Aggregate the complete native value-preparation price using the
declared rational model laws, then apply its fast logarithmic majorant.
The original rational length remains additive throughout this argument. -/
namespace Blotto.GeneralPaperOriginalValueBitGrowth
open GeneralPaperOriginalValueBitOperands GeneralPaperOriginalValueBitEnvelope
open GeneralPaperFastRationalModel
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

theorem mul_price (model : RationalCostModel) (a b : ℕ) : a*model.rat b≤model.rat (a*b) := by
  induction a with
  | zero => simp only [Nat.zero_mul];exact Nat.zero_le _
  | succ a ih =>
    simpa only [Nat.succ_mul] using
      (Nat.add_le_add_right ih (model.rat b)).trans (model.superadditive (a*b) b)

def budget (n k W S : ℕ) : ℕ :=
  8192*(n+logarithm n k W+1)*operand n k W+26*aggregate n k W S

def size (n k W S : ℕ) : ℕ := S+(n+1)*(logarithm n k W)^2

theorem envelope_price (model : RationalCostModel) (n k W S : ℕ) :
    envelope model n k W S≤model.rat (budget n k W S) := by
  have h0 := Nat.mul_le_mul_left (4096*(n+logarithm n k W+1)) (model.word_le (operand n k W))
  have h1 := mul_price model (8192*(n+logarithm n k W+1)) (operand n k W)
  have h2 := mul_price model 26 (aggregate n k W S)
  have h3 := model.superadditive (8192*(n+logarithm n k W+1)*operand n k W) (26*aggregate n k W S)
  unfold envelope budget
  nlinarith only [h0,h1,h2,h3]

theorem budget_bound (n k W S : ℕ) : budget n k W S≤2^28*size n k W S := by
  let L := logarithm n k W
  have hL : 1≤L := (basics n k W).1
  have hSquare : L≤L^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_left L hL
  have hN := Nat.mul_le_mul_left (n+1) hSquare
  have hOne : L^2≤(n+1)*L^2 := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
  dsimp only [budget,aggregate,operand,size]
  change 8192*(n+L+1)*(4096*L)+26*(8*S+16*(n+1)*(4096*L))≤2^28*(S+(n+1)*L^2)
  nlinarith only [hN,hOne,Nat.zero_le S,Nat.zero_le ((n+1)*L^2)]

theorem price_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    GeneralPaperOriginalSourceValuePrice.bitPrice model W k values≤
      model.rat (budget n k W (GeneralPaperValueRoundingInputPrice.inputSize values)) :=
  (GeneralPaperOriginalValueBitEnvelope.price_bound model W k values v hv).trans (envelope_price model n k W _)

theorem native_price {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).2≤
      model.rat (budget n k W (GeneralPaperValueRoundingInputPrice.inputSize values)) :=
  (GeneralPaperOriginalSourceValuePrice.bit_work model W k values v hv).trans (price_bound model W k values v hv)

theorem fast_price {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    GeneralPaperOriginalSourceValuePrice.bitPrice model W k values≤
      charge C d (2^28*size n k W (GeneralPaperValueRoundingInputPrice.inputSize values)) :=
  (price_bound model W k values v hv).trans ((hg _).trans (charge_monotone C d (budget_bound n k W _)))

theorem native_fast {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).2≤
      charge C d (2^28*size n k W (GeneralPaperValueRoundingInputPrice.inputSize values)) :=
  (GeneralPaperOriginalSourceValuePrice.bit_work model W k values v hv).trans (fast_price hg W k values v hv)

end Blotto.GeneralPaperOriginalValueBitGrowth
