import Blotto.PlayerSpecificInputWidthCost

/-! Operand/result-priced natural arithmetic and linear power construction.
The exponents used for root bounds are linear in measured input length;
the only non-dyadic exponent is a certificate-list length at most seventeen. -/
namespace Blotto.PlayerSpecificNaturalExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

def binary (model : RationalCostModel) (op : ℕ → ℕ → ℕ) (a b : ℕ) : ℕ×ℕ :=
  let result := op a b
  (result,16*((1+binaryWordWidth a)+(1+binaryWordWidth b)+(1+binaryWordWidth result))+
    GeneralPaperNaturalPrimitivePrice.binary model.rat op a b)

theorem binary_value (model : RationalCostModel) (op : ℕ → ℕ → ℕ) (a b : ℕ) : (binary model op a b).1=op a b := rfl

theorem binary_cost (model : RationalCostModel) (op : ℕ → ℕ → ℕ) (a b L : ℕ)
    (ha : 1+binaryWordWidth a≤L) (hb : 1+binaryWordWidth b≤L) (hc : 1+binaryWordWidth (op a b)≤L) :
    (binary model op a b).2≤64*model.rat L := by
  have h:=GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone op a b L ha hb hc
  have hw:=model.word_le L
  change 16*((1+binaryWordWidth a)+(1+binaryWordWidth b)+(1+binaryWordWidth (op a b)))+_≤_
  omega

def power (model : RationalCostModel) (base : ℕ) : ℕ → ℕ×ℕ
  | 0 => (1,32*(2+binaryWordWidth base+binaryWordWidth 1))
  | exponent+1 =>
    let earlier := power model base exponent
    let product := binary model (fun a b => a*b) earlier.1 base
    (product.1,earlier.2+product.2+
      32*(4+binaryWordWidth base+binaryWordWidth (exponent+1)+binaryWordWidth earlier.1+binaryWordWidth product.1))

theorem power_value (model : RationalCostModel) (base exponent : ℕ) : (power model base exponent).1=base^exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp only [power,binary,ih,pow_succ]

def powerWidth (base exponent : ℕ) : ℕ := (exponent+1)*(binaryWordWidth base+1)+32

theorem power_cost (model : RationalCostModel) (base exponent : ℕ) :
    (power model base exponent).2≤256*(exponent+1)*model.rat (powerWidth base exponent) := by
  induction exponent with
  | zero =>
    have hw:=model.word_le (powerWidth base 0)
    change 32*(2+binaryWordWidth base+binaryWordWidth 1)≤_
    have h1 : binaryWordWidth 1=1 := by decide
    rw [h1]
    unfold powerWidth at *
    nlinarith
  | succ exponent ih =>
    let L:=powerWidth base (exponent+1)
    let earlier:=power model base exponent
    have hmono : powerWidth base exponent≤L := by unfold L powerWidth; nlinarith
    have hip:=ih.trans (Nat.mul_le_mul_left (256*(exponent+1)) (model.monotone hmono))
    have hprevious : binaryWordWidth earlier.1≤1+exponent*binaryWordWidth base := by
      rw [power_value]
      exact GeneralPaperNatPowerOperands.power_width base exponent
    have hcurrent : binaryWordWidth (earlier.1*base)≤1+(exponent+1)*binaryWordWidth base := by
      rw [power_value,←pow_succ]
      exact GeneralPaperNatPowerOperands.power_width base (exponent+1)
    have hbase : 1+binaryWordWidth base≤L := by unfold L powerWidth; nlinarith
    have hprior : 1+binaryWordWidth earlier.1≤L := by unfold L powerWidth; nlinarith
    have hout : 1+binaryWordWidth (earlier.1*base)≤L := by unfold L powerWidth; nlinarith
    have hexp : 1+binaryWordWidth (exponent+1)≤L := by
      have he:=PlayerSpecificRationalTrace.control_width (exponent+1)
      unfold L powerWidth
      nlinarith
    have hm:=binary_cost model (fun a b => a*b) earlier.1 base L hprior hbase hout
    have hw:=model.word_le L
    change earlier.2+(binary model (fun a b => a*b) earlier.1 base).2+
      32*(4+binaryWordWidth base+binaryWordWidth (exponent+1)+binaryWordWidth earlier.1+
        binaryWordWidth (earlier.1*base))≤_
    change earlier.2≤256*(exponent+1)*model.rat L at hip
    change _≤256*(exponent+1+1)*model.rat L
    nlinarith only [hip,hm,hw,hbase,hprior,hout,hexp]

end Blotto.PlayerSpecificNaturalExecution
