import Blotto.GeneralPaperMidpointFilterBits

/-! Complete bit-priced midpoint CF query, for both the inclusive proxy
cell and strict source bucket. Construct and traverse once, then test the
retained fraction once. No supplied quotient, bounded-continuant, call-count
or phase-cost oracle is used; temporary-space joins are still separate.
-/
namespace Blotto.GeneralPaperMidpointQueryBits
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (model : RationalCostModel) (W : ℕ) (closed : Bool) (D C t lambda : ℕ) : GeneralPaperMidpointQuery.Result × ℕ :=
  let raw := GeneralPaperMidpointRawBits.run model.rat W D C t lambda
  let checked := GeneralPaperMidpointFilterBits.run model W closed C t raw.1
  (checked.1,raw.2+checked.2+24*W)

theorem closed_data (model : RationalCostModel) (W D C t lambda : ℕ) :
    (run model W true D C t lambda).1=GeneralPaperProxyRootQuery.lookup D C t lambda := by
  simp only [run,GeneralPaperMidpointRawBits.data,GeneralPaperMidpointFilterBits.run]
  exact GeneralPaperMidpointFilterBits.closed_data D C t lambda

theorem strict_data (model : RationalCostModel) (W D C t lambda : ℕ) :
    (run model W false D C t lambda).1=GeneralPaperMidpointQuery.lookup D C t lambda := by
  simp only [run,GeneralPaperMidpointRawBits.data,GeneralPaperMidpointFilterBits.run]
  exact GeneralPaperMidpointFilterBits.strict_data D C t lambda

theorem work (model : RationalCostModel) (W D C t lambda : ℕ) (closed : Bool)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (run model W closed D C t lambda).2≤2097152*(lambda+3)*
      (W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  let P := model.rat (GeneralPaperCFOperandPrice.width lambda D)
  let F := W+P
  have hr := GeneralPaperMidpointRawBits.work model.rat model.monotone W D C t lambda hD hC ht hPower
  have hv := GeneralPaperMidpointRawBits.valid model.rat W D C t lambda hC ht hPower
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  have hf := GeneralPaperMidpointFilterBits.work model W D C t lambda closed
    (GeneralPaperMidpointRawBits.run model.rat W D C t lambda).1 hv ht hp.2
  change _≤1048576*(lambda+3)*F at hr
  change _≤96*W+15*P at hf
  change (GeneralPaperMidpointRawBits.run model.rat W D C t lambda).2+
    (GeneralPaperMidpointFilterBits.run model W closed C t
      (GeneralPaperMidpointRawBits.run model.rat W D C t lambda).1).2+24*W≤2097152*(lambda+3)*F
  have hWF : W≤F := Nat.le_add_right _ _
  have hPF : P≤F := Nat.le_add_left _ _
  nlinarith only [hr,hf,hWF,hPF,Nat.zero_le (lambda*F)]

end Blotto.GeneralPaperMidpointQueryBits
