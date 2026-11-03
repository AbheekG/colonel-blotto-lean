import Blotto.GeneralPaperStreamingMidpointRaw

/-! Complete inclusive/strict CF query using streaming adaptive division.
All native result fields and the previous amortized bit bound are retained.
The source-space bound is joined to the register implementation separately.
-/
namespace Blotto.GeneralPaperStreamingMidpointQuery
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (model : RationalCostModel) (W : ℕ) (closed : Bool) (D C t lambda : ℕ) : GeneralPaperMidpointQuery.Result × ℕ :=
  let raw := GeneralPaperStreamingMidpointRaw.run model W D C t lambda
  let checked := GeneralPaperMidpointFilterBits.run model W closed C t raw.1
  (checked.1,raw.2+checked.2+24*W)

theorem closed_data (model : RationalCostModel) (W D C t lambda : ℕ) :
    (run model W true D C t lambda).1=GeneralPaperProxyRootQuery.lookup D C t lambda := by
  simp only [run,GeneralPaperStreamingMidpointRaw.data,GeneralPaperMidpointFilterBits.run]
  exact GeneralPaperMidpointFilterBits.closed_data D C t lambda

theorem strict_data (model : RationalCostModel) (W D C t lambda : ℕ) :
    (run model W false D C t lambda).1=GeneralPaperMidpointQuery.lookup D C t lambda := by
  simp only [run,GeneralPaperStreamingMidpointRaw.data,GeneralPaperMidpointFilterBits.run]
  exact GeneralPaperMidpointFilterBits.strict_data D C t lambda

theorem work (model : RationalCostModel) (W D C t lambda : ℕ) (closed : Bool)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (run model W closed D C t lambda).2≤2097152*(lambda+3)*
      (W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  let P := model.rat (GeneralPaperCFOperandPrice.width lambda D)
  let F := W+P
  have hr := GeneralPaperStreamingMidpointRaw.work model W D C t lambda hD hC ht hPower
  have hv := GeneralPaperStreamingMidpointRaw.valid model W D C t lambda hC ht hPower
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  have hf := GeneralPaperMidpointFilterBits.work model W D C t lambda closed
    (GeneralPaperStreamingMidpointRaw.run model W D C t lambda).1 hv ht hp.2
  change _≤1048576*(lambda+3)*F at hr
  change _≤96*W+15*P at hf
  change (GeneralPaperStreamingMidpointRaw.run model W D C t lambda).2+
    (GeneralPaperMidpointFilterBits.run model W closed C t
      (GeneralPaperStreamingMidpointRaw.run model W D C t lambda).1).2+24*W≤2097152*(lambda+3)*F
  have hWF : W≤F := Nat.le_add_right _ _
  have hPF : P≤F := Nat.le_add_left _ _
  nlinarith only [hr,hf,hWF,hPF,Nat.zero_le (lambda*F)]

end Blotto.GeneralPaperStreamingMidpointQuery
