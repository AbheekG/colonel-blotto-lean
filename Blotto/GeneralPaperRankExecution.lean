import Blotto.GeneralPaperRankMidpointPrice

/-! One priced binary search over occurrence codes. Native guards and all
three result fields are retained. Each branch charges actual reads/tests,
index/fuel changes, native metadata and returns. No sorting or list scan is
substituted for the selected logarithmic search.
-/
namespace Blotto.GeneralPaperRankExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def control (primitive : ℕ → ℕ) (W fuel lo hi : ℕ) : ℕ :=
  GeneralPaperIntegerWordPrice.compare primitive (fuel+1) 0+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) (fuel+1) 1+
  GeneralPaperIntegerWordPrice.compare primitive lo hi+64*W

def finish (primitive : ℕ → ℕ) (W : ℕ) (child : GeneralPaperRankSearch.Result)
    (mid : GeneralPaperRankMidpointPrice.Result) : GeneralPaperRankSearch.Result × ℕ :=
  (⟨child.rank,child.work+mid.work+32,child.probes+1⟩,
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) child.work mid.work+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (child.work+mid.work) 32+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) child.probes 1+96*W)

def run {n : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (values : FixedArrayTable n ℕ) (cut depth : ℕ) :
    ℕ → ℕ → ℕ → GeneralPaperRankSearch.Result × ℕ
  | 0,lo,_ => (⟨lo,8,0⟩,64*W+GeneralPaperIntegerWordPrice.compare primitive 0 0)
  | fuel+1,lo,hi =>
    let common := control primitive W fuel lo hi
    if lo<hi then
      let mid := GeneralPaperRankMidpointPrice.run bits primitive W depth lo hi
      let checked := GeneralPaperIntegerWordPrice.compare primitive mid.1.quotient n
      if hMid : mid.1.quotient<n then
        let read := GeneralPaperIntegerWordPrice.compare primitive (values.read ⟨mid.1.quotient,hMid⟩) cut+32*W
        if values.read ⟨mid.1.quotient,hMid⟩<cut then
          let next := mid.1.quotient+1
          let child := run bits primitive W values cut depth fuel next hi
          let result := finish primitive W child.1 mid.1
          (result.1,common+mid.2+checked+read+child.2+result.2+
            GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) mid.1.quotient 1)
        else
          let child := run bits primitive W values cut depth fuel lo mid.1.quotient
          let result := finish primitive W child.1 mid.1
          (result.1,common+mid.2+checked+read+child.2+result.2)
      else (⟨lo,mid.1.work+24,0⟩,common+mid.2+checked+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) mid.1.work 24+64*W)
    else (⟨lo,8,0⟩,common)

end Blotto.GeneralPaperRankExecution
