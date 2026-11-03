import Blotto.GeneralPaperSharpSourceBitContract

/-! Close the actual real-RAM DP recurrence before applying source rates.
There is one constant arithmetic resource operation at each native DP step;
the field count comes from the actual balanced tree's padded leaves. -/
namespace Blotto.GeneralPaperSharpDPArithmeticRate
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperOrderedTableArithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000

def envelope (K J depth h : ℕ) : ℕ := 2^h*(leafProfile K J depth+mergeProfile J depth+256)

theorem recurrence_identity (K J depth h : ℕ) :
    GeneralPaperOrderedDPPrice.arithmeticProfile K J depth h+mergeProfile J depth+128=envelope K J depth h := by
  induction h with
  | zero => unfold envelope GeneralPaperOrderedDPPrice.arithmeticProfile; simp only [pow_zero,one_mul]; ring
  | succ h ih =>
    rw [GeneralPaperOrderedDPPrice.arithmeticProfile]
    unfold envelope at ih ⊢
    rw [pow_succ]
    nlinarith only [ih]

theorem recurrence_bound (K J depth h : ℕ) :
    GeneralPaperOrderedDPPrice.arithmeticProfile K J depth h≤envelope K J depth h := by
  have h := recurrence_identity K J depth h
  omega

def nativeCertificate : Certificate (fun x => envelope (options x) (grid x)
    (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.depth
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height) := by
  refine ⟨_,_,_,by
    unfold envelope GeneralPaperOrderedTableArithmetic.leafProfile GeneralPaperOrderedTableArithmetic.mergeProfile options
    fun_prop⟩

theorem native_degrees : (nativeCertificate.fields,nativeCertificate.symbols,nativeCertificate.accuracy)=(1,0,2) := rfl

@[fun_prop]
theorem native_rate : Rated (fun x => GeneralPaperOrderedDPPrice.arithmeticProfile
    ((GeneralPaperSourceParameters.prepare x.k).summarySize+2)
    (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.size
    (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.depth
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height) 1 0 2 :=
  dominated nativeCertificate.bound (fun _x => recurrence_bound ..)

end Blotto.GeneralPaperSharpDPArithmeticRate
