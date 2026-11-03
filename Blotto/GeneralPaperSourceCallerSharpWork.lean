import Blotto.GeneralPaperFastDriverPriorContracts

/-! Keep the two native source-time tradeoffs separate under the sharp
alphabet substitution. The reduced-field cap then gives the paper powers;
merging the two terms first would lose one accuracy/field tradeoff. -/
namespace Blotto.GeneralPaperSourceCallerSharpWork
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra GeneralPaperNativeSourceRates
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def bitRate (x : Input) : ℕ := monomial 4 0 5 x+monomial 3 0 6 x
def realRate (x : Input) : ℕ := monomial 3 0 4 x+monomial 2 0 5 x

theorem soft_trans {r s f : Input → ℕ} (hs : Soft r s) (hf : Soft s f) : Soft r f := by
  obtain ⟨A,e,hA⟩ := hs
  obtain ⟨B,d,hB⟩ := hf
  refine ⟨A*B,e+d,?_⟩
  intro x
  exact (hB x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left B (hA x))).trans_eq (by rw [pow_add];ring))

def bitFirst : Certificate (fun x => monomial 1 3 2 x) := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hAcc : Rated (fun x => 2^x.k) 0 0 1 := by simpa only [Nat.zero_add] using dyadic_accuracy 0
  refine ⟨_,_,_,by unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy;source_space⟩
def bitSecond : Certificate (fun x => monomial 1 2 4 x) := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hAcc : Rated (fun x => 2^x.k) 0 0 1 := by simpa only [Nat.zero_add] using dyadic_accuracy 0
  refine ⟨_,_,_,by unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy;source_space⟩
def realFirst : Certificate (fun x => monomial 1 2 2 x) := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hAcc : Rated (fun x => 2^x.k) 0 0 1 := by simpa only [Nat.zero_add] using dyadic_accuracy 0
  refine ⟨_,_,_,by unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy;source_space⟩
def realSecond : Certificate (fun x => monomial 1 1 4 x) := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hAcc : Rated (fun x => 2^x.k) 0 0 1 := by simpa only [Nat.zero_add] using dyadic_accuracy 0
  refine ⟨_,_,_,by unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy;source_space⟩

theorem degrees :
    (bitFirst.fields,bitFirst.symbols,bitFirst.accuracy)=(4,0,5) ∧
      (bitSecond.fields,bitSecond.symbols,bitSecond.accuracy)=(3,0,6) ∧
      (realFirst.fields,realFirst.symbols,realFirst.accuracy)=(3,0,4) ∧
      (realSecond.fields,realSecond.symbols,realSecond.accuracy)=(2,0,5) := ⟨rfl,rfl,rfl,rfl⟩

theorem bit_source_rate : Soft bitRate GeneralPaperSharpSourceBitRate.sourceRate :=
  add_same (rate_mono bitFirst.bound (fun x => by
    change monomial 4 0 5 x≤monomial 4 0 5 x+monomial 3 0 6 x;omega))
    (rate_mono bitSecond.bound (fun x => by
      change monomial 3 0 6 x≤monomial 4 0 5 x+monomial 3 0 6 x;omega))

theorem real_source_rate : Soft realRate GeneralPaperSharpSourceRealRate.sourceRate :=
  add_same (rate_mono realFirst.bound (fun x => by
    change monomial 3 0 4 x≤monomial 3 0 4 x+monomial 2 0 5 x;omega))
    (rate_mono realSecond.bound (fun x => by
      change monomial 2 0 5 x≤monomial 3 0 4 x+monomial 2 0 5 x;omega))

theorem source_work_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft bitRate
    (fun x => GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d (W x) x.m x.k x.Qv) :=
  soft_trans bit_source_rate (GeneralPaperSourceRowsSharpContract.bit_profile_soft C d W hW)

theorem arithmetic_source_rate : Soft realRate (fun x =>
    GeneralPaperSourceRowsDriver.arithmeticProfile x.m x.k x.Qv (alphabet x)) :=
  soft_trans real_source_rate GeneralPaperSourceRowsSharpContract.arithmetic_profile_soft

theorem arithmetic_core_bound : ∃ A e : ℕ,∀ x,
    GeneralPaperSourceRowsDriver.arithmeticProfile x.m x.k x.Qv (alphabet x)≤
      A*realRate x*(GeneralPaperSourceCoreLogBound.coreLog x)^e :=
  GeneralPaperSourceCoreLogBound.remove_unused_height arithmetic_source_rate (fun _ => rfl) (fun _ => rfl)

theorem field_shift (x : Input) (C a c : ℕ) (h : fields x≤C*accuracy x) :
    monomial (a+1) 0 c x≤C*monomial a 0 (c+1) x := by
  calc
    monomial (a+1) 0 c x=fields x*((fields x)^a*(accuracy x)^c) := by unfold monomial;ring
    _≤(C*accuracy x)*((fields x)^a*(accuracy x)^c) := Nat.mul_le_mul_right _ h
    _=C*monomial a 0 (c+1) x := by unfold monomial;ring

theorem reduced_field_bound (x : Input) (C : ℕ) (h : x.m≤C*accuracy x) :
    fields x≤(C+1)*accuracy x := by
  have ha := accuracy_positive x
  unfold fields
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem bit_collapse (x : Input) (C : ℕ) (h : x.m≤C*accuracy x) : bitRate x≤(C+2)*monomial 3 0 6 x := by
  have hs := field_shift x (C+1) 3 5 (reduced_field_bound x C h)
  unfold bitRate
  calc
    monomial 4 0 5 x+monomial 3 0 6 x≤(C+1)*monomial 3 0 6 x+monomial 3 0 6 x := Nat.add_le_add_right hs _
    _=(C+2)*monomial 3 0 6 x := by ring

theorem real_collapse (x : Input) (C : ℕ) (h : x.m≤C*accuracy x) : realRate x≤(C+2)*monomial 2 0 5 x := by
  have hs := field_shift x (C+1) 2 4 (reduced_field_bound x C h)
  unfold realRate
  calc
    monomial 3 0 4 x+monomial 2 0 5 x≤(C+1)*monomial 2 0 5 x+monomial 2 0 5 x := Nat.add_le_add_right hs _
    _=(C+2)*monomial 2 0 5 x := by ring

theorem bit_reduced_bound (C d cap : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ∃ A e : ℕ,∀ x,x.m≤cap*accuracy x →
      GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d (W x) x.m x.k x.Qv≤
        A*monomial 3 0 6 x*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := source_work_rate C d W hW
  refine ⟨A*(cap+2),e,?_⟩
  intro x hx
  exact (h x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (bit_collapse x cap hx))).trans_eq (by ring))

theorem real_reduced_bound (cap : ℕ) : ∃ A e : ℕ,∀ x,x.m≤cap*accuracy x →
    GeneralPaperSourceRowsDriver.arithmeticProfile x.m x.k x.Qv (alphabet x)≤
      A*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e := by
  obtain ⟨A,e,h⟩ := arithmetic_core_bound
  refine ⟨A*(cap+2),e,?_⟩
  intro x hx
  exact (h x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (real_collapse x cap hx))).trans_eq (by ring))

end Blotto.GeneralPaperSourceCallerSharpWork
