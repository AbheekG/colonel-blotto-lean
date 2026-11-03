import Blotto.GeneralPaperAccuracyStrategyEquilibrium

/-! Store actual row/shift controls during preparation. Row count is read
from an existing array descriptor (one constant-time metadata load), never
obtained by traversing rows or inspecting encoding/work. A native doubling
ceiling recovers its dyadic exponent; shift power is constructed once. -/
namespace Blotto.GeneralPaperSamplingControls
open GeneralPaperStrategyDescription
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

theorem ceiling_dyadic (R : ℕ) : (GeneralPaperPowerCeiling.ceiling (2^R)).doublings=R ∧
    (GeneralPaperPowerCeiling.ceiling (2^R)).power=2^R := by
  have hu := GeneralPaperPowerCeiling.ceiling_minimal (2^R) R le_rfl
  have hl := GeneralPaperPowerCeiling.ceiling_lower (2^R)
  rw [GeneralPaperPowerCeiling.ceiling_power] at hl
  have hw := binaryWordWidth_mono hl
  simp only [binaryWordWidth,Nat.log2_two_pow] at hw
  have he : (GeneralPaperPowerCeiling.ceiling (2^R)).doublings=R := by omega
  exact ⟨he,by rw [GeneralPaperPowerCeiling.ceiling_power,he]⟩

def rowCount {n T K : ℕ} (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m)
    (description : Description o T K) : ℕ×ℕ :=
  match description with
  | .circle _ _ rows => (rows.rich.sorted.data.size,64*A)
  | .direct _ columns => ((columns.rich.read ⟨0,hm⟩).labels.data.size,64*A)

theorem row_count_data {n T K : ℕ} (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m)
    (description : Description o T K) : (rowCount A o hm description).1=T := by
  cases description with
  | circle h hR rows => exact rows.rich.sorted.size
  | direct h columns => exact (columns.rich.read ⟨0,hm⟩).labels.size

theorem row_count_work {n T K : ℕ} (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m)
    (description : Description o T K) : (rowCount A o hm description).2=64*A := by cases description <;> rfl

structure Controls (T : ℕ) where
  rows : ℕ
  rowBits : ℕ
  shifts : ℕ
  shiftBits : ℕ
  rows_eq : rows=T
  rows_power : rows=2^rowBits
  shifts_power : shifts=2^shiftBits

theorem controls_ext {T : ℕ} (a b : Controls T) (hr : a.rows=b.rows) (hb : a.rowBits=b.rowBits)
    (hs : a.shifts=b.shifts) (hl : a.shiftBits=b.shiftBits) : a=b := by
  cases a
  cases b
  cases hr
  cases hb
  cases hs
  cases hl
  rfl

def specification (T R k : ℕ) (hT : T=2^R) : Controls T :=
  ⟨T,R,GeneralPaperNativeSelectedSecurity.count k,k+6,rfl,hT,GeneralPaperNativeSelectedSecurity.count_power k⟩

def make {n T K : ℕ} (primitive : ℕ → ℕ) (A k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m)
    (description : Description o T K) (hDyadic : ∃ R,T=2^R) : Controls T×ℕ :=
  let rows := rowCount A o hm description
  let rowPrecision := GeneralPaperPowerCeilingBits.run primitive A rows.1
  let L := k+6
  let shift := GeneralPaperDyadicPowerBits.run primitive A L
  have hRows : rows.1=2^rowPrecision.1.doublings := by
    obtain ⟨R,hR⟩ := hDyadic
    dsimp only [rows,rowPrecision]
    rw [GeneralPaperPowerCeilingBits.data,row_count_data,hR,(ceiling_dyadic R).1]
  have hShift : shift.1.power=2^L := by
    dsimp only [shift]
    rw [GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data L).1]
  (⟨rows.1,rowPrecision.1.doublings,shift.1.power,L,row_count_data A o hm description,hRows,hShift⟩,
    rows.2+rowPrecision.2+shift.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) k 6+256*A)

theorem data {n T K : ℕ} (primitive : ℕ → ℕ) (A k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m)
    (description : Description o T K) (hDyadic : ∃ R,T=2^R) (R : ℕ) (hT : T=2^R) :
    (make primitive A k o hm description hDyadic).1=specification T R k hT := by
  apply controls_ext
  · exact row_count_data A o hm description
  · change (GeneralPaperPowerCeilingBits.run primitive A (rowCount A o hm description).1).1.doublings=R
    rw [GeneralPaperPowerCeilingBits.data,row_count_data,hT]
    exact (ceiling_dyadic R).1
  · change (GeneralPaperDyadicPowerBits.run primitive A (k+6)).1.power=GeneralPaperNativeSelectedSecurity.count k
    rw [GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data (k+6)).1]
    exact (GeneralPaperNativeSelectedSecurity.count_power k).symm
  · rfl

def profile (primitive : ℕ → ℕ) (A T k : ℕ) : ℕ :=
  64*(binaryWordWidth T+1)*(A+primitive (1+binaryWordWidth (2*(T+1))))+
    64*(k+7)*(A+primitive (8+2*(k+6)))+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) k 6+320*A

theorem work {n T K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (A k : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m) (description : Description o T K) (hDyadic : ∃ R,T=2^R) :
    (make primitive A k o hm description hDyadic).2≤profile primitive A T k := by
  have hr := GeneralPaperPowerCeilingBits.work primitive hMono A (rowCount A o hm description).1
  have hs := GeneralPaperDyadicPowerBits.work primitive hMono A (k+6)
  rw [row_count_data] at hr
  rw [show k+6+1=k+7 by omega] at hs
  unfold make profile
  dsimp only
  rw [row_count_work,row_count_data]
  omega

theorem arithmetic_work {n T K : ℕ} (k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m)
    (description : Description o T K) (hDyadic : ∃ R,T=2^R) :
    (make (fun _ => 1) 1 k o hm description hDyadic).2≤128*(binaryWordWidth T+k+8)+322 := by
  have h := work (fun _ => 1) (fun _ _ _ => le_rfl) 1 k o hm description hDyadic
  simp only [profile,GeneralPaperNaturalPrimitivePrice.binary,Nat.mul_one] at h
  omega

end Blotto.GeneralPaperSamplingControls
