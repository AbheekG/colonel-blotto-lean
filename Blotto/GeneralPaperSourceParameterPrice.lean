import Blotto.GeneralPaperStreamingCFUnitWork

/-! Construct all five source dyadics once and retain their denominator
records. The trajectory period, profit accuracy denominator and power
precision denominator can subsequently reuse these exact returned records.
Casts, reciprocals, exponent arithmetic and metadata writes are priced.
-/
namespace Blotto.GeneralPaperSourceParameterPrice
open GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

structure Cache where
  zDen : GeneralPaperPowerCeiling.Result
  etaDen : GeneralPaperPowerCeiling.Result
  nuDen : GeneralPaperPowerCeiling.Result
  thetaDen : GeneralPaperPowerCeiling.Result
  summaryDen : GeneralPaperPowerCeiling.Result

def specification (k : ℕ) : Cache :=
  ⟨powerRun (11+k),powerRun (25+k),powerRun (32+k),powerRun (29+k),powerRun (34+k)⟩

def source (c : Cache) : GeneralPaperSourceParameters.Parameters :=
  ⟨1/(c.zDen.power:ℚ),1/(c.etaDen.power:ℚ),1/(c.nuDen.power:ℚ),1/(c.thetaDen.power:ℚ),
    c.thetaDen.power,c.summaryDen.power,
    c.zDen.work+c.etaDen.work+c.nuDen.work+c.thetaDen.work+c.summaryDen.work+64⟩

theorem source_data (k : ℕ) : source (specification k)=GeneralPaperSourceParameters.prepare k := rfl

def width (k : ℕ) : ℕ := 256+16*k+4*binaryWordWidth k

def indexCost (primitive : ℕ → ℕ) (k : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 11 k+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 25 k+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 32 k+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 29 k+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 34 k

theorem index_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (k e : ℕ) (he : e≤34) :
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) e k≤2*primitive (width k) := by
  have hw := binaryWordWidth_mono he
  have h34 : binaryWordWidth 34=6 := by decide
  have hs := GeneralPaperRayOperandWidthEnvelope.word_add e k
  apply GeneralPaperIntegerWordPrice.natural_binary primitive hMono <;> unfold width <;> omega

theorem indices_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (k : ℕ) :
    indexCost primitive k≤10*primitive (width k) := by
  have h1 := index_work primitive hMono k 11 (by decide)
  have h2 := index_work primitive hMono k 25 (by decide)
  have h3 := index_work primitive hMono k 32 (by decide)
  have h4 := index_work primitive hMono k 29 (by decide)
  have h5 := index_work primitive hMono k 34 (by decide)
  unfold indexCost
  omega

def inverseCost (primitive : ℕ → ℕ) (d : ℕ) : ℕ :=
  primitive (rationalWordWidth (d:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary primitive (fun a b => a/b) 1 (d:ℚ)

theorem inverse_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (d L : ℕ)
    (hL : 3≤L) (hd : 1+2*binaryWordWidth d≤L) : inverseCost primitive d≤3*primitive L := by
  have hD := GeneralPaperBasisDivideBits.nat_height d
  have hI : RationalHeight (1/(d:ℚ)) (binaryWordWidth d) := by simpa only [one_div] using hD.inv
  have wD := (rationalWordWidth_of_height hD).trans hd
  have wI := (rationalWordWidth_of_height hI).trans hd
  have w1 : rationalWordWidth (1:ℚ)≤L :=
    (by decide : rationalWordWidth (1:ℚ)≤3).trans hL
  have hc := hMono wD
  have hi := GeneralPaperRationalPrimitivePrice.binary_le primitive hMono (fun a b => a/b) 1 (d:ℚ) L w1 wD wI
  unfold inverseCost
  omega

theorem dyadic_inverse_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (k e : ℕ) (he : e≤34) :
    inverseCost primitive (powerRun (e+k)).power≤3*primitive (width k) := by
  have hw : binaryWordWidth (powerRun (e+k)).power≤1+2*(e+k) := by
    rw [(power_data (e+k)).1]
    simpa only [show binaryWordWidth 2=2 by decide,Nat.mul_comm] using GeneralPaperNatPowerOperands.power_width 2 (e+k)
  exact inverse_work primitive hMono _ _ (by unfold width; omega) (by unfold width; omega)

def run (primitive : ℕ → ℕ) (W k : ℕ) : (Cache × GeneralPaperSourceParameters.Parameters) × ℕ :=
  let zd := GeneralPaperDyadicPowerBits.run primitive W (11+k)
  let ed := GeneralPaperDyadicPowerBits.run primitive W (25+k)
  let nd := GeneralPaperDyadicPowerBits.run primitive W (32+k)
  let td := GeneralPaperDyadicPowerBits.run primitive W (29+k)
  let sd := GeneralPaperDyadicPowerBits.run primitive W (34+k)
  let c : Cache := ⟨zd.1,ed.1,nd.1,td.1,sd.1⟩
  ((c,source c),zd.2+ed.2+nd.2+td.2+sd.2+indexCost primitive k+
    inverseCost primitive zd.1.power+inverseCost primitive ed.1.power+
    inverseCost primitive nd.1.power+inverseCost primitive td.1.power+160*W)

theorem data (primitive : ℕ → ℕ) (W k : ℕ) :
    (run primitive W k).1=(specification k,GeneralPaperSourceParameters.prepare k) := by
  simp only [run,GeneralPaperDyadicPowerBits.data,specification]
  rfl

def profile (primitive : ℕ → ℕ) (W k : ℕ) : ℕ := 512*(k+35)*(W+primitive (width k))

theorem power_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k e : ℕ) (he : e≤34) :
    (GeneralPaperDyadicPowerBits.run primitive W (e+k)).2≤64*(k+35)*(W+primitive (width k)) := by
  have h := GeneralPaperDyadicPowerBits.work primitive hMono W (e+k)
  exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (by omega : e+k+1≤k+35))
    (Nat.add_le_add_left (hMono (by unfold width; omega : 8+2*(e+k)≤width k)) W))

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k : ℕ) :
    (run primitive W k).2≤profile primitive W k := by
  let F := W+primitive (width k)
  have h1 := power_work primitive hMono W k 11 (by decide)
  have h2 := power_work primitive hMono W k 25 (by decide)
  have h3 := power_work primitive hMono W k 32 (by decide)
  have h4 := power_work primitive hMono W k 29 (by decide)
  have h5 := power_work primitive hMono W k 34 (by decide)
  have hi := indices_work primitive hMono k
  have hz := dyadic_inverse_work primitive hMono k 11 (by decide)
  have he := dyadic_inverse_work primitive hMono k 25 (by decide)
  have hn := dyadic_inverse_work primitive hMono k 32 (by decide)
  have ht := dyadic_inverse_work primitive hMono k 29 (by decide)
  unfold run profile
  dsimp only
  simp only [GeneralPaperDyadicPowerBits.data]
  change _≤512*(k+35)*F
  change _≤64*(k+35)*F at h1 h2 h3 h4 h5
  have hW : W≤F := Nat.le_add_right _ _
  have hP : primitive (width k)≤F := Nat.le_add_left _ _
  nlinarith only [h1,h2,h3,h4,h5,hi,hz,he,hn,ht,hW,hP,Nat.zero_le (k*F)]

theorem both_data (primitive : ℕ → ℕ) (W k : ℕ) :
    (run primitive W k).1=(run (fun _ => 1) 1 k).1 := by rw [data,data]

theorem unit_work (k : ℕ) : (run (fun _ => 1) 1 k).2≤1024*(k+35) := by
  have h := work (fun _ => 1) (by intro a b hab; rfl) 1 k
  exact h.trans (by change 512*(k+35)*2≤1024*(k+35); omega)

end Blotto.GeneralPaperSourceParameterPrice
