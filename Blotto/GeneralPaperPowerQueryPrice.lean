import Blotto.GeneralPaperPowerQueryScanPrice

/-! Complete bit power evaluation: construct one, scan the retained table
once and return the entire native result. Initialization, signed cast/negation,
mantissa write and final metadata/result writes are included.
-/
namespace Blotto.GeneralPaperPowerQueryPrice
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable GeneralPaperPowerQueryBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def initialWork (primitive : ℕ → ℕ) (unit p : ℕ) : ℕ :=
  primitive (1+binaryWordWidth unit)+primitive (GeneralPaperIntegerPrimitivePrice.word (p:ℤ))+
    GeneralPaperIntegerPrimitivePrice.unary primitive (fun a => -a) (p:ℤ)

theorem initial_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (unit p columns D R : ℕ)
    (hPower : unit=2^p) : initialWork primitive unit p≤4*primitive (width p columns D R) := by
  let L := width p columns D R
  have hu := GeneralPaperParameterOperandBounds.dyadic_word p
  rw [(GeneralPaperScoreScaleParameters.power_data p).1,←hPower] at hu
  have hp := GeneralPaperInitializerControlCounters.word_le_self p
  have hU := hMono (show 1+binaryWordWidth unit≤L by dsimp [L,width]; omega)
  have hP : GeneralPaperIntegerPrimitivePrice.word (p:ℤ)≤L := by
    simp only [GeneralPaperIntegerPrimitivePrice.word,Int.natAbs_natCast]
    dsimp [L,width]
    omega
  have hN : GeneralPaperIntegerPrimitivePrice.word (-(p:ℤ))≤L := by
    simpa only [GeneralPaperIntegerPrimitivePrice.word,Int.natAbs_neg] using hP
  have hPC := hMono hP
  have hNC := hMono hN
  change _≤4*primitive L
  unfold initialWork GeneralPaperIntegerPrimitivePrice.unary
  change primitive (1+binaryWordWidth unit)+primitive (GeneralPaperIntegerPrimitivePrice.word (p:ℤ))+
    (primitive (GeneralPaperIntegerPrimitivePrice.word (p:ℤ))+primitive (GeneralPaperIntegerPrimitivePrice.word (-(p:ℤ))))≤4*primitive L
  omega

def run (primitive : ℕ → ℕ) (W unit p : ℕ) (entries : List Entry) (exponent : ℕ) :
    GeneralPaperRoundedPowerQuery.Result × ℕ :=
  let answer := GeneralPaperPowerQueryScanPrice.run primitive W unit p entries exponent (one unit p)
  (⟨answer.1.number,answer.1.remaining,answer.1.work+8⟩,
    answer.2+initialWork primitive unit p+GeneralPaperPowerTableBounds.metadataCost primitive answer.1.work 0 8+64*W)

theorem data (primitive : ℕ → ℕ) (W unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (entries : List Entry) (hEntries : ∀ e∈entries,Normal unit e.number) (exponent : ℕ) :
    (run primitive W unit p entries exponent).1=GeneralPaperRoundedPowerQuery.evaluate unit p entries exponent := by
  simp only [run,GeneralPaperRoundedPowerQuery.evaluate]
  rw [GeneralPaperPowerQueryScanPrice.data primitive W unit p hUnit hPower entries hEntries exponent _ (one_normal unit p hUnit)]

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W unit p columns D E R : ℕ)
    (hUnit : 0<unit) (hPower : unit=2^p) (entries : List Entry) (hEntries : Entries unit D E entries)
    (hLen : entries.length≤columns) (exponent : ℕ) (hExponent : exponent≤D)
    (hBudget : p+entries.length*(E+p+1)≤R) :
    (run primitive W unit p entries exponent).2≤2048*(entries.length+1)*(W+primitive (width p columns D R)) := by
  let L := width p columns D R
  let P := primitive L
  let F := W+P
  have hStart : (one unit p).exponent.natAbs+entries.length*(E+p+1)≤R := by
    simpa only [one,Int.natAbs_neg,Int.natAbs_natCast] using hBudget
  have hs := GeneralPaperPowerQueryScanPrice.work primitive hMono W unit p columns D E R hUnit hPower entries hEntries
    hLen exponent hExponent (one unit p) (one_normal unit p hUnit) hStart
  have hi := initial_work primitive hMono unit p columns D R hPower
  have hn := GeneralPaperRoundedPowerQuery.scan_work unit p entries exponent (one unit p)
  have hm := GeneralPaperPowerTableBounds.metadata_work primitive hMono
    (GeneralPaperRoundedPowerQuery.scan unit p entries exponent (one unit p)).work 0 8
    (GeneralPaperPowerTableBounds.metadataCap p columns) L
    (by unfold GeneralPaperPowerTableBounds.metadataCap; nlinarith only [hn,hLen]) (metadata_word p columns D R)
  unfold run
  dsimp only
  rw [GeneralPaperPowerQueryScanPrice.data primitive W unit p hUnit hPower entries hEntries.normal exponent _ (one_normal unit p hUnit)]
  change _≤2048*(entries.length+1)*F
  change _≤1024*(entries.length+1)*F at hs
  change _≤4*P at hi hm
  have hW : W≤F := Nat.le_add_right _ _
  have hP : P≤F := Nat.le_add_left _ _
  nlinarith only [hs,hi,hm,hW,hP,Nat.zero_le (entries.length*F)]

end Blotto.GeneralPaperPowerQueryPrice
