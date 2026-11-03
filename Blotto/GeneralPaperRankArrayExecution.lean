import Blotto.GeneralPaperSelectedRankPrice

/-! One loop writes cached ranks and accumulates the native work annotation.
The cached depth is shared by callbacks; no work-sum pass follows the fill.
The selected lookup reads the summary descriptor and reuses its data.
-/
namespace Blotto.GeneralPaperRankArrayExecution
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def slot (bits : Bool) (W count : ℕ) : ℕ := if bits then arrayWord W count else W

def fill {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k depth : ℕ) (values : Summary k)
    (cuts : FixedArrayTable m ℕ) : (count : ℕ) → count≤m → (Array (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) × ℕ) × ℕ
  | 0,_ => ((#[],18),PaperIndexedArrayConstruction.initialWork index (slot bits W m) m+64*W)
  | count+1,hCount =>
    let earlier := fill bits index primitive W k depth values cuts count (by omega)
    let found := GeneralPaperSelectedRankPrice.run bits primitive W k depth values (cuts.read ⟨count,by omega⟩)
    ((earlier.1.1.push found.1.position,earlier.1.2+found.1.work+50),
      earlier.2+found.2+PaperIndexedArrayConstruction.stepWork index (slot bits W m) count+32*W+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) earlier.1.2 found.1.work+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (earlier.1.2+found.1.work) 50)

theorem fill_size {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k depth : ℕ) (values : Summary k)
    (cuts : FixedArrayTable m ℕ) (count : ℕ) (hCount : count≤m) :
    (fill bits index primitive W k depth values cuts count hCount).1.1.size=count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [fill]
    dsimp only
    rw [Array.size_push,ih]

def run {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k depth : ℕ) (values : Summary k)
    (cuts : FixedArrayTable m ℕ) :
    (FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) × ℕ) × ℕ :=
  let result := fill bits index primitive W k depth values cuts m (Nat.le_refl _)
  ((⟨result.1.1,fill_size bits index primitive W k depth values cuts m (Nat.le_refl _)⟩,result.1.2),result.2+64*W)

def prepare {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k : ℕ) (values : Summary k) (cuts : FixedArrayTable m ℕ) :=
  let depth := 35+k
  let result := run bits index primitive W k depth values cuts
  (result.1,result.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 35 k+32*W)

end Blotto.GeneralPaperRankArrayExecution
