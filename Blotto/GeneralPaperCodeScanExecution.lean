import Blotto.GeneralPaperCodePickPrice

/-! One range test/decode and one optional minimum per candidate. The
native work annotation is accumulated in the scan itself; no sum pass or
extra decoder call follows. Full Result records agree with native execution.
-/
namespace Blotto.GeneralPaperCodeScanExecution
open GeneralPaperCodeAlphabet
open GeneralPaperCodeMinimumScan (Entry Result)
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def guards (price : ℕ → ℕ) (W lo hi code : ℕ) : ℕ :=
  GeneralPaperIntegerWordPrice.compare price lo code+GeneralPaperIntegerWordPrice.compare price code hi+64*W

def evaluate (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi code : ℕ) : Result × ℕ :=
  let common := guards (primitive bits model) W lo hi code
  if lo≤code ∧ code≤hi then
    let found := GeneralPaperCodeDecodeExecution.run bits model W a response code
    (⟨found.1.choice.map (fun choice => ⟨code,choice⟩),found.1.work+24⟩,
      common+found.2+GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a+b) found.1.work 24+64*W)
  else (⟨none,16⟩,common+64*W)

def additions (price : ℕ → ℕ) (tested later : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) tested later+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (tested+later) 24

def scan (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) : List ℕ → Result × ℕ
  | [] => (⟨none,8⟩,64*W)
  | code::rest =>
    let tested := evaluate bits model W a response lo hi code
    let later := scan bits model W a response lo hi rest
    let chosen := GeneralPaperCodePickPrice.run (primitive bits model) W tested.1.selected later.1.selected
    (⟨chosen.1,tested.1.work+later.1.work+24⟩,
      tested.2+later.2+chosen.2+additions (primitive bits model) tested.1.work later.1.work+64*W)

theorem evaluate_data (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi code : ℕ) :
    (evaluate bits model W a response lo hi code).1=GeneralPaperCodeMinimumScan.evaluate a response lo hi code := by
  unfold evaluate GeneralPaperCodeMinimumScan.evaluate
  split
  · dsimp only
    rw [GeneralPaperCodeDecodeExecution.data]
  · rfl

theorem scan_data (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) (codes : List ℕ) :
    (scan bits model W a response lo hi codes).1=GeneralPaperCodeMinimumScan.scan a response lo hi codes := by
  induction codes with
  | nil => rfl
  | cons code rest ih =>
    rw [scan,GeneralPaperCodeMinimumScan.scan]
    dsimp only
    rw [evaluate_data,ih,GeneralPaperCodePickPrice.data]

theorem evaluate_selected_bound (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (lo hi code : ℕ) (entry : Entry) (hSome : (evaluate bits model W a response lo hi code).1.selected=some entry) :
    entry.cost≤8*a.C := by
  rw [evaluate_data] at hSome
  have h := ((GeneralPaperCodeMinimumScan.evaluate_iff a response lo hi code entry).mp hSome).2
  exact (valid_in_alphabet a response entry.cost
    (GeneralPaperCodeDecodeSound.decode_valid a response entry.cost entry.predecessor h.2.2)).le

theorem scan_selected_bound (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (lo hi : ℕ) (codes : List ℕ) (entry : Entry) (hSome : (scan bits model W a response lo hi codes).1.selected=some entry) :
    entry.cost≤8*a.C := by
  rw [scan_data] at hSome
  have hBest := GeneralPaperCodeMinimumScan.scan_best a response lo hi codes
  rw [hSome] at hBest
  have h := GeneralPaperCodeMinimumScan.listed_possible a response lo hi codes entry hBest.1
  exact (valid_in_alphabet a response entry.cost
    (GeneralPaperCodeDecodeSound.decode_valid a response entry.cost entry.predecessor h.2.2)).le

end Blotto.GeneralPaperCodeScanExecution
