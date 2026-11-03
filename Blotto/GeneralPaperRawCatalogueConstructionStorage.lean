import Blotto.GeneralPaperRawCatalogueStorage

/-! Complete raw catalogue fill: input cells, all reserved old/new slots,
selected native recursion/control/annotation frames, one active lookup,
returned data/work and complete primitive scratch. -/
namespace Blotto.GeneralPaperRawCatalogueConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
open GeneralPaperRawCatalogueStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem index_word (n lambda x : ℕ) (hx : x≤n+1) : natBits x≤GeneralPaperCellCatalogueOperands.width n lambda := by
  have h := binaryWordWidth_mono hx
  unfold natBits GeneralPaperCellCatalogueOperands.width operandWidth
  omega

def controls (W n count : ℕ) : ℕ := fields W [n,count,n+1,count+1]+64*W

theorem controls_bound (W n lambda count : ℕ) (hc : count≤n) :
    controls W n count≤4*GeneralPaperCellCatalogueOperands.width n lambda+100*W := by
  have h := fields_bound W (GeneralPaperCellCatalogueOperands.width n lambda) [n,count,n+1,count+1] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|hx|hx|hx <;> rw [hx] <;> exact index_word n lambda _ (by omega))
  change _≤4*(GeneralPaperCellCatalogueOperands.width n lambda+W)+32*W at h
  unfold controls
  omega

def frame {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) : ℕ :=
  controls W n count+stepFields model W a response cells count+128*W

def coefficient (W n lambda : ℕ) : ℕ := 8*GeneralPaperCellCatalogueOperands.width n lambda+320*W

theorem frame_bound {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hc : count≤n) :
    frame model W a response cells count≤coefficient W n a.lambda := by
  have h0 := controls_bound W n a.lambda count hc
  have h1 := step_bound model W a response cells count
  unfold frame coefficient
  omega

def framePeak {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) : (count : ℕ) → count≤n → ℕ
  | 0,_ => frame model W a response cells 0
  | count+1,hc => frame model W a response cells (count+1)+framePeak model W a response cells count (by omega)

theorem frames_bound {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hc : count≤n) :
    framePeak model W a response cells count hc≤(n+1)*coefficient W n a.lambda := by
  have h (used : ℕ) (hu : used≤n) : framePeak model W a response cells used hu≤(used+1)*coefficient W n a.lambda := by
    induction used with
    | zero => simpa only [framePeak,Nat.zero_add,Nat.one_mul] using frame_bound model W a response cells 0 (by omega)
    | succ used ih =>
      have hf := frame_bound model W a response cells (used+1) hu
      have hi := ih (by omega)
      rw [framePeak]
      nlinarith only [hf,hi]
  exact (h count hc).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1))

def callbackWindow {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) : ℕ :=
  if h : count<n then GeneralPaperLeastValidStorage.cellWindow model W a response
    (cells.read ⟨count,h⟩).1 (cells.read ⟨count,h⟩).2 else 0

theorem callback_bound {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n)
    (hb : ∀ r,(cells.read r).1≤8*a.C ∧ (cells.read r).2≤8*a.C) (count : ℕ) :
    callbackWindow model W a response cells count≤GeneralPaperLeastValidStorage.cellProfile model W a := by
  unfold callbackWindow
  split
  · rename_i h
    have hbounds := hb ⟨count,h⟩
    exact GeneralPaperLeastValidStorage.cell_bound model W a response _ _ hbounds.1 hbounds.2
  · exact Nat.zero_le _

def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedPartitionStorage.pairBits W) cells+
    2*filledPrefix true (fun w => w) model W a response cells count hc+
    framePeak model W a response cells count hc+
    natBits (GeneralPaperCellCatalogueExecution.fill true (fun w => w) model W a response cells count hc).1.2+
    callbackWindow model W a response cells count+
    footprint W (GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response cells).1+
      (GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response cells).2+256*W

def profile (model : RationalCostModel) (W n : ℕ) (a : Alphabet) : ℕ :=
  let L := operandWidth a.lambda
  let P := entryCapacity W a.lambda
  let C := GeneralPaperCellCatalogueOperands.width n a.lambda
  n*(2*L+9*W)+32*W+2*(n*(P+W)+64*W)+(n+1)*coefficient W n a.lambda+C+
    GeneralPaperLeastValidStorage.cellProfile model W a+(n*(P+W)+C+96*W)+
    GeneralPaperCellCataloguePrice.profile model W n a+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n)
    (hb : ∀ r,(cells.read r).1≤8*a.C ∧ (cells.read r).2≤8*a.C) (count : ℕ) (hc : count≤n) :
    window model W a response cells count hc≤profile model W n a := by
  have hinput := GeneralPaperEncodedFixedVector.bounded W (2*operandWidth a.lambda+8*W)
    (GeneralPaperEncodedPartitionStorage.pairBits W) cells (by
      intro r
      have h := hb r
      have h0 := code_word a (cells.read r).1 h.1
      have h1 := code_word a (cells.read r).2 h.2
      unfold GeneralPaperEncodedPartitionStorage.pairBits
      omega)
  have hp := prefix_bound true (fun w => w) model W a response cells count hc
  have hf := frames_bound model W a response cells count hc
  have hm := annotation_word true (fun w => w) model W a response cells count hc
  have hcall := callback_bound model W a response cells hb count
  have hr := returned model W a response cells
  have hs := GeneralPaperCellCataloguePrice.bit_work model W a response cells hb
  unfold window profile
  dsimp only
  nlinarith only [hinput,hp,hf,hm,hcall,hr,hs]

theorem profile_mono (model : RationalCostModel) (W n N : ℕ) (a : Alphabet) (hn : n≤N) :
    profile model W n a≤profile model W N a := by
  have hword := binaryWordWidth_mono (Nat.add_le_add_right hn 1)
  have hC : GeneralPaperCellCatalogueOperands.width n a.lambda≤GeneralPaperCellCatalogueOperands.width N a.lambda := by
    unfold GeneralPaperCellCatalogueOperands.width
    omega
  have hframe : coefficient W n a.lambda≤coefficient W N a.lambda := by unfold coefficient; omega
  have h0 := Nat.mul_le_mul_right (2*operandWidth a.lambda+9*W) hn
  have h1 := Nat.mul_le_mul_right (entryCapacity W a.lambda+W) hn
  have h2 := Nat.mul_le_mul (Nat.add_le_add_right hn 1) hframe
  have hp := GeneralPaperCellCataloguePrice.profile_mono model W n N a hn
  unfold profile
  dsimp only
  omega

end Blotto.GeneralPaperRawCatalogueConstructionStorage
