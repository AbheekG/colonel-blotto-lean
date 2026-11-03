import Blotto.GeneralPaperEqualBitOutput

/-! Complete deterministic work after a segment is selected: fresh midpoint
production, cached group interpolation/scaling and all coordinate writes. -/
namespace Blotto.GeneralPaperEqualBitPostprocessing
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 900000

def base (s b c K : ℕ) : ℕ := b + c + s + K + 3
def height (s b c K : ℕ) : ℕ := expressionHeightBudget (base s b c K) 5
def word (s b c K : ℕ) : ℕ := 1 + 2 * height s b c K
def index (n m K : ℕ) : ℕ := GeneralPaperEqualBitMidpoint.indexWord K + binaryWordWidth (n + m + 2) + 1

theorem midpoint_height (s b c K : ℕ) : GeneralPaperCachedMidpointAssembly.height K ≤ height s b c K := by
  unfold GeneralPaperCachedMidpointAssembly.height height base expressionHeightBudget
  omega

theorem group_height (s b c K : ℕ) : GeneralPaperEqualBitGroups.height s b K ≤ height s b c K := by
  have hm : max b (max s (K + 2)) ≤ base s b c K := max_le (by unfold base; omega)
    (max_le (by unfold base; omega) (by unfold base; omega))
  unfold GeneralPaperEqualBitGroups.height GeneralPaperEqualBitGroups.base height expressionHeightBudget
  omega

theorem budget_mono {a b : ℕ} (d : ℕ) (h : a ≤ b) : expressionHeightBudget a d ≤ expressionHeightBudget b d :=
  Nat.sub_le_sub_right (Nat.mul_le_mul_right (2 ^ d) (Nat.add_le_add_right h 1)) 1

theorem output_height (s b c K : ℕ) :
    expressionHeightBudget (max c (GeneralPaperEqualCachedEmission.scaledHeight s K b)) 1 ≤ height s b c K := by
  let B := base s b c K
  have hM : max s (K + 2) ≤ B := max_le (by dsimp [B, base]; omega) (by dsimp [B, base]; omega)
  have hG : GeneralPaperEqualCachedEmission.groupHeight s K ≤ expressionHeightBudget B 3 := budget_mono 3 hM
  have hB : b ≤ expressionHeightBudget B 3 :=
    (by dsimp [B, base]; omega : b ≤ B) |>.trans (expressionHeightBudget_ge_input B 3)
  have hM' := max_le hB hG
  have hScaled := budget_mono 1 hM'
  rw [expressionHeightBudget_comp] at hScaled
  change GeneralPaperEqualCachedEmission.scaledHeight s K b ≤ expressionHeightBudget B 4 at hScaled
  have hC : c ≤ expressionHeightBudget B 4 :=
    (by dsimp [B, base]; omega : c ≤ B) |>.trans (expressionHeightBudget_ge_input B 4)
  have hLast := max_le hC hScaled
  have ho := budget_mono 1 hLast
  rw [expressionHeightBudget_comp] at ho
  exact ho

def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) : (RationalResourceArray n × ℕ) × ℕ :=
  let scalar := GeneralPaperEqualBitMidpoint.run p model A fresh
  let groups := GeneralPaperEqualBitGroups.run p model A slot scalar.1.1
  let emitted := GeneralPaperEqualBitOutput.run p model A groups.1
  ((emitted.1, scalar.1.2), scalar.2 + groups.2 + emitted.2 + 32 * A + 32)

theorem data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    (run p model A slot fresh).1.1 = (GeneralPaperEqualCachedEmission.emit p model (fun w => w) A slot fresh).1 := by
  unfold run
  dsimp only
  rw [GeneralPaperEqualBitMidpoint.data, GeneralPaperEqualBitGroups.data, GeneralPaperEqualBitOutput.data,
    GeneralPaperEqualCachedEmission.emit_data]

theorem reads {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    (run p model A slot fresh).1.2 = p.midpointBits := GeneralPaperEqualBitMidpoint.reads p model A fresh

def bound (model : RationalCostModel) (A n m K s b c : ℕ) : ℕ :=
  (24 + 25 * m + 5 * n) * model.rat (word s b c K) +
    1024 * (n + m + K + 3) * (A + index n m K + 1)

theorem metadata_bound (A n m K : ℕ) :
    256 * (K + 1) * (A + GeneralPaperEqualBitMidpoint.indexWord K + 1) +
    128 * (m + 1) * (A + 1) + 64 * (n + 1) * (A + 1) +
    PaperIndexedArrayConstruction.overhead (fun w => w) A m m +
    PaperIndexedArrayConstruction.overhead (fun w => w) A n n + 32 * A + 32 ≤
      1024 * (n + m + K + 3) * (A + index n m K + 1) := by
  let D := n + m + K + 3
  let F := A + index n m K + 1
  have hf : A + 1 ≤ F := by dsimp [F]; omega
  have hmI : binaryWordWidth (m + 1) ≤ index n m K :=
    (binaryWordWidth_mono (by omega : m + 1 ≤ n + m + 2)).trans (by unfold index; omega)
  have hnI : binaryWordWidth (n + 1) ≤ index n m K :=
    (binaryWordWidth_mono (by omega : n + 1 ≤ n + m + 2)).trans (by unfold index; omega)
  have hM := PaperIndexedArrayConstruction.overhead_bound (fun w => w) 1 (fun _ => by omega) A m m le_rfl
  have hN := PaperIndexedArrayConstruction.overhead_bound (fun w => w) 1 (fun _ => by omega) A n n le_rfl
  have hM' := hM.trans (Nat.mul_le_mul (by dsimp [D]; omega : m + 1 ≤ D)
    (by dsimp [F]; omega : 6 * A + 10 * 1 * binaryWordWidth (m + 1) + 28 ≤ 32 * F))
  have hN' := hN.trans (Nat.mul_le_mul (by dsimp [D]; omega : n + 1 ≤ D)
    (by dsimp [F]; omega : 6 * A + 10 * 1 * binaryWordWidth (n + 1) + 28 ≤ 32 * F))
  have h1 := Nat.mul_le_mul_left 256 (Nat.mul_le_mul (by dsimp [D]; omega : K + 1 ≤ D)
    (by dsimp [F, index]; omega : A + GeneralPaperEqualBitMidpoint.indexWord K + 1 ≤ F))
  have h2 := Nat.mul_le_mul_left 128 (Nat.mul_le_mul (by dsimp [D]; omega : m + 1 ≤ D) hf)
  have h3 := Nat.mul_le_mul_left 64 (Nat.mul_le_mul (by dsimp [D]; omega : n + 1 ≤ D) hf)
  have h4 := Nat.mul_le_mul_left 32 (Nat.mul_le_mul (by dsimp [D]; omega : 1 ≤ D) hf)
  change _ ≤ 1024 * D * F
  nlinarith only [hM', hN', h1, h2, h3, h4]

theorem work {n m k s b c : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight p.budget b)
    (hc : 2 ≤ c) (hC : ∀ j, RationalHeight (p.routes.table.read j).2 c) :
    (run p model A slot fresh).2 ≤ bound model A n m p.midpointBits s b c := by
  let scalar := GeneralPaperEqualBitMidpoint.run p model A fresh
  let groups := GeneralPaperEqualBitGroups.run p model A slot scalar.1.1
  have hData : groups.1 = GeneralPaperEqualCachedEmission.scaledPoint p slot fresh := by
    dsimp only [groups]
    rw [GeneralPaperEqualBitMidpoint.data, GeneralPaperEqualBitGroups.data]
  have hMid := GeneralPaperEqualBitMidpoint.work p model A fresh
  have hGroups := GeneralPaperEqualBitGroups.work p model A slot fresh hs h hB
  have hOut := GeneralPaperEqualBitOutput.work p model A groups.1 hc hC
    (fun g => by rw [hData]; exact GeneralPaperEqualCachedEmission.scaledPoint_height p hs h hB slot fresh g)
  have hMP := model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (midpoint_height s b c p.midpointBits)) 1)
  have hGP := model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (group_height s b c p.midpointBits)) 1)
  have hOP := model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (output_height s b c p.midpointBits)) 1)
  have hp1 := Nat.mul_le_mul_left 24 hMP
  have hp2 := Nat.mul_le_mul_left (25 * m) hGP
  have hp3 := Nat.mul_le_mul_left (5 * n) hOP
  have hMeta := metadata_bound A n m p.midpointBits
  change scalar.2 ≤ _ at hMid
  have hGroupWork : groups.2 ≤ 25 * m * model.rat (1 + 2 * GeneralPaperEqualBitGroups.height s b p.midpointBits) +
      128 * (m + 1) * (A + 1) + PaperIndexedArrayConstruction.overhead (fun w => w) A m m := by
    dsimp only [groups]
    rw [GeneralPaperEqualBitMidpoint.data]
    exact hGroups
  change scalar.2 + groups.2 + (GeneralPaperEqualBitOutput.run p model A groups.1).2 + 32 * A + 32 ≤ _
  unfold bound word
  nlinarith only [hMid, hGroupWork, hOut, hp1, hp2, hp3, hMeta]

end Blotto.GeneralPaperEqualBitPostprocessing
