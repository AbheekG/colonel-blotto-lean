import Blotto.GeneralPaperDPPhaseStorage

/-! Recursive DP construction retains the completed left computation
during the right descent, then streams the merge with both children live.
All phase reservations are summed only in analysis; execution never scans
subtrees or reconstructs state metadata to determine a capacity. -/
namespace Blotto.GeneralPaperDPConstructionStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperDPPhaseStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def peak {K q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) : {h : ℕ} → Tree Tag K h → ℕ
  | _,.leaf field => leafWindow bits index price W grid field
  | _,.node left right =>
    let lc := GeneralPaperOrderedProfitDP.run grid left
    let rc := GeneralPaperOrderedProfitDP.run grid right
    max (peak bits index price W grid left)
      (max (GeneralPaperEncodedDPStorage.footprint W lc+peak bits index price W grid right)
        (GeneralPaperEncodedDPStorage.footprint W lc+GeneralPaperEncodedDPStorage.footprint W rc+
          mergeWindow bits index price W grid lc.table rc.table))

theorem retained_children {K q w B h : ℕ} (W : ℕ) (grid : GeneralPaperProfitGridPrepare.Prepared q w B)
    (left right : Tree Tag K h) :
    GeneralPaperEncodedDPStorage.footprint W (GeneralPaperOrderedProfitDP.run grid left)+
      GeneralPaperEncodedDPStorage.footprint W (GeneralPaperOrderedProfitDP.run grid right)≤
      GeneralPaperEncodedDPStorage.footprint W (GeneralPaperOrderedProfitDP.run grid (.node left right)) := by
  change _≤_+_+_+_+32*W
  omega

theorem bounded {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W s : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h)
    (hl : GeneralPaperOrderedDPHeight.Leaves s tree) :
    peak bits index price W grid tree≤GeneralPaperEncodedDPStorage.footprint W (GeneralPaperOrderedProfitDP.run grid tree)+
      phaseProfile W K grid.size s h := by
  induction tree with
  | leaf field =>
    have hb := leaf_bound bits index price W s grid field hl
    change _≤_+phaseProfile W K grid.size s 0
    exact hb.trans (Nat.le_add_left _ _)
  | @node h left right ihl ihr =>
    have hleft := ihl hl.1
    have hright := ihr hl.2
    have hm := merge_bound bits index price W s h grid
      (GeneralPaperOrderedProfitDP.run grid left).table (GeneralPaperOrderedProfitDP.run grid right).table
      (GeneralPaperOrderedDPHeight.states grid left s hl.1) (GeneralPaperOrderedDPHeight.states grid right s hl.2)
    have hc := retained_children W grid left right
    have hmax : max (peak bits index price W grid left)
        (max (GeneralPaperEncodedDPStorage.footprint W (GeneralPaperOrderedProfitDP.run grid left)+peak bits index price W grid right)
          (GeneralPaperEncodedDPStorage.footprint W (GeneralPaperOrderedProfitDP.run grid left)+
            GeneralPaperEncodedDPStorage.footprint W (GeneralPaperOrderedProfitDP.run grid right)+
            mergeWindow bits index price W grid (GeneralPaperOrderedProfitDP.run grid left).table (GeneralPaperOrderedProfitDP.run grid right).table))≤
        GeneralPaperEncodedDPStorage.footprint W (GeneralPaperOrderedProfitDP.run grid (.node left right))+
          phaseProfile W K grid.size s (h+1) := by
      apply max_le
      · simp only [phaseProfile]
        nlinarith only [hleft,hc]
      · apply max_le
        · simp only [phaseProfile]
          nlinarith only [hright,hc]
        · simp only [phaseProfile]
          nlinarith only [hm,hc]
    exact hmax

def profile (W K J s h : ℕ) : ℕ := GeneralPaperEncodedDPStorage.profile W K J s h+phaseBound W K J s h

theorem native {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W s : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h)
    (hl : GeneralPaperOrderedDPHeight.Leaves s tree) : peak bits index price W grid tree≤profile W K grid.size s h :=
  (bounded bits index price W s grid tree hl).trans
    (Nat.add_le_add (GeneralPaperEncodedDPStorage.native W grid tree s hl) (phase_bound W K grid.size s h))

end Blotto.GeneralPaperDPConstructionStorage
