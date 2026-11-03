import Blotto.GeneralPaperStoredNumberBits

/-! Abstract encoded sparse nodes include constructor/scalar data and child
references. Every descendant obtains its own valid/path mass certificate.
This counts retained nodes, not a native allocator or physical stack. -/
namespace Blotto.GeneralPaperSparseNodeBits
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint (W : ℕ) : {height : ℕ} → Node height → ℕ
  | _,.uniform height level => (1+binaryWordWidth height)+(1+binaryWordWidth level)+16*W
  | _,.branch level cached left right => (1+binaryWordWidth level)+GeneralPaperStoredNumberBits.bits cached+32*W+
      footprint W left+footprint W right

def perNode (W m lambda k Qv : ℕ) : ℕ := 64*W+4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv

theorem drop_ancestor (G ancestor : ℕ) {height : ℕ} (node : Node height) (hp : PathBound G ancestor node) :
    PathBound G 0 node := by
  intro i hi
  have h := hp i hi
  omega

theorem height_word (m lambda k Qv height : ℕ) (hh : height≤lambda+1) :
    1+binaryWordWidth height≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hw := binaryWordWidth_mono hh
  have hb : binaryWordWidth (lambda+1)≤GeneralPaperSourcePreparationSizes.measure m lambda k Qv := by
    unfold GeneralPaperSourcePreparationSizes.measure
    omega
  have hm := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem bounded {height : ℕ} (W m lambda k Qv : ℕ) (node : Node height) (hh : height≤lambda+1)
    (hv : Valid lambda k node) (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    footprint W node≤nodes node*perNode W m lambda k Qv := by
  induction node with
  | uniform height level =>
    have hHeight := height_word m lambda k Qv height hh
    have hLevel := (Nat.add_le_add_left (binaryWordWidth_mono hv) 1).trans (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
    dsimp only [footprint,nodes,perNode]
    omega
  | @branch height level cached left right ihl ihr =>
    have hChild := child_paths _ 0 (Node.branch level cached left right) hp
    have hl := ihl (by omega) hv.2.1 (drop_ancestor _ _ left hChild.1)
    have hr := ihr (by omega) hv.2.2.1 (drop_ancestor _ _ right hChild.2)
    have hMass := GeneralPaperStoredNumberBits.operand m lambda k Qv cached hv.2.2.2.1
      (GeneralPaperTreeMassRange.cached lambda k (Node.branch level cached left right) hh hv hp)
    have hLevel := (Nat.add_le_add_left (binaryWordWidth_mono hv.1) 1).trans (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
    change (1+binaryWordWidth level)+GeneralPaperStoredNumberBits.bits cached+32*W+footprint W left+footprint W right≤
      (1+nodes left+nodes right)*perNode W m lambda k Qv
    unfold perNode at hl hr ⊢
    nlinarith only [hl,hr,hMass,hLevel]

end Blotto.GeneralPaperSparseNodeBits
