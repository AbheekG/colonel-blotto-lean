import Blotto.GeneralPaperIntervalBatch

/-! Every partial batch inherits the final code-level cap. Retained node,
visit and source-operation profiles are linear in the instruction count.
-/
namespace Blotto.GeneralPaperIntervalBatchBounds
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperPreparedPowers
open GeneralPaperIntervalBatch
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem effect_take_le (entries : List Instruction) (n i : ℕ) : effect (entries.take n) i≤effect entries i := by
  have he := effect_append (entries.take n) (entries.drop n) i
  rw [List.take_append_drop] at he
  omega

theorem prefix_valid (lambda k height : ℕ) (span : ℚ) (node : Node height) (entries : List Instruction)
    (hSpan : span=(2:ℚ)^height) (hValid : Valid lambda k node)
    (hFinal : ∀ i<2^height, levelAt node i+effect entries i≤GeneralPaperPowerPrecision.levelBound lambda k) (n : ℕ) :
    Valid lambda k (run (prepare lambda k) height span node (entries.take n)).node := by
  apply run_valid lambda k height span node (entries.take n) hSpan hValid
  intro i hi
  have he := effect_take_le entries n i
  have hc := hFinal i hi
  omega

theorem node_bound (prepared : Prepared) (height : ℕ) (span : ℚ) (node : Node height) (entries : List Instruction)
    (hSpan : 0<span) : nodes (run prepared height span node entries).node≤nodes node+4*height*entries.length := by
  induction entries generalizing node with
  | nil => simp only [run,List.length_nil,Nat.mul_zero,Nat.add_zero,le_refl]
  | cons entry rest ih =>
    have hn := GeneralPaperIntervalUpdate.nodes_linear prepared entry.lo entry.hi entry.amount height node 0 span hSpan
    have ht := ih (GeneralPaperIntervalUpdate.run prepared entry.lo entry.hi entry.amount height node 0 span).node
    dsimp only [run,List.length_cons]
    nlinarith

theorem visit_bound (prepared : Prepared) (height : ℕ) (span : ℚ) (node : Node height) (entries : List Instruction)
    (hSpan : 0<span) : (run prepared height span node entries).visits≤(1+4*height)*entries.length := by
  induction entries generalizing node with
  | nil => simp only [run,List.length_nil,Nat.mul_zero,le_refl]
  | cons entry rest ih =>
    have hn := GeneralPaperIntervalUpdate.visits_linear prepared entry.lo entry.hi entry.amount height node 0 span hSpan
    have ht := ih (GeneralPaperIntervalUpdate.run prepared entry.lo entry.hi entry.amount height node 0 span).node
    dsimp only [run,List.length_cons]
    nlinarith

def entryPrice (prepared : Prepared) (height : ℕ) : ℕ := (1+4*height)*GeneralPaperIntervalUpdateWork.nodeWork prepared+16

theorem work_bound (lambda k height : ℕ) (span : ℚ) (node : Node height) (entries : List Instruction)
    (hSpan : 0<span) : (run (prepare lambda k) height span node entries).work≤entryPrice (prepare lambda k) height*entries.length+8 := by
  induction entries generalizing node with
  | nil => simp only [run,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons entry rest ih =>
    have hn := GeneralPaperIntervalUpdateWork.run_work_linear lambda k entry.lo entry.hi entry.amount height node 0 span hSpan
    have ht := ih (GeneralPaperIntervalUpdate.run (prepare lambda k) entry.lo entry.hi entry.amount height node 0 span).node
    dsimp only [run,List.length_cons]
    dsimp only [entryPrice] at *
    nlinarith

theorem prefix_nodes (prepared : Prepared) (height : ℕ) (span : ℚ) (node : Node height) (entries : List Instruction)
    (hSpan : 0<span) (n : ℕ) : nodes (run prepared height span node (entries.take n)).node≤nodes node+4*height*entries.length := by
  have hn := node_bound prepared height span node (entries.take n) hSpan
  have hl : (entries.take n).length≤entries.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  nlinarith

end Blotto.GeneralPaperIntervalBatchBounds
