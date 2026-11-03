import Blotto.UnaryAccuracyTraversal

/-! The actual paired-cursor positive-word reader retains its parsed word and
suffix, and records reached unary/payload-copy/trim cell visits. All malformed,
truncated and zero-payload rejection paths have incoming-length-derived prices.
Numeric scalar/controller/address/physical costs remain separate. -/

namespace Blotto.BinaryPositiveWordReadWork

def read (frame : List Bool) : Option (PositiveBinaryWord × List Bool) × ℕ :=
  let raw := UnaryPayload.readReversed frame
  let work := UnaryPayload.readSteps frame
  match raw with
  | none => (none,work)
  | some pair => ((PositiveBinaryWord.parse pair.1).map (fun word => (word,pair.2)),work + 2 * pair.1.length + 1)

theorem read_state (frame : List Bool) : (read frame).1 = PositiveBinaryWord.read frame := by
  unfold read PositiveBinaryWord.read
  cases hr : UnaryPayload.readReversed frame <;> rfl

theorem read_work (frame : List Bool) : (read frame).2 = PositiveBinaryWord.unaryReadTraversalWork frame := by
  unfold read PositiveBinaryWord.unaryReadTraversalWork
  cases hr : UnaryPayload.readReversed frame <;> rfl

theorem read_bound (frame : List Bool) : (read frame).2 ≤ 2 * frame.length + 2 := by
  rw [read_work]
  exact PositiveBinaryWord.unaryReadTraversalWork_bound frame

theorem read_consumed (frame : List Bool) (parsed : PositiveBinaryWord × List Bool)
    (h : (read frame).1 = some parsed) : 2 * parsed.1.width + parsed.2.length + 1 ≤ frame.length :=
  PositiveBinaryWord.read_width_bound frame parsed.2 parsed.1 ((read_state frame).symm.trans h)

theorem read_suffix_length (frame : List Bool) (parsed : PositiveBinaryWord × List Bool)
    (h : (read frame).1 = some parsed) : parsed.2.length ≤ frame.length := by
  have hc := read_consumed frame parsed h
  omega

end Blotto.BinaryPositiveWordReadWork
