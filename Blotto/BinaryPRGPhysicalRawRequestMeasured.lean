import Blotto.BinaryPRGPhysicalCheckedGameMeasured
import Blotto.BinaryPRGRequestRulersMeasured

/-! The complete physical raw request companion executes measured game
parsing, ordered promise/numerical physical preparation, accuracy reading
and retained-row ruler assembly once. The exact old physical/logical request
and trace are preserved. Work and retained usage have frame-only polynomial
bounds; native observer/address/reference/ownership/allocator joins remain. -/
namespace Blotto.BinaryPRGPhysicalRawRequestMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false

def read (frame : List Bool) : (Option ((Σ n,Request n) × List Bool) × Trace) × ℕ :=
  let game := BinaryPRGPhysicalCheckedGameMeasured.read frame
  match game.1.1 with
  | none => ((none,wrap 16 2 [game.1.2]),game.2+4)
  | some parsed =>
      let accuracy := BinaryAccuracyMeasured.read parsed.2
      match accuracy.1.1 with
      | none => ((none,wrap 48 2 [game.1.2,accuracy.1.2]),game.2+accuracy.2+8)
      | some selected =>
          let checked := parsed.1.2.prepared
          let assembled := BinaryPRGRequestRulersMeasured.assembleWithRows
            (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical checked)
            selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
          let physical : Request parsed.1.1 := ⟨assembled.1.1,checked.1,rfl⟩
          ((some (⟨parsed.1.1,physical⟩,selected.2),wrap 64 2 [game.1.2,accuracy.1.2,assembled.1.2]),
            game.2+accuracy.2+assembled.2+16)

theorem read_erases (frame : List Bool) :
    (read frame).1 = BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame := by
  unfold read BinaryPRGPhysicalRawRequestLifetime.readWithTrace
  dsimp only
  simp only [BinaryPRGPhysicalCheckedGameMeasured.read_erases,BinaryAccuracyMeasured.read_erases,
    BinaryPRGRequestRulersMeasured.assembleWithRows_erases]
  cases (BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).1 with
  | none => rfl
  | some parsed =>
      dsimp only
      cases (BinaryAccuracyLifetime.readWithTrace parsed.2).1 <;> rfl

def price (L : ℕ) : ℕ := BinaryPRGPhysicalCheckedGameMeasured.price L+
  BinaryAccuracyMeasured.price L+1024*(2*L+1001)+32

theorem read_work (frame : List Bool) : (read frame).2 ≤ price frame.length := by
  have hGame := BinaryPRGPhysicalCheckedGameMeasured.read_work frame
  unfold read
  dsimp only
  split
  · unfold price
    omega
  · rename_i parsed hg
    have hTail := BinaryPRGPhysicalCheckedGameMeasured.read_suffix_length frame parsed hg
    have hn := BinaryPRGPhysicalCheckedGameMeasured.read_dimension_bound frame parsed hg
    have hAccuracy := BinaryAccuracyMeasured.read_work parsed.2
    have hAccuracyTop : (BinaryAccuracyMeasured.read parsed.2).2 ≤ BinaryAccuracyMeasured.price frame.length := by
      unfold BinaryAccuracyMeasured.price at hAccuracy ⊢
      omega
    split
    · unfold price
      omega
    · rename_i selected hs
      have hWords := BinaryAccuracyMeasured.read_widths parsed.2 selected hs
      have hAssembly := BinaryPRGRequestRulersMeasured.assembleWithRows_work
        (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical parsed.1.2.prepared)
        selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
      unfold price
      omega

theorem price_polynomial (L : ℕ) : price L ≤ 6000000000*(L+1001)^5 := by
  let X := L+1001
  have hX : 0 < X := by dsimp [X]; omega
  have hGame : BinaryPRGPhysicalCheckedGameMeasured.price L ≤ 5000000000*X^5 := by
    unfold BinaryPRGPhysicalCheckedGameMeasured.price
    gcongr
    dsimp [X]
    omega
  have hLinear : L ≤ X^5 := (show L ≤ X by dsimp [X]; omega).trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 5))
  have hOne : 1 ≤ X^5 := Nat.one_le_pow 5 X (by omega)
  unfold price BinaryAccuracyMeasured.price
  change _ ≤ 6000000000*X^5
  omega

theorem read_usage (frame : List Bool) : usage (read frame).1.2 ≤ BinaryPRGPhysicalRawRequestLifetime.envelope frame.length := by
  rw [read_erases]
  exact BinaryPRGPhysicalRawRequestLifetime.readWithTrace_usage frame

theorem read_joint_polynomial (frame : List Bool) :
    (read frame).2+usage (read frame).1.2 ≤ 500006000000000*(frame.length+1001)^8 := by
  let X := frame.length+1001
  have hX : 0 < X := by dsimp [X]; omega
  have hw := (read_work frame).trans (price_polynomial frame.length)
  have hwTop := hw.trans (Nat.mul_le_mul_left 6000000000 (Nat.pow_le_pow_right hX (by decide : 5 ≤ 8)))
  have hu := (read_usage frame).trans (BinaryTerminalPhysicalRawPolynomial.raw_envelope_bound frame.length)
  have huTop := hu.trans (Nat.mul_le_mul_left 500000000000000
    (Nat.pow_le_pow_left (show frame.length+4 ≤ X by dsimp [X]; omega) 8))
  change _ ≤ 500006000000000*X^8
  omega

theorem uniform_joint : ∃ C d : ℕ, ∀ frame : List Bool,
    (read frame).2+usage (read frame).1.2 ≤ C*(frame.length+1)^d := by
  refine ⟨500006000000000*1001^8,8,?_⟩
  intro frame
  have hL : frame.length+1001 ≤ 1001*(frame.length+1) := by omega
  calc
    (read frame).2+usage (read frame).1.2 ≤ 500006000000000*(frame.length+1001)^8 := read_joint_polynomial frame
    _ ≤ 500006000000000*(1001*(frame.length+1))^8 :=
      Nat.mul_le_mul_left 500006000000000 (Nat.pow_le_pow_left hL 8)
    _ = (500006000000000*1001^8)*(frame.length+1)^8 := by rw [mul_pow]; ring

theorem read_original (frame : List Bool) :
    (read frame).1.1.map BinaryPRGPhysicalRawRequestLifetime.forgetParsed =
      (BinaryPRGAccuracyRulerRequest.read frame).1 := by
  rw [read_erases]
  exact BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame

theorem returned_resource_reads (frame : List Bool) (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (read frame).1.1 = some parsed) (rich : Bool) (index : List Bool) (j : Fin parsed.1.1)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace parsed.1.2.physical.lengthStore index).1 =
        some ((BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length.read j) ∧
      (BinaryWordObjectArrayAccess.getWithTrace
        (if rich then parsed.1.2.physical.lengthStore else parsed.1.2.physical.poorStore) index).1 =
        some ((BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource.read j) :=
  BinaryPRGPhysicalRawRequestLifetime.returned_resource_reads frame parsed
    ((congrArg Prod.fst (read_erases frame)).symm.trans hParsed) rich index j hIndex

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (read frame).1.2 steps ≤
      borrowed+frame.length+BinaryPRGPhysicalRawRequestLifetime.envelope frame.length ∧
    framePeak ((read frame).1.2.take steps) ≤ BinaryPRGPhysicalRawRequestLifetime.envelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (read_usage frame) _ steps

end Blotto.BinaryPRGPhysicalRawRequestMeasured
