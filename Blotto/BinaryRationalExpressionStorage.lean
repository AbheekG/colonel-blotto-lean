import Blotto.BinaryRationalExpressionWork

/-! Selected-path evaluator storage counts live result words and control
frames. The first operand remains live during the second operand, and both
comparison operands remain live during the selected continuation. Environment
and literal payloads are counted separately. The model follows the actual AST
evaluator; Boolean opcode/GCD scratch and physical allocator/GC peaks are separate
contracts, not hidden constant-memory assumptions. -/

namespace Blotto
open BinaryRationalNormalization BinaryRationalEncoding
open scoped BigOperators
namespace BinaryRationalExpression

def heldResultPeak (firstPeak secondPeak firstWords secondWords outputWords : ℕ) : ℕ :=
  max firstPeak (max (firstWords + secondPeak) (firstWords + secondWords + outputWords))

def runWithStorage {k : ℕ} (env : FixedArrayTable k SignedWord) :
    BinaryRationalExpression k → (SignedWord × ℕ) × (ℕ × ℕ)
  | .input j => ((env.read j, 1), (payloadWords (env.read j), 1))
  | .literal word => ((word, 1), (payloadWords word, 1))
  | .add a b =>
      let x := a.runWithStorage env; let y := b.runWithStorage env
      let out := BinaryRationalOpcode.apply .add x.1.1 y.1.1
      ((out, x.1.2 + y.1.2 + 1),
        (heldResultPeak x.2.1 y.2.1 (payloadWords x.1.1) (payloadWords y.1.1) (payloadWords out), 1 + max x.2.2 y.2.2))
  | .sub a b =>
      let x := a.runWithStorage env; let y := b.runWithStorage env
      let out := BinaryRationalOpcode.apply .sub x.1.1 y.1.1
      ((out, x.1.2 + y.1.2 + 1),
        (heldResultPeak x.2.1 y.2.1 (payloadWords x.1.1) (payloadWords y.1.1) (payloadWords out), 1 + max x.2.2 y.2.2))
  | .mul a b =>
      let x := a.runWithStorage env; let y := b.runWithStorage env
      let out := BinaryRationalOpcode.apply .mul x.1.1 y.1.1
      ((out, x.1.2 + y.1.2 + 1),
        (heldResultPeak x.2.1 y.2.1 (payloadWords x.1.1) (payloadWords y.1.1) (payloadWords out), 1 + max x.2.2 y.2.2))
  | .div a b =>
      let x := a.runWithStorage env; let y := b.runWithStorage env
      let out := BinaryRationalOpcode.apply .div x.1.1 y.1.1
      ((out, x.1.2 + y.1.2 + 2),
        (heldResultPeak x.2.1 y.2.1 (payloadWords x.1.1) (payloadWords y.1.1) (payloadWords out), 1 + max x.2.2 y.2.2))
  | .minimum a b =>
      let x := a.runWithStorage env; let y := b.runWithStorage env
      let out := BinaryRationalOpcode.apply .minimum x.1.1 y.1.1
      ((out, x.1.2 + y.1.2 + 1),
        (heldResultPeak x.2.1 y.2.1 (payloadWords x.1.1) (payloadWords y.1.1) (payloadWords out), 1 + max x.2.2 y.2.2))
  | .maximum a b =>
      let x := a.runWithStorage env; let y := b.runWithStorage env
      let out := BinaryRationalOpcode.apply .maximum x.1.1 y.1.1
      ((out, x.1.2 + y.1.2 + 1),
        (heldResultPeak x.2.1 y.2.1 (payloadWords x.1.1) (payloadWords y.1.1) (payloadWords out), 1 + max x.2.2 y.2.2))
  | .ifLe a b yes no =>
      let x := a.runWithStorage env; let y := b.runWithStorage env
      let z := if BinaryRationalArithmetic.lessEqual x.1.1 y.1.1 then yes.runWithStorage env else no.runWithStorage env
      ((z.1.1, x.1.2 + y.1.2 + z.1.2 + 1),
        (max x.2.1 (max (payloadWords x.1.1 + y.2.1)
          (payloadWords x.1.1 + payloadWords y.1.1 + z.2.1)),
          1 + max (max x.2.2 y.2.2) z.2.2))

theorem runWithStorage_refines {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord) :
    (e.runWithStorage env).1 = e.run env := by
  induction e with
  | input _ | literal _ => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [runWithStorage, run, ha, hb]
  | ifLe a b yes no ha hb hy hn =>
      simp only [runWithStorage, run, ha, hb]
      split <;> simp only [hy, hn]

def depth {k : ℕ} : BinaryRationalExpression k → ℕ
  | .input _ | .literal _ => 0
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => max a.depth b.depth + 1
  | .ifLe a b yes no => max (max a.depth b.depth) (max yes.depth no.depth) + 1

theorem depth_interpreted {k : ℕ} (e : BinaryRationalExpression k) : e.depth = e.interpreted.depth := by
  induction e <;> simp only [depth, interpreted, RationalExpression.depth, *]

theorem controlDepth_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord) :
    (e.runWithStorage env).2.2 ≤ e.depth + 1 := by
  induction e with
  | input _ | literal _ => simp [runWithStorage, depth]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [runWithStorage, depth]
      omega
  | ifLe a b yes no ha hb hy hn =>
      simp only [runWithStorage, depth]
      split <;> omega

def ResultWordsBounded {k : ℕ} (env : FixedArrayTable k SignedWord) (P : ℕ) : BinaryRationalExpression k → Prop
  | .input j => payloadWords (env.read j) ≤ P
  | .literal word => payloadWords word ≤ P
  | .add a b => a.ResultWordsBounded env P ∧ b.ResultWordsBounded env P ∧ payloadWords ((add a b).run env).1 ≤ P
  | .sub a b => a.ResultWordsBounded env P ∧ b.ResultWordsBounded env P ∧ payloadWords ((sub a b).run env).1 ≤ P
  | .mul a b => a.ResultWordsBounded env P ∧ b.ResultWordsBounded env P ∧ payloadWords ((mul a b).run env).1 ≤ P
  | .div a b => a.ResultWordsBounded env P ∧ b.ResultWordsBounded env P ∧ payloadWords ((div a b).run env).1 ≤ P
  | .minimum a b => a.ResultWordsBounded env P ∧ b.ResultWordsBounded env P ∧ payloadWords ((minimum a b).run env).1 ≤ P
  | .maximum a b => a.ResultWordsBounded env P ∧ b.ResultWordsBounded env P ∧ payloadWords ((maximum a b).run env).1 ≤ P
  | .ifLe a b yes no => a.ResultWordsBounded env P ∧ b.ResultWordsBounded env P ∧
      yes.ResultWordsBounded env P ∧ no.ResultWordsBounded env P

theorem ResultWordsBounded.output {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord) (P : ℕ)
    (h : e.ResultWordsBounded env P) : payloadWords (e.run env).1 ≤ P := by
  induction e with
  | input _ | literal _ => exact h
  | add _ _ _ _ | sub _ _ _ _ | mul _ _ _ _ | div _ _ _ _ | minimum _ _ _ _ | maximum _ _ _ _ => exact h.2.2
  | ifLe a b yes no _ha _hb hy hn =>
      unfold run
      dsimp only
      split
      · exact hy h.2.2.1
      · exact hn h.2.2.2

theorem heldResultPeak_bound {aPeak bPeak aWords bWords outWords da db P : ℕ}
    (ha : aPeak ≤ 3 * (da + 1) * P) (hb : bPeak ≤ 3 * (db + 1) * P)
    (hA : aWords ≤ P) (hB : bWords ≤ P) (hOut : outWords ≤ P) :
    heldResultPeak aPeak bPeak aWords bWords outWords ≤ 3 * (max da db + 2) * P := by
  unfold heldResultPeak
  have hda : da ≤ max da db := Nat.le_max_left _ _
  have hdb : db ≤ max da db := Nat.le_max_right _ _
  apply max_le
  · nlinarith
  · apply max_le <;> nlinarith

theorem resultPeak_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord) (P : ℕ)
    (h : e.ResultWordsBounded env P) : (e.runWithStorage env).2.1 ≤ 3 * (e.depth + 1) * P := by
  induction e with
  | input _ | literal _ => simp only [runWithStorage, depth, ResultWordsBounded] at h ⊢; omega
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      have hA := ResultWordsBounded.output a env P h.1
      have hB := ResultWordsBounded.output b env P h.2.1
      have hOut := h.2.2
      have hPeak := heldResultPeak_bound (ha h.1) (hb h.2.1) hA hB hOut
      simpa only [runWithStorage, runWithStorage_refines, run, depth, Nat.add_assoc] using hPeak
  | ifLe a b yes no ha hb hy hn =>
      have hA := ResultWordsBounded.output a env P h.1
      have hB := ResultWordsBounded.output b env P h.2.1
      have pa := ha h.1
      have pb := hb h.2.1
      have py := hy h.2.2.1
      have pn := hn h.2.2.2
      simp only [runWithStorage, runWithStorage_refines, depth]
      split <;> apply max_le
      all_goals try (apply max_le)
      all_goals nlinarith [Nat.le_max_left a.depth b.depth, Nat.le_max_right a.depth b.depth,
        Nat.le_max_left yes.depth no.depth, Nat.le_max_right yes.depth no.depth,
        Nat.le_max_left (max a.depth b.depth) (max yes.depth no.depth),
        Nat.le_max_right (max a.depth b.depth) (max yes.depth no.depth)]

theorem interpreted_root_height {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord) (s : ℕ)
    (h : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    RationalHeight (e.interpreted.run (interpretedEnvironment env)).1 (2 * s + 1) := by
  cases e with
  | input j => exact h.mono (by omega)
  | literal word => exact h.mono (by omega)
  | add a b => simpa only [interpreted, RationalExpression.run, two_mul] using h.1.add h.2.1
  | sub a b => simpa only [interpreted, RationalExpression.run, two_mul] using h.1.sub h.2.1
  | mul a b => exact (h.1.mul h.2.1).mono (by omega)
  | div a b =>
      have hd := (h.1.div h.2.1).mono (show s + s ≤ 2 * s + 1 by omega)
      simpa only [interpreted, RationalExpression.safe_div_value] using hd
  | minimum a b => exact (h.1.min h.2.1).mono (by omega)
  | maximum a b => exact (h.1.max h.2.1).mono (by omega)
  | ifLe a b yes no =>
      have hy := interpreted_root_height yes env s h.2.2.2.2.1
      have hn := interpreted_root_height no env s h.2.2.2.2.2
      simp only [interpreted, RationalExpression.run]
      split
      · exact hy
      · exact hn
termination_by e

theorem root_payload_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    payloadWords (e.run env).1 ≤ 8 * s + 7 := by
  have hWidth := e.run_height_width env hEnv hLit (2 * s + 1) (interpreted_root_height e env s hHeight)
  have hPayload := payloadWords_bound (e.run env).1 (1 + 2 * (2 * s + 1)) hWidth
  omega

theorem resultWords_of_heights {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    e.ResultWordsBounded env (8 * s + 7) := by
  induction e with
  | input _ | literal _ => exact root_payload_bound _ env hEnv hLit s hHeight
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      exact ⟨ha hLit.1 hHeight.2.2.1, hb hLit.2 hHeight.2.2.2,
        root_payload_bound _ env hEnv hLit s hHeight⟩
  | ifLe a b yes no ha hb hy hn =>
      exact ⟨ha hLit.1 hHeight.2.2.1, hb hLit.2.1 hHeight.2.2.2.1,
        hy hLit.2.2.1 hHeight.2.2.2.2.1, hn hLit.2.2.2 hHeight.2.2.2.2.2⟩

theorem resultPeak_height_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    (e.runWithStorage env).2.1 ≤ 3 * (e.depth + 1) * (8 * s + 7) :=
  e.resultPeak_bound env _ (e.resultWords_of_heights env hEnv hLit s hHeight)

def environmentPayload {k : ℕ} (env : FixedArrayTable k SignedWord) : ℕ := ∑ j, payloadWords (env.read j)

def literalPayload {k : ℕ} : BinaryRationalExpression k → ℕ
  | .input _ => 0
  | .literal word => payloadWords word
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => a.literalPayload + b.literalPayload
  | .ifLe a b yes no => a.literalPayload + b.literalPayload + yes.literalPayload + no.literalPayload

def evaluationPayloadPeak {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord) : ℕ :=
  environmentPayload env + e.literalPayload + (e.runWithStorage env).2.1

theorem evaluationPayloadPeak_height_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    e.evaluationPayloadPeak env ≤ environmentPayload env + e.literalPayload + 3 * (e.depth + 1) * (8 * s + 7) :=
  Nat.add_le_add_left (e.resultPeak_height_bound env hEnv hLit s hHeight) _

theorem environmentPayload_bound {k : ℕ} (env : FixedArrayTable k SignedWord) (s : ℕ)
    (hCanonical : ∀ j, CanonicalWord (env.read j))
    (hHeight : ∀ j, RationalHeight (value (env.read j)) s) :
    environmentPayload env ≤ k * (4 * s + 3) := by
  unfold environmentPayload
  calc
    _ ≤ ∑ _j : Fin k, (4 * s + 3) := by
      apply Finset.sum_le_sum
      intro j _
      have hW := (hCanonical j).2.trans (rationalWordWidth_of_height (hHeight j))
      have hP := payloadWords_bound (env.read j) (1 + 2 * s) hW
      omega
    _ = _ := by simp

def literalCount {k : ℕ} : BinaryRationalExpression k → ℕ
  | .input _ => 0
  | .literal _ => 1
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => a.literalCount + b.literalCount
  | .ifLe a b yes no => a.literalCount + b.literalCount + yes.literalCount + no.literalCount

theorem literalPayload_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    e.literalPayload ≤ e.literalCount * (8 * s + 7) := by
  induction e with
  | input _ => simp [literalPayload, literalCount]
  | literal word => simpa only [literalPayload, literalCount, run, Nat.one_mul] using root_payload_bound _ env hEnv hLit s hHeight
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      have hA := ha hLit.1 hHeight.2.2.1
      have hB := hb hLit.2 hHeight.2.2.2
      simp only [literalPayload, literalCount]
      nlinarith
  | ifLe a b yes no ha hb hy hn =>
      have hA := ha hLit.1 hHeight.2.2.1
      have hB := hb hLit.2.1 hHeight.2.2.2.1
      have hY := hy hLit.2.2.1 hHeight.2.2.2.2.1
      have hN := hn hLit.2.2.2 hHeight.2.2.2.2.2
      simp only [literalPayload, literalCount]
      nlinarith

theorem evaluationStorage_contract {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s)
    (hEnvHeight : ∀ j, RationalHeight (value (env.read j)) s) :
    (e.runWithStorage env).1 = e.run env ∧
      e.evaluationPayloadPeak env ≤ k * (4 * s + 3) +
        (e.literalCount + 3 * (e.depth + 1)) * (8 * s + 7) ∧
      (e.runWithStorage env).2.2 ≤ e.depth + 1 := by
  refine ⟨e.runWithStorage_refines env, ?_, e.controlDepth_bound env⟩
  have hPeak := e.resultPeak_height_bound env hEnv hLit s hHeight
  have hLiterals := e.literalPayload_bound env hEnv hLit s hHeight
  have hEnvironment := environmentPayload_bound env s hEnv hEnvHeight
  unfold evaluationPayloadPeak
  nlinarith

end BinaryRationalExpression
end Blotto
