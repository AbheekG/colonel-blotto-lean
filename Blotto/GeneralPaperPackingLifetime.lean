import Blotto.GeneralPaperPackingFrameLifetime

/-! One conservative reserve for input-index construction, the actual
packing scan and group-array materialization/return. The caller proves the
returned group payload bound. Shared labels are counted once in the pool;
frame charges remain linear in total work, never n times total work. -/
namespace Blotto.GeneralPaperPackingLifetime
open GeneralPaperEqualPackingExecution (run scan unit)
open GeneralPaperPackingAllocationLifetime (pool poolProfile indicesLive indicesProfile)
open GeneralPaperPackingFrameLifetime (frames frames_bound frameProfile)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def initialPrice {n : ℕ} (values : FixedArrayTable n ℚ) (A : ℕ) (x : Fin n) : ℕ :=
  4 * (rationalWordWidth (values.read x) + 2 * A) + 2 * unit A n

def parentFoot {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ) (B : ℚ)
    (x : Fin n) (rest : List (Fin n)) : ℕ :=
  let child := scan model A (unit A n) values B [x] (values.read x) rest
  let actual := run model A values B (x :: rest)
  rationalWordWidth (values.read x) + initialPrice values A x +
    fields A [n, (x :: rest).length, unit A n, initialPrice values A x, child.2, actual.2] + 128 * A

def window {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A : ℕ) (B : ℚ)
    (items : List (Fin n)) (borrowed returnedPayload : ℕ) : ℕ :=
  borrowed + returnedPayload + indicesLive A n n +
    match items with
    | [] => fields A [n, unit A n, (run model A values B []).2] + 128 * A
    | x :: rest => pool model A (unit A n) values B [x] rest (values.read x) +
        frames values model A B [x] (values.read x) rest + parentFoot values model A B x rest

def profile (A n F borrowed returnedPayload : ℕ) : ℕ :=
  borrowed + returnedPayload + indicesProfile A n + poolProfile A n + 32 * F + (n + 2) * frameProfile A n F

theorem owner_work_mono (A n F G B C R S : ℕ) (hF : F ≤ G) (hB : B ≤ C) (hR : R ≤ S) :
    profile A n F B R ≤ profile A n G C S := by
  have hWord : natBits (n + F + unit A n + 1) ≤ natBits (n + G + unit A n + 1) :=
    Nat.add_le_add_left (binaryWordWidth_mono (show n + F + unit A n + 1 ≤ n + G + unit A n + 1 by omega)) 1
  have hFrame : frameProfile A n F ≤ frameProfile A n G := by unfold frameProfile; omega
  have hScaled := Nat.mul_le_mul_left (n + 2) hFrame
  unfold profile
  omega

theorem bounded {n : ℕ} (values : FixedArrayTable n ℚ) (model : RationalCostModel) (A F : ℕ) (B : ℚ)
    (items : List (Fin n)) (borrowed returnedPayload : ℕ) (hL : items.length ≤ n)
    (hF : (run model A values B items).2 ≤ F) :
    window values model A B items borrowed returnedPayload ≤ profile A n F borrowed returnedPayload := by
  have hIndices := GeneralPaperPackingAllocationLifetime.indices_bound A n n le_rfl
  cases items with
  | nil =>
    have hCost : (run model A values B []).2 = unit A n := by simp only [run, values.size]
    have hUnit : 64 * A + 64 ≤ unit A n := by unfold unit; omega
    have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + F + unit A n + 1)
      [n, unit A n, (run model A values B []).2] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> omega)
    change fields A _ ≤ 3 * (natBits (n + F + unit A n + 1) + A) + 32 * A at hFields
    have hFrames : frameProfile A n F ≤ (n + 2) * frameProfile A n F := Nat.le_mul_of_pos_left _ (by omega)
    simp only [window]
    unfold profile
    unfold frameProfile at *
    omega
  | cons x rest =>
    let child := scan model A (unit A n) values B [x] (values.read x) rest
    let C := (run model A values B (x :: rest)).2
    have hC : C = initialPrice values A x + child.2 := by
      dsimp only [C, run]
      rw [values.size]
      rfl
    have hChild : child.2 ≤ F := by omega
    have hSize : [x].length + rest.length ≤ n := by
      simp only [List.length_cons, List.length_nil, Nat.zero_add]
      simp only [List.length_cons] at hL
      omega
    have hPool := GeneralPaperPackingAllocationLifetime.pool_bound model A (unit A n) values B [x] rest (values.read x) hSize
    have hFrames := frames_bound values model A F B (values.read x) [x] rest hSize hChild
    have hUnit : 64 * A + 64 ≤ unit A n := by unfold unit; omega
    have hInitial : rationalWordWidth (values.read x) + 2 * unit A n ≤ initialPrice values A x := by unfold initialPrice; omega
    have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + F + unit A n + 1)
      [n, (x :: rest).length, unit A n, initialPrice values A x, child.2, C] (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    change fields A _ ≤ 6 * (natBits (n + F + unit A n + 1) + A) + 32 * A at hFields
    have hParent : parentFoot values model A B x rest ≤ 8 * initialPrice values A x + frameProfile A n F := by
      change rationalWordWidth (values.read x) + initialPrice values A x +
        fields A [n, (x :: rest).length, unit A n, initialPrice values A x, child.2, C] + 128 * A ≤ _
      unfold frameProfile
      omega
    have hFrameScale := Nat.mul_le_mul_right (frameProfile A n F) (show rest.length + 2 ≤ n + 2 by simp only [List.length_cons] at hL; omega)
    simp only [window]
    unfold profile
    nlinarith only [hIndices, hPool, hFrames, hParent, hFrameScale, hC, hF]

end Blotto.GeneralPaperPackingLifetime
