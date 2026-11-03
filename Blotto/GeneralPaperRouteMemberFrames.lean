import Blotto.GeneralPaperRouteTableLifetime

/-! Actual cached coefficient/write recursion. Scalar words/scratch are paid
by the reached division charge; only indices, prices and references remain
per pending frame. One route-table backing payload is owned by the caller. -/
namespace Blotto.GeneralPaperRouteMemberFrames
open GeneralPaperEqualRouteMembers (run)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def header {n m : ℕ} (A : ℕ) (j : Fin n) (g : Fin m) : ℕ :=
  32 * (A + binaryWordWidth (j.val + 1) + binaryWordWidth (g.val + 1) + 1)

def frameProfile (A n m F : ℕ) : ℕ := 8 * (natBits (n + m + F + A + 1) + A) + 32 * A

def baseFoot {n m : ℕ} (A : ℕ) (g : Fin m) : ℕ := fields A [n, m, g.val, 16 * A + 16] + 64 * A

def stepFoot {n m : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) (j : Fin n) (rest : List (Fin n)) (table : FixedArrayTable n (GroupRoute m)) : ℕ :=
  let coefficient := GeneralPaperRationalScalarStep.run model A .div (values.read j) total
  let child := run model A values g total rest (table.write j (some g, coefficient.1))
  let actual := run model A values g total (j :: rest) table
  GeneralPaperExpressionStorageBudget.scalarFrame model A .div (values.read j) total +
    fields A [n, m, j.val, g.val, coefficient.2, header A j g, child.2, actual.2] + 128 * A

theorem base_bound {m : ℕ} (A n F : ℕ) (g : Fin m) (hF : 16 * A + 16 ≤ F) :
    baseFoot (n := n) A g ≤ 32 * (16 * A + 16) + frameProfile A n m F := by
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + m + F + A + 1)
    [n, m, g.val, 16 * A + 16] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 4 * (natBits (n + m + F + A + 1) + A) + 32 * A at hFields
  unfold baseFoot frameProfile
  omega

theorem step_bound {n m : ℕ} (model : RationalCostModel) (A F : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) (j : Fin n) (rest : List (Fin n)) (table : FixedArrayTable n (GroupRoute m))
    (hF : (run model A values g total (j :: rest) table).2 ≤ F) :
    stepFoot model A values g total j rest table ≤
      32 * ((GeneralPaperRationalScalarStep.run model A .div (values.read j) total).2 + header A j g) + frameProfile A n m F := by
  let coefficient := GeneralPaperRationalScalarStep.run model A .div (values.read j) total
  let child := run model A values g total rest (table.write j (some g, coefficient.1))
  let C := (run model A values g total (j :: rest) table).2
  have hC : C = coefficient.2 + header A j g + child.2 := rfl
  have hScalar : GeneralPaperExpressionStorageBudget.scalarFrame model A .div (values.read j) total ≤ 32 * coefficient.2 :=
    GeneralPaperExpressionStorageBudget.scalar_frame_bound model A .div (values.read j) total
  have hHeader : 32 * A + 32 ≤ header A j g := by unfold header; omega
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + m + F + A + 1)
    [n, m, j.val, g.val, coefficient.2, header A j g, child.2, C] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 8 * (natBits (n + m + F + A + 1) + A) + 32 * A at hFields
  change GeneralPaperExpressionStorageBudget.scalarFrame model A .div (values.read j) total +
    fields A [n, m, j.val, g.val, coefficient.2, header A j g, child.2, C] + 128 * A ≤ 32 * (coefficient.2 + header A j g) + frameProfile A n m F
  unfold frameProfile
  omega

def frames {n m : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) : List (Fin n) → FixedArrayTable n (GroupRoute m) → ℕ
  | [], _ => baseFoot (n := n) A g
  | j :: rest, table => stepFoot model A values g total j rest table +
      frames model A values g total rest (table.write j (some g, (GeneralPaperRationalScalarStep.run model A .div (values.read j) total).1))

theorem bounded {n m : ℕ} (model : RationalCostModel) (A F : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) (items : List (Fin n)) (table : FixedArrayTable n (GroupRoute m))
    (hF : (run model A values g total items table).2 ≤ F) :
    frames model A values g total items table ≤ 32 * (run model A values g total items table).2 +
      (items.length + 1) * frameProfile A n m F := by
  induction items generalizing table with
  | nil => simpa only [frames, run, List.length_nil, Nat.zero_add, one_mul] using base_bound A n F g hF
  | cons j rest ih =>
    let coefficient := GeneralPaperRationalScalarStep.run model A .div (values.read j) total
    let child := run model A values g total rest (table.write j (some g, coefficient.1))
    have hShape : (run model A values g total (j :: rest) table).2 = coefficient.2 + header A j g + child.2 := rfl
    have hStep := step_bound model A F values g total j rest table hF
    have hChild : child.2 ≤ F := by omega
    have hRest := ih (table.write j (some g, coefficient.1)) hChild
    simp only [frames, List.length_cons]
    nlinarith only [hStep, hRest, hShape]

end Blotto.GeneralPaperRouteMemberFrames
