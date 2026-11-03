import Blotto.GeneralPaperEqualRouteConstruction
import Blotto.RationalTerminalLottoHeight

/-! The actual rounded denominator gives all route operands short heights.
There is no dependence on original per-field precision after rounding, and
no runtime precision or minimum-group-mass certificate is supplied. -/
namespace Blotto.GeneralPaperEqualNativeRouteCost
open GeneralPaperEqualRouteConstruction
open GeneralPaperEqualNativeSampler (rounded roundDen)
open GeneralPaperEqualFiniteKernel (terminal)
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem bound_mono_groups (model : RationalCostModel) (A n s : ℕ) {m M : ℕ} (hm : m ≤ M) :
    bound model A n m s ≤ bound model A n M s := by
  have hw := binaryWordWidth_mono (Nat.add_le_add_right hm 1)
  unfold bound groupHeader indicesWork GeneralPaperEqualRouteMembers.stepBound
  gcongr

theorem headline (model : RationalCostModel) (A n s : ℕ) :
    bound model A n 3 s ≤ 64 * (n + 1) * model.rat (4 * s + 3) +
      4096 * (n + 1) * (A + binaryWordWidth (n + 1) + 1) := by
  have hOver := PaperIndexedArrayConstruction.overhead_bound id 1
    (fun w => by change w ≤ 1 * w; omega) A n n le_rfl
  have h4 : binaryWordWidth 4 = 3 := by decide
  have hR : 1 + 2 * GeneralPaperEqualRouteMembers.height s = 4 * s + 3 := by
    unfold GeneralPaperEqualRouteMembers.height expressionHeightBudget
    omega
  unfold bound groupHeader indicesWork GeneralPaperEqualRouteMembers.stepBound
  rw [h4, hR]
  nlinarith only [hOver]

theorem fields_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (terminal (rounded bits model W k values v hv) small))
    (lengths : FixedArrayTable n ℚ)
    (hLength : ∀ j, lengths.read j = (terminal (rounded bits model W k values v hv) small).length j) :
    (∀ j, RationalHeight (lengths.read j) (binaryWordWidth n + k + 9)) ∧
      ∀ g, RationalHeight (p.groups.read g).2 (binaryWordWidth n + k + 9) := by
  let i := terminal (rounded bits model W k values v hv) small
  let D := roundDen bits model W k values
  have hD := GeneralPaperEqualNativeSampler.roundDen_positive bits model W k values v hv
  have hW := GeneralPaperEqualNativeSampler.roundDen_word bits model W k values v hv
  have hLat : i.OnLattice D := by
    constructor <;> intro j <;>
      exact (GeneralPaperEqualNativeSampler.rounded_lattice bits model W k values v hv j).int_mul 2
  constructor
  · intro j
    rw [hLength j]
    exact (hLat.length_height hD (by norm_num [i, terminal]) j).mono hW
  · intro g
    rw [p.total_correct]
    exact (hLat.total_height hD (by norm_num [i, terminal]) g).mono hW

theorem native_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (terminal (rounded bits model W k values v hv) small))
    (lengths : FixedArrayTable n ℚ)
    (hLength : ∀ j, lengths.read j = (terminal (rounded bits model W k values v hv) small).length j) :
    (prepare p model A lengths hLength).2 ≤
      64 * (n + 1) * model.rat (4 * (binaryWordWidth n + k + 9) + 3) +
        4096 * (n + 1) * (A + binaryWordWidth (n + 1) + 1) := by
  have hFields := fields_height bits model W k values v hv small p lengths hLength
  have h := work p model A lengths hFields.1 hFields.2
  have hm := GeneralPaperEqualNativeCache.group_count (rounded bits model W k values v hv) small
  exact (h.trans (bound_mono_groups model A n _ hm)).trans (headline model A n _)

end Blotto.GeneralPaperEqualNativeRouteCost
