import Blotto.GeneralPaperEqualPackedOwner

/-! All retained per-field routes have native short coefficients. The owner
counts option tags, group labels, rational coefficients and array metadata,
and applies to any actual prepared route table with the indexed correctness. -/
namespace Blotto.GeneralPaperEqualRouteOwner
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEqualRetainedStorage (routeFoot route_bound)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def footprint {n m : ℕ} {G : RationalProportionalGroups n m} (A : ℕ) (p : PreparedGroupOutput G) : ℕ :=
  arrayFootprint A (routeFoot A) p.table + 32 * A

def profile (A n m s : ℕ) : ℕ := arrayProfile A n (4 + binaryWordWidth m + 2 * s + 16 * A) + 32 * A

theorem bounded {n m : ℕ} {G : RationalProportionalGroups n m} (A s : ℕ) (p : PreparedGroupOutput G)
    (h : ∀ j, RationalHeight (p.table.read j).2 s) : footprint A p ≤ profile A n m s :=
  Nat.add_le_add_right (array_bound A _ (routeFoot A) p.table (fun j => route_bound A _ (h j))) (32 * A)

theorem native_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv).weight j ≤ 1)
    (p : PreparedGroupOutput (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small).partition) (j : Fin n) :
    RationalHeight (p.table.read j).2 (binaryWordWidth n + exponent + 9) := by
  let i := GeneralPaperEqualFiniteKernel.terminal (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small
  let D := GeneralPaperEqualNativeSampler.roundDen bits model W exponent values
  have hL : ∀ j, OnRationalLattice D (i.partition.length j) := fun j =>
    (GeneralPaperEqualNativeSampler.rounded_lattice bits model W exponent values v hv j).int_mul 2
  exact (p.coefficient_height_lattice D (GeneralPaperEqualNativeSampler.roundDen_positive bits model W exponent values v hv)
    hL small i.partition_total_le j).mono (GeneralPaperEqualNativeSampler.roundDen_word bits model W exponent values v hv)

theorem native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv).weight j ≤ 1)
    (p : PreparedGroupOutput (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small).partition) :
    footprint A p ≤ profile A n 3 (binaryWordWidth n + exponent + 9) := by
  have h := bounded A _ p (native_height bits model W exponent values v hv small p)
  have hm := GeneralPaperEqualNativeCache.group_count (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small
  have hw := binaryWordWidth_mono hm
  unfold profile GeneralPaperEncodedBasisStorage.arrayProfile at h ⊢
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left n (by omega)) (64 * A)) (32 * A))

end Blotto.GeneralPaperEqualRouteOwner
