import Blotto.GeneralPaperEqualFirstPrefixSpace

/-! Actual packed member lists and route tables at the corrected source.
Generic footprint observers count each retained label/coefficient once.
All field heights are derived from the c=256 denominator lattice. -/
namespace Blotto.GeneralPaperEqualFirstSourceOwnership
open GeneralPaperEqualFirstNativeFacts
open GeneralPaperEqualFiniteKernel (terminal)
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem fields_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (terminal (rounded bits model W k values v hv) small))
    (lengths : FixedArrayTable n ℚ)
    (hL : ∀ j, lengths.read j = (terminal (rounded bits model W k values v hv) small).length j) :
    (∀ j, RationalHeight (lengths.read j) (binaryWordWidth n+k+10)) ∧
      ∀ g, RationalHeight (p.groups.read g).2 (binaryWordWidth n+k+10) := by
  let i := terminal (rounded bits model W k values v hv) small
  let D := roundDen bits model W k values
  have hD := roundDen_positive bits model W k values v hv
  have hW := roundDen_word bits model W k values v hv
  have hLat : i.OnLattice D := by
    constructor <;> intro j <;> exact (rounded_lattice bits model W k values v hv j).int_mul 2
  constructor
  · intro j
    rw [hL j]
    exact (hLat.length_height hD (by norm_num [i, terminal]) j).mono hW
  · intro g
    rw [p.total_correct]
    exact (hLat.total_height hD (by norm_num [i, terminal]) g).mono hW

theorem packed {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (terminal (rounded bits model W k values v hv) small))
    (lengths : FixedArrayTable n ℚ)
    (hL : ∀ j, lengths.read j = (terminal (rounded bits model W k values v hv) small).length j) :
    GeneralPaperEqualPackedOwner.footprint A p ≤ GeneralPaperEqualPackedOwner.profile A n 3 (binaryWordWidth n+k+10) := by
  have h := GeneralPaperEqualPackedOwner.bounded A _ p (fields_height bits model W k values v hv small p lengths hL).2
  have hm := GeneralPaperEqualFirstNativeCache.group_count (rounded bits model W k values v hv) small
  have hScale := Nat.mul_le_mul_right (1+2*(binaryWordWidth n+k+10)+65*A) hm
  unfold GeneralPaperEqualPackedOwner.profile at h ⊢
  omega

theorem route_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1)
    (p : PreparedGroupOutput (terminal (rounded bits model W k values v hv) small).partition) (j : Fin n) :
    RationalHeight (p.table.read j).2 (binaryWordWidth n+k+10) := by
  let i := terminal (rounded bits model W k values v hv) small
  let D := roundDen bits model W k values
  have hL : ∀ j, OnRationalLattice D (i.partition.length j) :=
    fun j => (rounded_lattice bits model W k values v hv j).int_mul 2
  exact (p.coefficient_height_lattice D (roundDen_positive bits model W k values v hv)
    hL small i.partition_total_le j).mono (roundDen_word bits model W k values v hv)

theorem routes {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1)
    (p : PreparedGroupOutput (terminal (rounded bits model W k values v hv) small).partition) :
    GeneralPaperEqualRouteOwner.footprint A p ≤ GeneralPaperEqualRouteOwner.profile A n 3 (binaryWordWidth n+k+10) := by
  have h := GeneralPaperEqualRouteOwner.bounded A _ p (route_height bits model W k values v hv small p)
  have hm := GeneralPaperEqualFirstNativeCache.group_count (rounded bits model W k values v hv) small
  have hw := binaryWordWidth_mono hm
  unfold GeneralPaperEqualRouteOwner.profile GeneralPaperEncodedBasisStorage.arrayProfile at h ⊢
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left n (by omega)) (64*A)) (32*A))

end Blotto.GeneralPaperEqualFirstSourceOwnership
