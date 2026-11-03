import Blotto.GeneralPaperRaySortedCrossings

/-! Construct the binary-search midpoint depth and fuel by doubling the
actual stored batch length. No encoding-length or logarithm primitive is
executed. The on-demand query count is logarithmic in the batch length.
-/
namespace Blotto.GeneralPaperRaySearchControls
open GeneralPaperRayOracleSearch
set_option autoImplicit false
set_option maxHeartbeats 2500000

def depth (n : ℕ) : ℕ := (GeneralPaperPowerCeiling.ceiling n).doublings+1

theorem size_cap (n : ℕ) : n<2^depth n := by
  have hl := GeneralPaperPowerCeiling.ceiling_lower n
  have hp := GeneralPaperPowerCeiling.ceiling_power n
  exact (hl.trans_eq hp).trans_lt (GeneralPaperBoundedQuotient.dyadic_cap _)

theorem depth_bound (n : ℕ) : depth n≤binaryWordWidth n+1 := by
  have hh := GeneralPaperPowerCeiling.loop_depth n 1 (by decide)
  exact Nat.add_le_add_right hh 1

def selected {n : ℕ} (query : Fin n → Bool × ℕ) : Result :=
  let scale := GeneralPaperPowerCeiling.ceiling n
  let result := run query (scale.doublings+1) (scale.doublings+1) 0 n
  ⟨result.rank,result.work+scale.work+16,result.probes⟩

theorem selected_valid {n : ℕ} (query : Fin n → Bool × ℕ) (hDown : Downward query) :
    Valid query (selected query).rank := by
  apply run_spec query (depth n) (depth n) 0 n hDown (Nat.zero_le _) le_rfl (size_cap n)
    (by simpa only [Nat.sub_zero] using size_cap n)
  · intro i hi
    omega
  · intro i hi
    have hh := i.isLt
    omega

theorem selected_probes {n : ℕ} (query : Fin n → Bool × ℕ) : (selected query).probes≤depth n :=
  run_probes query (depth n) (depth n) 0 n

theorem logarithmic_probes {n : ℕ} (query : Fin n → Bool × ℕ) : (selected query).probes≤binaryWordWidth n+1 :=
  (selected_probes query).trans (depth_bound n)

theorem selected_work {n : ℕ} (query : Fin n → Bool × ℕ) (E : ℕ) (hWork : ∀ i,(query i).2≤E) :
    (selected query).work≤depth n*(12*depth n+34+E)+12*binaryWordWidth n+26 := by
  have hr := run_work query (depth n) (depth n) 0 n E hWork
  have hc := GeneralPaperPowerCeiling.ceiling_work n
  change (run query (depth n) (depth n) 0 n).work+(GeneralPaperPowerCeiling.ceiling n).work+16≤_
  omega

end Blotto.GeneralPaperRaySearchControls
