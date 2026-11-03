import Blotto.ImplicitLeafUpperGuideLaw
import Blotto.ResourceBlockHistory
import Blotto.MonotonePlateauBounds
import Blotto.CumulativeGuideLogSize

/-! The actual R162 upper leaf constructor has geometric growth of complete
start-plateau prefix masses. Its logarithmic bin count is instantiated with
actual resource-driven rounded block histories, without a minimum-mass oracle.
Specific Farey decoding and complete bit/space pricing remain separate. -/

namespace Blotto
open scoped Classical
namespace ImplicitLeafCounts

def plateauPrefix (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (start : ℕ) : ℚ :=
  prefixMass blocks (plateauEnd C decode start : ℤ)

def upperStartHeights (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (gamma : ℚ) (start : ℕ) : List ℚ :=
  (upperBins C blocks decode gamma start).map (fun bin => plateauPrefix C blocks decode bin.lo)

theorem upperBinEnd_next_height (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ) (hg : 1 ≤ gamma)
    (start : ℕ) (hs : start ≤ C) (hNonfinal : upperBinEnd C blocks decode gamma start < C) :
    gamma * plateauPrefix C blocks decode start <
      plateauPrefix C blocks decode (upperBinEnd C blocks decode gamma start + 1) := by
  have hn : Nonnegative blocks := fun block hb => (hw block hb).le
  have hpBounds := plateauEnd_bounds C decode hm start hs
  have hPrefix := partition_prefixMass_positive C blocks hp hw (plateauEnd C decode start : ℤ) (by omega)
  let target := gamma * plateauPrefix C blocks decode start
  have hLevel : 0 ≤ target := by unfold target plateauPrefix; positivity
  have hLast : ¬totalMass blocks ≤ target := by
    intro h
    have he : upperBinEnd C blocks decode gamma start = C := by
      unfold upperBinEnd
      change (if totalMass blocks ≤ target then C else _) = C
      rw [ite_eq_left h]
    rw [he] at hNonfinal
    omega
  rcases inverseStrict_contract C blocks hp hw target ⟨hLevel, lt_of_not_ge hLast⟩ with ⟨cross, hInv, _, hThrough⟩
  have hEnd : upperBinEnd C blocks decode gamma start =
      (MonotoneResourceCuts.weak C decode (decode cross.val)).1 - 1 := by
    unfold upperBinEnd
    change (if totalMass blocks ≤ target then C else _) = _
    rw [ite_eq_right hLast]
    change (match inverseStrict blocks target with | none => C | some crossing => _) = _
    rw [hInv]
  have hCross : plateauEnd C decode start < cross.val := by
    by_contra hc
    have hMono := prefixMass_mono blocks hn (show (cross.val : ℤ) ≤ plateauEnd C decode start by omega)
    have hGamma : plateauPrefix C blocks decode start ≤ target := by unfold target plateauPrefix; nlinarith
    change target < prefixMass blocks (cross.val : ℤ) at hThrough
    unfold plateauPrefix at hGamma
    linarith
  have hFirst := MonotoneResourceCuts.separated_plateau_progress C decode hm start cross.val hs (by omega)
    (by unfold MonotoneResourceCuts.plateauEnd; unfold plateauEnd at hCross; omega)
  have hFirstLe := MonotoneResourceCuts.plateauFirst_le C decode hm cross.val (by omega)
  have hFirstValue := MonotoneResourceCuts.plateauFirst_value C decode hm cross.val (by omega)
  have hNext : upperBinEnd C blocks decode gamma start + 1 = MonotoneResourceCuts.plateauFirst C decode cross.val := by
    rw [hEnd]
    unfold MonotoneResourceCuts.plateauFirst at hFirst ⊢
    omega
  have hNextBounds := plateauEnd_bounds C decode hm (upperBinEnd C blocks decode gamma start + 1) (by omega)
  have hEqual : decode (upperBinEnd C blocks decode gamma start + 1) = decode cross.val := by rw [hNext]; exact hFirstValue
  have hCrossLast : cross.val ≤ plateauEnd C decode (upperBinEnd C blocks decode gamma start + 1) := by
    have hcStrict := MonotoneResourceCuts.code_lt_strict_self C decode hm cross.val (by omega)
    unfold plateauEnd
    rw [hEqual]
    omega
  have hMass := prefixMass_mono blocks hn (show (cross.val : ℤ) ≤
    (plateauEnd C decode (upperBinEnd C blocks decode gamma start + 1) : ℤ) by omega)
  exact hThrough.trans_le hMass

theorem upperStartHeights_head (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ) (hg : 1 ≤ gamma)
    (start : ℕ) (hs : start ≤ C) :
    upperStartHeights C blocks decode gamma start = plateauPrefix C blocks decode start ::
      upperStartHeights C blocks decode gamma (upperBinEnd C blocks decode gamma start + 1) := by
  have he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hs
  unfold upperStartHeights
  rw [upperBins, ite_eq_left hs]
  have hStep : start ≤ (upperBinStep C blocks decode gamma start).hi := he.1
  rw [ite_eq_left hStep]
  rfl

theorem upperStartHeights_lower (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ) (hg : 1 ≤ gamma)
    (start : ℕ) (hs : start ≤ C) :
    ∀ height ∈ upperStartHeights C blocks decode gamma start, plateauPrefix C blocks decode start ≤ height := by
  intro height hh
  rcases List.mem_map.mp hh with ⟨bin, hb, rfl⟩
  have hBin := localUpperBins_after C blocks decode gamma (upperBins C blocks decode gamma start) start
    (upperBins_local C blocks hp hw decode hm gamma hg start (by omega)) bin hb
  have hStart := plateauEnd_bounds C decode hm start hs
  have hBinEnd := plateauEnd_bounds C decode hm bin.lo (hBin.2.1.trans hBin.2.2.1)
  have hDecode := hm start bin.lo hBin.1 (hBin.2.1.trans hBin.2.2.1)
  have hEndOrder : plateauEnd C decode start ≤ plateauEnd C decode bin.lo := by
    by_contra hn
    have hOwn : decode bin.lo < decode (plateauEnd C decode start) :=
      plateauEnd_after C decode hm bin.lo (hBin.2.1.trans hBin.2.2.1) _ ⟨by omega, hStart.2⟩
    have hStartSame := plateauEnd_same C decode hm start hs (plateauEnd C decode start) ⟨hStart.1, le_rfl⟩
    rw [hStartSame] at hOwn
    linarith
  unfold plateauPrefix
  exact prefixMass_mono blocks (fun block hb => (hw block hb).le) (by omega)

theorem upperStartHeights_geometric (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ) (hg : 1 ≤ gamma)
    (start : ℕ) (_hs : start ≤ C + 1) :
    (upperStartHeights C blocks decode gamma start).Pairwise (fun first last => gamma * first < last) := by
  by_cases hActive : start ≤ C
  · rw [upperStartHeights_head C blocks hp hw decode hm gamma hg start hActive]
    apply List.pairwise_cons.mpr
    constructor
    · intro height hh
      have hEnd := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hActive
      have hNext : upperBinEnd C blocks decode gamma start < C := by
        rcases List.mem_map.mp hh with ⟨bin, hb, _⟩
        have hBin := localUpperBins_after C blocks decode gamma
          (upperBins C blocks decode gamma (upperBinEnd C blocks decode gamma start + 1))
          (upperBinEnd C blocks decode gamma start + 1)
          (upperBins_local C blocks hp hw decode hm gamma hg _ (by omega)) bin hb
        omega
      exact (upperBinEnd_next_height C blocks hp hw decode hm gamma hg start hActive hNext).trans_le
        (upperStartHeights_lower C blocks hp hw decode hm gamma hg _ (by omega) height hh)
    · have he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hActive
      exact upperStartHeights_geometric C blocks hp hw decode hm gamma hg
        (upperBinEnd C blocks decode gamma start + 1) (by omega)
  · unfold upperStartHeights
    rw [upperBins, ite_eq_right hActive]
    simp
termination_by C + 1 - start
decreasing_by
  have _he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hActive
  omega

theorem upperStartHeights_total_bound (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ) (hg : 1 ≤ gamma)
    (start : ℕ) (hs : start ≤ C + 1) :
    ∀ height ∈ upperStartHeights C blocks decode gamma start, height ≤ totalMass blocks := by
  intro height hh
  rcases List.mem_map.mp hh with ⟨bin, hb, rfl⟩
  have hBin := localUpperBins_after C blocks decode gamma (upperBins C blocks decode gamma start) start
    (upperBins_local C blocks hp hw decode hm gamma hg start hs) bin hb
  have hpEnd := plateauEnd_bounds C decode hm bin.lo (hBin.2.1.trans hBin.2.2.1)
  unfold plateauPrefix
  have hMono := prefixMass_mono blocks (fun block hb => (hw block hb).le)
    (show (plateauEnd C decode bin.lo : ℤ) ≤ (C : ℤ) by omega)
  rw [partition_prefixMass_full C blocks hp (C : ℤ) le_rfl] at hMono
  exact hMono

theorem upperGuide_size_power (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ) (hg : 1 ≤ gamma) :
    0 < plateauPrefix C blocks decode 0 ∧
      gamma ^ ((upperGuide C blocks decode gamma).length - 1) * plateauPrefix C blocks decode 0 ≤ totalMass blocks := by
  have hBounds := plateauEnd_bounds C decode hm 0 (by omega)
  have hPositive := partition_prefixMass_positive C blocks hp hw (plateauEnd C decode 0 : ℤ) (by omega)
  have hHead := upperStartHeights_head C blocks hp hw decode hm gamma hg 0 (by omega)
  let rest := upperStartHeights C blocks decode gamma (upperBinEnd C blocks decode gamma 0 + 1)
  have hGeom := upperStartHeights_geometric C blocks hp hw decode hm gamma hg 0 (by omega)
  rw [hHead] at hGeom
  have hWeak := hGeom.imp (fun h => h.le)
  have hPow := CumulativeGuidePruning.positive_geometric_list_power (plateauPrefix C blocks decode 0) rest gamma
    (by linarith) hWeak rest.length (by simp)
  have hLength : (upperGuide C blocks decode gamma).length = rest.length + 1 := by
    have he := congrArg List.length hHead
    simp only [upperStartHeights, upperGuide, List.length_map, List.length_cons] at he ⊢
    simpa only [rest, upperStartHeights, List.length_map] using he
  have hTotal := upperStartHeights_total_bound C blocks hp hw decode hm gamma hg 0 (by omega)
    ((plateauPrefix C blocks decode 0 :: rest)[rest.length])
    (by rw [hHead]; exact List.getElem_mem (by simp [rest]))
  refine ⟨hPositive, ?_⟩
  rw [hLength, Nat.add_sub_cancel]
  exact hPow.trans hTotal

theorem upperGuide_length_log_bound (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((upperGuide C blocks decode (1 + delta)).length : ℝ) ≤
      1 + 2 * Real.log ((totalMass blocks : ℝ) / (plateauPrefix C blocks decode 0 : ℝ)) / (delta : ℝ) := by
  have hpBound := upperGuide_size_power C blocks hp hw decode hm (1 + delta) (by linarith)
  have hf : (0 : ℝ) < (plateauPrefix C blocks decode 0 : ℝ) := by exact_mod_cast hpBound.1
  have hPow : (1 + (delta : ℝ)) ^ ((upperGuide C blocks decode (1 + delta)).length - 1) *
      (plateauPrefix C blocks decode 0 : ℝ) ≤ (totalMass blocks : ℝ) := by exact_mod_cast hpBound.2
  have hLog := CumulativeGuidePruning.geometric_delta_log_bound _ (by exact_mod_cast hd) (by exact_mod_cast hu) hf hPow
  have hHead := upperStartHeights_head C blocks hp hw decode hm (1 + delta) (by linarith) 0 (by omega)
  have hLength : 0 < (upperGuide C blocks decode (1 + delta)).length := by
    have he := congrArg List.length hHead
    simp only [upperStartHeights, upperGuide, List.length_map, List.length_cons] at he ⊢
    omega
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hd
  have hDiv := (le_div_iff₀ hdR).mpr hLog
  have hNat : (upperGuide C blocks decode (1 + delta)).length - 1 + 1 =
      (upperGuide C blocks decode (1 + delta)).length := by omega
  have hCast := congrArg (fun n : ℕ => (n : ℝ)) hNat
  simp only [Nat.cast_add, Nat.cast_one] at hCast
  linarith

theorem plateauPrefix_log_range (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) :
    Real.log ((totalMass blocks : ℝ) / (plateauPrefix C blocks decode 0 : ℝ)) ≤
      Real.log ((totalMass blocks : ℝ) / (prefixMass blocks 0 : ℝ)) := by
  have hpEnd := plateauEnd_bounds C decode hm 0 (by omega)
  have hp0 := partition_prefixMass_positive C blocks hp hw 0 le_rfl
  have ht := partition_prefixMass_positive C blocks hp hw (C : ℤ) (by omega)
  rw [partition_prefixMass_full C blocks hp (C : ℤ) le_rfl] at ht
  have hMass := prefixMass_mono blocks (fun block hb => (hw block hb).le)
    (show (0 : ℤ) ≤ (plateauEnd C decode 0 : ℤ) by omega)
  have hfR : (0 : ℝ) < prefixMass blocks 0 := by exact_mod_cast hp0
  have htR : (0 : ℝ) < totalMass blocks := by exact_mod_cast ht
  have hMassR : (prefixMass blocks 0 : ℝ) ≤ (plateauPrefix C blocks decode 0 : ℝ) := by exact_mod_cast hMass
  exact Real.log_le_log (div_pos htR (hfR.trans_le hMassR))
    (div_le_div_of_nonneg_left htR.le hfR hMassR)

theorem resourceBlockHistory_upperGuide_length {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (field : Fin m) (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((upperGuide (caps field) (resourceBlockHistory caps decode selected opponent eta theta past field)
      (decode field) (1 + delta)).length : ℝ) ≤
      1 + 2 * (Real.log ((caps field + 1 : ℕ) : ℝ) +
        (SparseMW.fieldUpdateCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ))) / (delta : ℝ) := by
  let blocks := resourceBlockHistory caps decode selected opponent eta theta past field
  have hp := resourceBlockHistory_partition caps decode selected opponent eta theta past field
  have hw := resourceBlockHistory_positive caps decode selected opponent eta theta heta htheta past field
  have hSize := upperGuide_length_log_bound (caps field) blocks hp hw (decode field) (hm field) delta hd hu
  have hPlateau := plateauPrefix_log_range (caps field) blocks hp hw (decode field) (hm field)
  have hRange := rounded_history_log_range (sizes := fun field => caps field + 1) selected
    (resourceLoss caps decode selected opponent) eta theta heta htheta (resourceLoss_unit caps decode selected opponent)
    past field (caps field) rfl blocks hp hw (resourceBlockHistory_refines caps decode hm selected opponent eta theta past field)
  have hLog := hPlateau.trans hRange
  have hdR : (0 : ℝ) ≤ delta := by exact_mod_cast hd.le
  exact hSize.trans (add_le_add_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLog (by norm_num : (0 : ℝ) ≤ 2)) hdR) 1)

end ImplicitLeafCounts
end Blotto
