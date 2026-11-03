import Blotto.ImplicitLeafInverse
import Blotto.MonotoneResourceCuts
import Blotto.CumulativeGuideSize

/-! The R162 upper leaf-bin step queries complete decoded plateaus, locates an
exact strict weighted crossing, and retreats it to its entire plateau's first
code. Only stored blocks and logarithmic code searches are accessed. Specific
Farey decoding, complete-bin envelope/size and operation pricing remain separate
until established by the subsequent theorems. -/

namespace Blotto
open scoped Classical
namespace ImplicitLeafCounts

structure UpperBin where
  resource : ℚ
  lo : ℕ
  hi : ℕ
  mass : ℚ
  deriving DecidableEq, Repr

def plateauEnd (C : ℕ) (decode : ℕ → ℚ) (start : ℕ) : ℕ :=
  min C ((MonotoneResourceCuts.strict C decode (decode start)).1 - 1)

def upperBinEnd (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (gamma : ℚ) (start : ℕ) : ℕ :=
  let target := gamma * prefixMass blocks (plateauEnd C decode start : ℤ)
  if totalMass blocks ≤ target then C else
    match inverseStrict blocks target with
    | none => C
    | some crossing => (MonotoneResourceCuts.weak C decode (decode crossing)).1 - 1

def upperBinStep (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (gamma : ℚ) (start : ℕ) : UpperBin :=
  let last := upperBinEnd C blocks decode gamma start
  ⟨decode start, start, last, prefixMass blocks (last : ℤ) - prefixMass blocks ((start : ℤ) - 1)⟩

theorem plateauEnd_bounds (C : ℕ) (decode : ℕ → ℚ)
    (hm : MonotoneResourceCuts.MonotoneDecode C decode) (start : ℕ) (hs : start ≤ C) :
    start ≤ plateauEnd C decode start ∧ plateauEnd C decode start ≤ C := by
  have hc := MonotoneResourceCuts.strict_contract C decode hm (decode start)
  have hFalse : ¬(MonotoneResourceCuts.strict C decode (decode start)).1 ≤ start := by
    intro h
    have he := (hc.2 start hs).mpr h
    exact lt_irrefl _ he
  unfold plateauEnd
  omega

theorem plateauEnd_same (C : ℕ) (decode : ℕ → ℚ)
    (hm : MonotoneResourceCuts.MonotoneDecode C decode) (start : ℕ) (hs : start ≤ C)
    (code : ℕ) (hc : start ≤ code ∧ code ≤ plateauEnd C decode start) : decode code = decode start := by
  have hb := plateauEnd_bounds C decode hm start hs
  have hLower := hm start code hc.1 (hc.2.trans hb.2)
  have hStrict := MonotoneResourceCuts.strict_contract C decode hm (decode start)
  have hAbove : ¬decode start < decode code := by
    intro h
    have he := (hStrict.2 code (hc.2.trans hb.2)).mp h
    unfold plateauEnd at hc
    have hz : 0 < (MonotoneResourceCuts.strict C decode (decode start)).1 := by
      have hFalse : ¬(MonotoneResourceCuts.strict C decode (decode start)).1 ≤ start := by
        intro hn; exact lt_irrefl _ ((hStrict.2 start hs).mpr hn)
      omega
    omega
  exact le_antisymm (le_of_not_gt hAbove) hLower

theorem plateauEnd_after (C : ℕ) (decode : ℕ → ℚ)
    (hm : MonotoneResourceCuts.MonotoneDecode C decode) (start : ℕ) (_hs : start ≤ C)
    (code : ℕ) (hc : plateauEnd C decode start < code ∧ code ≤ C) : decode start < decode code := by
  have hStrict := MonotoneResourceCuts.strict_contract C decode hm (decode start)
  apply (hStrict.2 code hc.2).mpr
  unfold plateauEnd at hc
  omega

theorem upperBinEnd_contract (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (start : ℕ) (hs : start ≤ C) :
    start ≤ upperBinEnd C blocks decode gamma start ∧ upperBinEnd C blocks decode gamma start ≤ C ∧
      prefixMass blocks (upperBinEnd C blocks decode gamma start : ℤ) ≤
        gamma * prefixMass blocks (plateauEnd C decode start : ℤ) := by
  have hn : Nonnegative blocks := fun block hb => (hw block hb).le
  have hPlateau := plateauEnd_bounds C decode hm start hs
  have hPrefix := partition_prefixMass_positive C blocks hp hw (plateauEnd C decode start : ℤ) (by omega)
  let target := gamma * prefixMass blocks (plateauEnd C decode start : ℤ)
  have hTarget : 0 ≤ target := mul_nonneg (by linarith) hPrefix.le
  unfold upperBinEnd
  dsimp only
  change start ≤ (if totalMass blocks ≤ target then C else
      match inverseStrict blocks target with | none => C | some crossing => (MonotoneResourceCuts.weak C decode (decode crossing)).1 - 1) ∧
    (if totalMass blocks ≤ target then C else
      match inverseStrict blocks target with | none => C | some crossing => (MonotoneResourceCuts.weak C decode (decode crossing)).1 - 1) ≤ C ∧
    prefixMass blocks (Int.ofNat (if totalMass blocks ≤ target then C else
      match inverseStrict blocks target with | none => C | some crossing => (MonotoneResourceCuts.weak C decode (decode crossing)).1 - 1)) ≤ target
  by_cases hLast : totalMass blocks ≤ target
  · simp only [hLast, ite_true]
    refine ⟨hs, le_rfl, ?_⟩
    change prefixMass blocks (C : ℤ) ≤ target
    rw [partition_prefixMass_full C blocks hp (C : ℤ) le_rfl]
    exact hLast
  · simp only [hLast, ite_false]
    rcases inverseStrict_contract C blocks hp hw target ⟨hTarget, lt_of_not_ge hLast⟩ with ⟨crossing, hi, hb, ht⟩
    rw [hi]
    dsimp only
    have hCross : plateauEnd C decode start < crossing.val := by
      by_contra hc
      have hMono := prefixMass_mono blocks hn (show (crossing.val : ℤ) ≤ plateauEnd C decode start by omega)
      have hGamma : prefixMass blocks (plateauEnd C decode start : ℤ) ≤ target := by
        dsimp only [target]
        nlinarith
      linarith
    have hGreater := plateauEnd_after C decode hm start hs crossing.val ⟨hCross, by omega⟩
    have hWeak := MonotoneResourceCuts.weak_contract C decode hm (decode crossing.val)
    have hFirst : (MonotoneResourceCuts.weak C decode (decode crossing.val)).1 ≤ crossing.val :=
      (hWeak.2 crossing.val (by omega)).mp le_rfl
    have hStart : start < (MonotoneResourceCuts.weak C decode (decode crossing.val)).1 := by
      by_contra hc
      have hLe := (hWeak.2 start hs).mpr (by omega)
      linarith
    refine ⟨by omega, by omega, ?_⟩
    change prefixMass blocks (((MonotoneResourceCuts.weak C decode (decode crossing.val)).1 - 1 : ℕ) : ℤ) ≤ target
    have hMono := prefixMass_mono blocks hn (show
      ((MonotoneResourceCuts.weak C decode (decode crossing.val)).1 - 1 : ℕ) ≤ (crossing.val : ℤ) - 1 by omega)
    exact hMono.trans hb

theorem upperBinStep_positive (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (start : ℕ) (hs : start ≤ C) :
    0 < (upperBinStep C blocks decode gamma start).mass := by
  have hb := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hs
  rw [upperBinStep]
  dsimp only
  rw [partition_prefixMass_labels C blocks hp, partition_prefixMass_labels C blocks hp]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_pos'
  · intro code _
    have hm := (partition_labelMass_positive C blocks hp hw code).le
    split_ifs <;> first | omega | linarith
  · refine ⟨⟨start, by omega⟩, Finset.mem_univ _, ?_⟩
    have hFirst : (start : ℤ) ≤ upperBinEnd C blocks decode gamma start := by omega
    have hNot : ¬(start : ℤ) ≤ (start : ℤ) - 1 := by omega
    simp only [hFirst, hNot, ite_true, ite_false, sub_zero]
    exact partition_labelMass_positive C blocks hp hw ⟨start, by omega⟩

def upperBins (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (gamma : ℚ) (start : ℕ) : List UpperBin :=
  if start ≤ C then
    let bin := upperBinStep C blocks decode gamma start
    if start ≤ bin.hi then bin :: upperBins C blocks decode gamma (bin.hi + 1) else []
  else []
termination_by C + 1 - start
decreasing_by
  simp_wf
  have _hs : start ≤ C := by assumption
  have hp : start ≤ (upperBinStep C blocks decode gamma start).hi := by assumption
  omega

def upperGuide (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (gamma : ℚ) : List CumulativeGuidePruning.Atom :=
  (upperBins C blocks decode gamma 0).map (fun bin => (bin.resource, bin.mass))

def BinsCover (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) : ℕ → List UpperBin → Prop
  | next, [] => next = C + 1
  | next, bin :: rest => bin.lo = next ∧ bin.lo ≤ bin.hi ∧ bin.hi ≤ C ∧
      bin.resource = decode bin.lo ∧
      bin.mass = prefixMass blocks (bin.hi : ℤ) - prefixMass blocks ((bin.lo : ℤ) - 1) ∧
      BinsCover C blocks decode (bin.hi + 1) rest

theorem upperBins_cover (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (start : ℕ) (hs : start ≤ C + 1) :
    BinsCover C blocks decode start (upperBins C blocks decode gamma start) := by
  rw [upperBins]
  by_cases hActive : start ≤ C
  · rw [ite_eq_left hActive]
    have he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hActive
    have hStep : start ≤ (upperBinStep C blocks decode gamma start).hi := he.1
    rw [ite_eq_left hStep]
    change (upperBinStep C blocks decode gamma start).lo = start ∧
      (upperBinStep C blocks decode gamma start).lo ≤ (upperBinStep C blocks decode gamma start).hi ∧
      (upperBinStep C blocks decode gamma start).hi ≤ C ∧
      (upperBinStep C blocks decode gamma start).resource = decode (upperBinStep C blocks decode gamma start).lo ∧
      (upperBinStep C blocks decode gamma start).mass = _ ∧ _
    refine ⟨rfl, hStep, he.2.1, rfl, rfl, ?_⟩
    exact upperBins_cover C blocks hp hw decode hm gamma hg
      ((upperBinStep C blocks decode gamma start).hi + 1) (by dsimp only [upperBinStep]; omega)
  · rw [ite_eq_right hActive]
    change start = C + 1
    omega
termination_by C + 1 - start
decreasing_by
  have _he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hActive
  dsimp only [upperBinStep]
  omega

theorem upperBinEnd_plateau_covered (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (start : ℕ) (hs : start ≤ C) :
    plateauEnd C decode start ≤ upperBinEnd C blocks decode gamma start := by
  have hEnd := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hs
  have hn : Nonnegative blocks := fun block hb => (hw block hb).le
  have hPlateau := plateauEnd_bounds C decode hm start hs
  have hPrefix := partition_prefixMass_positive C blocks hp hw (plateauEnd C decode start : ℤ) (by omega)
  let target := gamma * prefixMass blocks (plateauEnd C decode start : ℤ)
  have hGamma : prefixMass blocks (plateauEnd C decode start : ℤ) ≤ target := by dsimp only [target]; nlinarith
  unfold upperBinEnd
  dsimp only
  by_cases hLast : totalMass blocks ≤ target
  · have he : totalMass blocks ≤ gamma * prefixMass blocks (plateauEnd C decode start : ℤ) := hLast
    rw [ite_eq_left he]
    exact hPlateau.2
  · have he : ¬totalMass blocks ≤ gamma * prefixMass blocks (plateauEnd C decode start : ℤ) := hLast
    rw [ite_eq_right he]
    rcases inverseStrict_contract C blocks hp hw target ⟨by positivity, lt_of_not_ge hLast⟩ with ⟨cross, hi, _, ht⟩
    change inverseStrict blocks (gamma * prefixMass blocks (plateauEnd C decode start : ℤ)) = some cross.val at hi
    rw [hi]
    dsimp only
    have hCross : plateauEnd C decode start < cross.val := by
      by_contra hc
      have hMono := prefixMass_mono blocks hn (show (cross.val : ℤ) ≤ plateauEnd C decode start by omega)
      linarith
    have hGreater := plateauEnd_after C decode hm start hs cross.val ⟨hCross, by omega⟩
    have hValue := plateauEnd_same C decode hm start hs (plateauEnd C decode start) ⟨hPlateau.1, le_rfl⟩
    have hWeak := MonotoneResourceCuts.weak_contract C decode hm (decode cross.val)
    have hAfter : plateauEnd C decode start < (MonotoneResourceCuts.weak C decode (decode cross.val)).1 := by
      by_contra hc
      have hLe := (hWeak.2 (plateauEnd C decode start) hPlateau.2).mpr (by omega)
      rw [hValue] at hLe
      linarith
    omega

theorem upperBinEnd_next_strict (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (start : ℕ) (hs : start ≤ C)
    (hNext : upperBinEnd C blocks decode gamma start < C) :
    decode start < decode (upperBinEnd C blocks decode gamma start + 1) := by
  have hpEnd := upperBinEnd_plateau_covered C blocks hp hw decode hm gamma hg start hs
  exact plateauEnd_after C decode hm start hs _ ⟨by omega, by omega⟩

theorem binsCover_total (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (bins : List UpperBin)
    (next : ℕ) (h : BinsCover C blocks decode next bins) :
    (bins.map UpperBin.mass).sum = prefixMass blocks (C : ℤ) - prefixMass blocks ((next : ℤ) - 1) := by
  induction bins generalizing next with
  | nil =>
    change next = C + 1 at h
    simp only [List.map_nil, List.sum_nil]
    have he : ((next : ℤ) - 1) = (C : ℤ) := by omega
    rw [he, sub_self]
  | cons bin rest ih =>
    change bin.lo = next ∧ bin.lo ≤ bin.hi ∧ bin.hi ≤ C ∧ bin.resource = decode bin.lo ∧
      bin.mass = prefixMass blocks (bin.hi : ℤ) - prefixMass blocks ((bin.lo : ℤ) - 1) ∧
      BinsCover C blocks decode (bin.hi + 1) rest at h
    simp only [List.map_cons, List.sum_cons]
    rw [h.2.2.2.2.1, ih (bin.hi + 1) h.2.2.2.2.2, h.1]
    have he : ((bin.hi + 1 : ℕ) : ℤ) - 1 = (bin.hi : ℤ) := by omega
    rw [he]
    ring

theorem upperGuide_totalMass (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ) (hg : 1 ≤ gamma) :
    CumulativeGuidePruning.totalMass (upperGuide C blocks decode gamma) = totalMass blocks := by
  have ht := binsCover_total C blocks decode (upperBins C blocks decode gamma 0) 0
    (upperBins_cover C blocks hp hw decode hm gamma hg 0 (by omega))
  unfold upperGuide CumulativeGuidePruning.totalMass
  simp only [List.map_map, Function.comp_def] at *
  change ((upperBins C blocks decode gamma 0).map UpperBin.mass).sum = _
  rw [ht, partition_prefixMass_full C blocks hp (C : ℤ) le_rfl]
  have hz := prefixMass_negative blocks (-1) (by omega)
  simp only [Int.ofNat_zero, zero_sub, hz, sub_zero]

theorem upperGuide_positive (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ) (hg : 1 ≤ gamma)
    (start : ℕ) (_hs : start ≤ C + 1) :
    ∀ bin ∈ upperBins C blocks decode gamma start, 0 < bin.mass := by
  rw [upperBins]
  by_cases hActive : start ≤ C
  · rw [ite_eq_left hActive]
    have he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hActive
    have hStep : start ≤ (upperBinStep C blocks decode gamma start).hi := he.1
    rw [ite_eq_left hStep]
    intro bin hb
    rcases List.mem_cons.mp hb with hBin | hb
    · subst bin
      exact upperBinStep_positive C blocks hp hw decode hm gamma hg start hActive
    · exact upperGuide_positive C blocks hp hw decode hm gamma hg
        ((upperBinStep C blocks decode gamma start).hi + 1) (by dsimp only [upperBinStep]; omega) bin hb
  · rw [ite_eq_right hActive]
    simp
termination_by C + 1 - start
decreasing_by
  have _he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hActive
  dsimp only [upperBinStep]
  omega

end ImplicitLeafCounts
end Blotto
