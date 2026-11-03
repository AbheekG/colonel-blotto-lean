import Blotto.GeneralPaperDictionaryScale

/-! Actual preparation of one defender for budget transfer: quantize the
full rows, normalize its stored dictionary, construct the complete exact-score
table, and scan that same table with the strict normalized proxy budget.
The table is retained, including every score above the computed threshold.
-/
namespace Blotto.GeneralPaperTransferPreparation
open GeneralPaperDictionary GeneralPaperStrictScore GeneralPaperComputedThreshold
open GeneralPaperMinimum
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Prepared (T m K S : ℕ) where
  dictionary : Dictionary T m K
  table : FixedArrayTable (S+1) (Option (Selection K))
  threshold : ℕ

def prepare {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (v : RationalFieldSelector m) (S : ℕ) : Prepared T m K S :=
  let quantized := GeneralPaperRowQuantizer.buildDivisible hT hK hDiv rows
  let dictionary := normalize quantized ownBudget
  let stored := GeneralPaperComputedThreshold.table dictionary v S
  ⟨dictionary,stored,scanThreshold stored (opposingProxy/ownBudget)⟩

theorem prepare_dictionary {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (v : RationalFieldSelector m) (S : ℕ) :
    (prepare hT hK hDiv rows ownBudget opposingProxy v S).dictionary=
      normalize (GeneralPaperRowQuantizer.buildDivisible hT hK hDiv rows) ownBudget := rfl

theorem prepare_table {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (v : RationalFieldSelector m) (S : ℕ) :
    (prepare hT hK hDiv rows ownBudget opposingProxy v S).table=
      GeneralPaperComputedThreshold.table (prepare hT hK hDiv rows ownBudget opposingProxy v S).dictionary v S := rfl

theorem prepare_threshold {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (v : RationalFieldSelector m) (S : ℕ) :
    (prepare hT hK hDiv rows ownBudget opposingProxy v S).threshold=
      compute (prepare hT hK hDiv rows ownBudget opposingProxy v S).dictionary (opposingProxy/ownBudget) v S := rfl

structure UnitDictionary {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (hK : 0<K) : Prop where
  balanced : Balanced d
  zero : ∀ j,d.anchor j ⟨0,hK⟩=0
  ordered : ∀ j,Monotone (d.anchor j)
  nonnegative : ∀ j l,0≤d.anchor j l
  bounded : ∀ j l,d.anchor j l≤1
  feasible : ∀ i,Feasible 1 ((law d hT).realRow i)
  supported : Supported 1 (law d hT).law

theorem prepared_unit {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (hOwn : 0<ownBudget) (v : RationalFieldSelector m) (S : ℕ)
    (hRows : ∀ i,Feasible (ownBudget:ℝ) (fun j => ((rows.read i).read j:ℝ))) :
    UnitDictionary (prepare hT hK hDiv rows ownBudget opposingProxy v S).dictionary hT hK := by
  let q := GeneralPaperRowQuantizer.buildDivisible hT hK hDiv rows
  have hq := GeneralPaperRowQuantizer.divisible_correct hT hK hDiv rows (ownBudget:ℝ) hRows
  change UnitDictionary (normalize q ownBudget) hT hK
  have hBounds := normalized_anchor_bounds q ownBudget hOwn hT hK hq.balanced hq.feasible
  exact {
    balanced := scale_balanced q ownBudget⁻¹ hq.balanced
    zero := scale_zero q ownBudget⁻¹ hK hq.zero
    ordered := scale_ordered q ownBudget⁻¹ (inv_nonneg.mpr hOwn.le) hq.ordered
    nonnegative := fun j l => (hBounds j l).1
    bounded := fun j l => (hBounds j l).2
    feasible := normalized_rows_feasible q ownBudget hOwn hT hq.feasible
    supported := normalized_supported q ownBudget hOwn hT hq.feasible }

theorem source_security {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (hOwn : 0<ownBudget) (hOpposing : 0≤opposingProxy) (v : RationalFieldSelector m) (S : ℕ)
    (hRows : ∀ i,Feasible (ownBudget:ℝ) (fun j => ((rows.read i).read j:ℝ))) :
    security v.values ((opposingProxy/ownBudget:ℚ):ℝ)
      (law (prepare hT hK hDiv rows ownBudget opposingProxy v S).dictionary hT).law ≤
      security v.values (opposingProxy:ℝ) (law (GeneralPaperRowQuantizer.original rows) hT).law+1/(K:ℝ) := by
  rw [prepare_dictionary,Rat.cast_div,
    normalized_security _ ownBudget hOwn hT v.values (opposingProxy:ℝ)]
  have hr : (0:ℝ)≤opposingProxy := by exact_mod_cast hOpposing
  exact (GeneralPaperRowQuantizer.divisible_correct hT hK hDiv rows (ownBudget:ℝ) hRows).security
    v.values (opposingProxy:ℝ) hr

theorem threshold_le {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (v : RationalFieldSelector m) (S : ℕ) :
    (prepare hT hK hDiv rows ownBudget opposingProxy v S).threshold≤S := by
  rw [prepare_threshold]
  exact compute_le _ _ _ _

theorem threshold_lower {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (hOwn : 0<ownBudget) (hOpposing : 0<opposingProxy) (v : RationalFieldSelector m) (S : ℕ) (hS : 0<S)
    (hRows : ∀ i,Feasible (ownBudget:ℝ) (fun j => ((rows.read i).read j:ℝ))) :
    ((prepare hT hK hDiv rows ownBudget opposingProxy v S).threshold:ℝ)/(S:ℝ) ≤
      security v.values ((opposingProxy/ownBudget:ℚ):ℝ)
        (law (prepare hT hK hDiv rows ownBudget opposingProxy v S).dictionary hT).law := by
  have hu := prepared_unit hT hK hDiv rows ownBudget opposingProxy hOwn v S hRows
  rw [prepare_threshold]
  exact computed_lower _ hT hK hu.balanced v S hS hu.ordered hu.nonnegative hu.zero
    (opposingProxy/ownBudget) (div_pos hOpposing hOwn)

theorem threshold_witness {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (hOwn : 0<ownBudget) (hOpposing : 0<opposingProxy) (v : RationalFieldSelector m) (S : ℕ)
    (hRows : ∀ i,Feasible (ownBudget:ℝ) (fun j => ((rows.read i).read j:ℝ))) :
    let p := prepare hT hK hDiv rows ownBudget opposingProxy v S
    ∃ chosen labels,
      p.table.read ⟨p.threshold,Nat.lt_succ_of_le (threshold_le hT hK hDiv rows ownBudget opposingProxy v S)⟩=some chosen ∧
      rationalCost p.dictionary labels<opposingProxy/ownBudget ∧
      totalScore v S labels=p.threshold ∧ rationalCost p.dictionary labels=chosen.cost ∧
      List.ofFn labels=chosen.labels := by
  dsimp only
  have hu := prepared_unit hT hK hDiv rows ownBudget opposingProxy hOwn v S hRows
  simp only [prepare_table,prepare_threshold]
  exact computed_witness _ v S hK (opposingProxy/ownBudget) (div_pos hOpposing hOwn) hu.zero

end Blotto.GeneralPaperTransferPreparation
