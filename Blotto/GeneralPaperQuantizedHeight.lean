import Blotto.GeneralPaperQuotientBits

/-! Source-row height bounds survive actual quantization, proof-only size
casts and materialized unit normalization. Thus DP resource widths are
derived from the actual input rows and proxy budget, not a supplied DP-size
certificate. Literal score capacity follows from the normalized values.
-/
namespace Blotto.GeneralPaperQuantizedHeight
open GeneralPaperDictionary GeneralPaperExactScoreDP GeneralPaperStrictScore
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem zero_height (A : ℕ) (hA : 0<A) : RationalHeight 0 A := by
  have hp : 1<(2:ℕ)^A := Nat.one_lt_pow (by omega) (by decide)
  simpa only [RationalHeight,Rat.num_zero,Int.natAbs_zero,Rat.den_zero] using
    And.intro (Nat.zero_lt_of_lt hp) hp

theorem block_anchor_height {K B : ℕ} (hB : 0<B) (x : Fin (K*B) → ℚ) (A : ℕ)
    (hA : 0<A) (hx : ∀ i,RationalHeight (x i) A) (l : Fin K) :
    RationalHeight (GeneralPaperBlockQuantization.anchor hB x l) A := by
  unfold GeneralPaperBlockQuantization.anchor
  split
  · exact zero_height A hA
  · exact hx _

theorem column_height {K B : ℕ} (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ) (A : ℕ)
    (hv : ∀ i,RationalHeight (value.read i) A) (l : Fin K) :
    RationalHeight ((GeneralPaperQuantizedColumn.build hK hB value).anchors.read l) A := by
  have hA := (hv ⟨0,Nat.mul_pos hK hB⟩).positive
  rw [GeneralPaperQuantizedColumn.build_anchor]
  exact block_anchor_height hB _ A hA (fun _ => hv _) l

theorem product_height {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (A : ℕ)
    (hRows : ∀ i j,RationalHeight ((rows.read i).read j) A) (j : Fin m) (l : Fin K) :
    RationalHeight ((GeneralPaperRowQuantizer.build hK hB rows).anchor j l) A := by
  have hc (i : Fin (K*B)) : RationalHeight ((GeneralPaperRowQuantizer.columnInput rows j).read i) A := by
    simpa only [GeneralPaperRowQuantizer.columnInput,FixedArrayTable.read_ofFn] using hRows i j
  simpa only [GeneralPaperRowQuantizer.build,GeneralPaperRowQuantizer.dictionary,
    GeneralPaperRowQuantizer.prepare,FixedArrayTable.read_ofFn] using
      column_height hK hB (GeneralPaperRowQuantizer.columnInput rows j) A hc l

theorem cast_height {T K B m : ℕ} (hK : 0<K) (hB : 0<B) (h : T=K*B)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (A : ℕ)
    (hRows : ∀ i j,RationalHeight ((rows.read i).read j) A) (j : Fin m) (l : Fin K) :
    RationalHeight ((GeneralPaperRowQuantizer.castDictionary h
      (GeneralPaperRowQuantizer.build hK hB (GeneralPaperRowQuantizer.castRows h rows))).anchor j l) A := by
  subst T
  exact product_height hK hB rows A hRows j l

theorem divisible_height {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (A : ℕ)
    (hRows : ∀ i j,RationalHeight ((rows.read i).read j) A) (j : Fin m) (l : Fin K) :
    RationalHeight ((GeneralPaperRowQuantizer.buildDivisible hT hK hDiv rows).anchor j l) A :=
  cast_height hK (GeneralPaperRowQuantizer.divisor_block_pos hT hK hDiv)
    (GeneralPaperRowQuantizer.divisor_size hDiv) rows A hRows j l

theorem scale_height {T m K : ℕ} (d : Dictionary T m K) (c : ℚ) (A C : ℕ)
    (hd : ∀ j l,RationalHeight (d.anchor j l) A) (hc : RationalHeight c C) (j : Fin m) (l : Fin K) :
    RationalHeight ((scale d c).anchor j l) (A+C) := by
  rw [scale_anchor]
  simpa only [Nat.add_comm] using hc.mul (hd j l)

theorem prepared_height {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (v : RationalFieldSelector m) (S A C : ℕ)
    (hRows : ∀ i j,RationalHeight ((rows.read i).read j) A) (hBudget : RationalHeight ownBudget C)
    (j : Fin m) (l : Fin K) :
    RationalHeight ((GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S).dictionary.anchor j l) (A+C) := by
  rw [GeneralPaperTransferPreparation.prepare_dictionary]
  exact scale_height _ ownBudget⁻¹ A C (divisible_height hT hK hDiv rows A hRows) hBudget.inv j l

theorem fields_cost_height {T m K : ℕ} (d : Dictionary T m K) (v : RationalFieldSelector m) (S A : ℕ)
    (hd : ∀ j l,RationalHeight (d.anchor j l) A) : CostHeight (fields (score v S) d.anchor) A := by
  intro f hf l
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
  simpa only [FixedArrayTable.read_ofFn] using hd j l

theorem score_le {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (j : Fin m) (l : Fin K) :
    score v S j l≤S := by
  have ha := GeneralPaperScoreMatrixWork.argument_bounds v S hK j l
  have hFloor : (score v S j l:ℚ)≤GeneralPaperScoreMatrixWork.argument v S j l := Nat.floor_le ha.1
  have h := hFloor.trans ha.2
  exact_mod_cast h

theorem fields_scores_bound {T m K : ℕ} (d : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) :
    GeneralPaperScoreDPBits.ScoresBound (fields (score v S) d.anchor) S := by
  intro f hf l
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
  simpa only [FixedArrayTable.read_ofFn] using score_le v S hK j l

end Blotto.GeneralPaperQuantizedHeight
