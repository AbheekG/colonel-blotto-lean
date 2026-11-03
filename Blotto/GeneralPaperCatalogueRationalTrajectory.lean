import Blotto.GeneralPaperCataloguePairedSecurity

/-! Decode the already-returned source table into rational whole rows.
Its uniform rational law equals the law used in the continuous-security
proof exactly. No coordinate resampling or source replay is performed by
this decoder. Prices for decoding/materialization remain separate.
-/
namespace Blotto.GeneralPaperCatalogueRationalTrajectory
open GeneralPaperCodeAlphabet GeneralPaperCatalogueCanonicalGap
open GeneralPaperCatalogueChosenMixture GeneralPaperCodeMixturePhysical
set_option autoImplicit false
set_option maxHeartbeats 3500000

def decodeValue (m qbar : ℕ) (a : Alphabet) (code : ℕ) : ℚ :=
  match (GeneralPaperCodeDecode.decode a false code).choice with
  | none => 0
  | some choice => choice.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C)

def rows {m : ℕ} (a : Alphabet) (k Qv qbar : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    FixedArrayTable (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows (FixedArrayTable m ℚ) :=
  let codes := GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br
  FixedArrayTable.ofFn (fun t => FixedArrayTable.ofFn (fun j => decodeValue m qbar a ((codes.read t).read j)))

theorem rows_read {m : ℕ} (a : Alphabet) (k Qv qbar : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (t : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m) :
    ((rows a k Qv qbar weights Bc Br).read t).read j=
      ((choices false a k Qv weights Bc Br t.val).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C) := by
  have hd := chosen_decoded false a k Qv weights Bc Br t.val j
  have ht := candidate_table_code a k Qv weights Bc Br t j
  change (GeneralPaperCodeDecode.decode a false ((empirical false a k Qv weights Bc Br).rows t j).val).choice=_ at hd
  rw [ht] at hd
  simp only [rows,FixedArrayTable.read_ofFn,decodeValue,hd]

def uniformLaw {m : ℕ} (a : Alphabet) (k Qv qbar : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    RationalWholeRowLaw (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m :=
  GeneralPaperDictionary.law (GeneralPaperRowQuantizer.original (rows a k Qv qbar weights Bc Br))
    (GeneralPaperTrajectoryParameters.rows_positive a.lambda k)

theorem realRow_eq {m : ℕ} (a : Alphabet) (k Qv qbar : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (hB : 0≤Bc)
    (t : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    (uniformLaw a k Qv qbar weights Bc Br).realRow t=
      allocation (feasible_empirical false a k Qv hm hQv weights hWeights Bc Br hB) qbar t := by
  funext j
  change (((rows a k Qv qbar weights Bc Br).read t).read j:ℝ)=_
  rw [rows_read]
  rfl

theorem law_eq {m : ℕ} (a : Alphabet) (k Qv qbar : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (hB : 0≤Bc) :
    (uniformLaw a k Qv qbar weights Bc Br).law=
      strategy false a k Qv hm hQv weights hWeights Bc Br hB qbar := by
  have hRow := realRow_eq a k Qv qbar hm hQv weights hWeights Bc Br hB
  unfold RationalWholeRowLaw.law strategy physicalLaw
  have hw : (uniformLaw a k Qv qbar weights Bc Br).realWeight=
      (feasible_empirical false a k Qv hm hQv weights hWeights Bc Br hB).law.weight := by
    funext t
    simp only [uniformLaw,GeneralPaperDictionary.law,RationalWholeRowLaw.realWeight,
      Rat.cast_div,Rat.cast_one,Rat.cast_natCast,feasible_empirical,empirical]
  have hl : (fun t => ProductBidTree.allocationPointLaw ((uniformLaw a k Qv qbar weights Bc Br).realRow t))=
      (fun t => PureBoundaryEquilibria.pointLaw
        (allocation (feasible_empirical false a k Qv hm hQv weights hWeights Bc Br hB) qbar t)) := by
    funext t
    rw [hRow]
    rfl
  apply Subtype.ext
  change mixtureMeasure _ _=mixtureMeasure _ _
  rw [hw,hl]
  rfl

theorem every_row_feasible {m : ℕ} (a : Alphabet) (k Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (hB : 0≤Bc)
    (hq : 0<q) (hCap : q≤qbar) (hDen : Bc.den∣q)
    (t : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    Blotto.Feasible (Bc:ℝ) (fun j => (((rows a k Qv qbar weights Bc Br).read t).read j:ℝ)) := by
  have hf := allocation_feasible a false Bc (feasible_empirical false a k Qv hm hQv weights hWeights Bc Br hB)
    q qbar hm hq hCap hDen t
  rw [← realRow_eq a k Qv qbar hm hQv weights hWeights Bc Br hB] at hf
  exact hf

theorem quantizer_correct {m : ℕ} (a : Alphabet) (k Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (hB : 0≤Bc)
    (hq : 0<q) (hCap : q≤qbar) (hDen : Bc.den∣q) :
    GeneralPaperRowQuantizer.Correct (rows a k Qv qbar weights Bc Br)
      (GeneralPaperRowQuantizer.buildDivisible (GeneralPaperTrajectoryParameters.rows_positive a.lambda k)
        (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m a.lambda k)
        (rows a k Qv qbar weights Bc Br))
      (GeneralPaperTrajectoryParameters.rows_positive a.lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k) (Bc:ℝ) :=
  GeneralPaperTrajectoryParameters.quantizer_correct a.lambda k (rows a k Qv qbar weights Bc Br) (Bc:ℝ)
    (every_row_feasible a k Qv q qbar hm hQv weights hWeights Bc Br hB hq hCap hDen)

end Blotto.GeneralPaperCatalogueRationalTrajectory
