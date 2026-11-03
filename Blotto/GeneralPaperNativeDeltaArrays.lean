import Blotto.GeneralPaperSignedCellConstancy

/-! Fill native delta arrays using the prepared query plans. Preparation
is an explicit input, reused across rounds; these loops do not reconstruct
ranks. They apply equally to cell representatives and repeated occurrences.
-/
namespace Blotto.GeneralPaperNativeDeltaArrays
open scoped BigOperators
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def unsigned {m : ℕ} (k : ℕ) (response : Bool) (cdfPrefix signedPrefix : Prefix k)
    (plan : GeneralPaperQueryLossCounts.Plan k m) : FixedArrayTable m ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (GeneralPaperQueryLossCounts.step k response cdfPrefix signedPrefix plan)

theorem unsigned_read {m : ℕ} (k U : ℕ) (response : Bool) (cdfSummary signedSummary : Summary k)
    (cdfPrefix signedPrefix : Prefix k) (codes : FixedArrayTable m ℕ) (r : Fin m) :
    (unsigned k response cdfPrefix signedPrefix (GeneralPaperQueryLossCounts.prepare k U cdfSummary signedSummary codes)).1.read r=
    GeneralPaperQueryLossCounts.increment k response
      (GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary cdfPrefix signedPrefix (codes.read r)) := by
  rw [unsigned,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperNativeLossReference.evaluate_increment k U response cdfSummary signedSummary cdfPrefix signedPrefix codes r

theorem unsigned_bound {m : ℕ} (k U : ℕ) (response : Bool) (cdfSummary signedSummary cdfValues signedValues : Summary k)
    (hCDF : 0<∑ r, cdfValues.read r) (hSigned : 0<∑ r, signedValues.read r) (codes : FixedArrayTable m ℕ) (r : Fin m) :
    (unsigned k response (GeneralPaperEpochPrefixArray.build cdfValues) (GeneralPaperEpochPrefixArray.build signedValues)
      (GeneralPaperQueryLossCounts.prepare k U cdfSummary signedSummary codes)).1.read r≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  rw [unsigned_read]
  exact GeneralPaperQueryLossCounts.increment_bound k response _
    (GeneralPaperNativeLossReference.reference_bounds k U cdfSummary signedSummary cdfValues signedValues hCDF hSigned _)

theorem unsigned_work {m : ℕ} (k : ℕ) (response : Bool) (cdfPrefix signedPrefix : Prefix k)
    (plan : GeneralPaperQueryLossCounts.Plan k m) :
    (unsigned k response cdfPrefix signedPrefix plan).2=m*(48*(30+k)+298)+18 := by
  rw [unsigned,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [GeneralPaperQueryLossCounts.step_work,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

def signed {m : ℕ} (k U bid : ℕ) (preparedPrefix : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k m) :
    FixedArrayTable m ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun r =>
    let result := GeneralPaperSignedUpdatePlan.evaluate k U bid preparedPrefix plan r
    (result.increment,result.work))

theorem signed_read {m : ℕ} (k U bid : ℕ) (summary : Summary k) (preparedPrefix : Prefix k)
    (codes : FixedArrayTable m ℕ) (r : Fin m) :
    (signed k U bid preparedPrefix (GeneralPaperSignedUpdatePlan.prepare k U summary codes)).1.read r=
      GeneralPaperSignedUpdateReference.increment k U bid summary preparedPrefix (codes.read r) := by
  rw [signed,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperSignedUpdateReference.evaluate_increment k U bid summary preparedPrefix codes r

theorem signed_bound {m : ℕ} (k U bid : ℕ) (summary values : Summary k) (hTotal : 0<∑ r, values.read r)
    (codes : FixedArrayTable m ℕ) (r : Fin m) :
    (signed k U bid (GeneralPaperEpochPrefixArray.build values) (GeneralPaperSignedUpdatePlan.prepare k U summary codes)).1.read r≤
      8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  rw [signed,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperSignedUpdatePlan.evaluate_bounds k U bid summary values hTotal codes r

theorem signed_work {m : ℕ} (k U bid : ℕ) (preparedPrefix : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k m) :
    (signed k U bid preparedPrefix plan).2=m*(12*(30+k)+108)+18 := by
  rw [signed,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [GeneralPaperSignedUpdatePlan.evaluate_work,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

end Blotto.GeneralPaperNativeDeltaArrays
