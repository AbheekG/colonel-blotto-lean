import Blotto.GeneralPaperSourcePairCanonical

/-! The ACTUAL dyadic K,S,z leave the paper reduced-game error margin,
including both value-approximation errors. No source or transfer error
budget is supplied as an oracle.
-/
namespace Blotto.GeneralPaperReducedErrorBudget
set_option autoImplicit false
set_option maxHeartbeats 3500000

def accuracy (k : ℕ) : ℚ := 1/(2:ℚ)^k

theorem accuracy_positive (k : ℕ) : 0<accuracy k := by unfold accuracy; positivity

theorem source_z (k : ℕ) : (GeneralPaperSourceParameters.prepare k).z=accuracy k/2048 := by
  rw [(GeneralPaperSourceParameters.data k).1]
  unfold accuracy
  rw [pow_add]
  norm_num
  ring

theorem labels_reciprocal (m k : ℕ) :
    (1:ℚ)/(GeneralPaperProxyParameters.prepare m k).K=accuracy k/128 := by
  rw [(GeneralPaperProxyParameters.data m k).1,GeneralPaperScoreScaleParameters.labels_accuracy]
  unfold accuracy
  field_simp

theorem score_error (m k : ℕ) (hm : 0<m) :
    (m:ℚ)/(GeneralPaperProxyParameters.prepare m k).S≤(1:ℚ)/(GeneralPaperProxyParameters.prepare m k).K := by
  have hs : (0:ℚ)<(GeneralPaperProxyParameters.prepare m k).S := by
    exact_mod_cast GeneralPaperSourceModifiedDictionary.scale_positive m k hm
  have hk : (0:ℚ)<(GeneralPaperProxyParameters.prepare m k).K := by
    exact_mod_cast GeneralPaperScoreScaleParameters.labels_positive m k
  apply (div_le_div_iff₀ hs hk).mpr
  have hh : (m:ℚ)*((GeneralPaperProxyParameters.prepare m k).K:ℚ)≤((GeneralPaperProxyParameters.prepare m k).S:ℚ) := by
    exact_mod_cast GeneralPaperScoreScaleParameters.scale_lower m k
  simpa only [one_mul] using hh

theorem gap_with_values_lt (m k : ℕ) (hm : 0<m) :
    3*(GeneralPaperSourceParameters.prepare k).z/32+
      2/((GeneralPaperProxyParameters.prepare m k).K:ℚ)+(m:ℚ)/(GeneralPaperProxyParameters.prepare m k).S+
        2*(accuracy k/256)<accuracy k/16 := by
  have hs := score_error m k hm
  rw [labels_reciprocal] at hs
  have ha := accuracy_positive k
  rw [source_z,show (2:ℚ)/((GeneralPaperProxyParameters.prepare m k).K:ℚ)=
    2*((1:ℚ)/(GeneralPaperProxyParameters.prepare m k).K) by ring,labels_reciprocal]
  nlinarith only [hs,ha]

theorem gap_lt (m k : ℕ) (hm : 0<m) :
    3*(GeneralPaperSourceParameters.prepare k).z/32+
      2/((GeneralPaperProxyParameters.prepare m k).K:ℚ)+(m:ℚ)/(GeneralPaperProxyParameters.prepare m k).S<accuracy k/16 := by
  have hh := gap_with_values_lt m k hm
  have ha := accuracy_positive k
  linarith only [hh,ha]

theorem real_gap (m k : ℕ) (hm : 0<m) :
    3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+
      2/((GeneralPaperProxyParameters.prepare m k).K:ℝ)+(m:ℝ)/(GeneralPaperProxyParameters.prepare m k).S<(accuracy k:ℝ)/16 := by
  have hh := gap_lt m k hm
  have hr : (((3*(GeneralPaperSourceParameters.prepare k).z/32+
      2/((GeneralPaperProxyParameters.prepare m k).K:ℚ)+(m:ℚ)/(GeneralPaperProxyParameters.prepare m k).S):ℚ):ℝ)<
      (((accuracy k/16):ℚ):ℝ) := by exact_mod_cast hh
  simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using hr

end Blotto.GeneralPaperReducedErrorBudget
