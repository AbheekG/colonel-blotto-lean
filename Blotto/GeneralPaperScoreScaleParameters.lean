import Blotto.GeneralPaperPowerCeiling

/-! Actual K,S and quotient depth from the retained dyadic-accuracy exponent.
Powers are constructed by doubling. S is the least power of two above m*K;
the depth is returned by that computation and satisfies S<2^depth.
-/
namespace Blotto.GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 1500000

def powerRun : ℕ → GeneralPaperPowerCeiling.Result
  | 0 => ⟨1,0,2⟩
  | n+1 =>
      let earlier := powerRun n
      ⟨2*earlier.power,earlier.doublings+1,earlier.work+8⟩

theorem power_data (n : ℕ) : (powerRun n).power=2^n ∧ (powerRun n).doublings=n ∧ (powerRun n).work=8*n+2 := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    change 2*(powerRun n).power=2^(n+1) ∧ (powerRun n).doublings+1=n+1 ∧ (powerRun n).work+8=8*(n+1)+2
    refine ⟨?_,?_,?_⟩
    · rw [ih.1,pow_succ]; omega
    · rw [ih.2.1]
    · rw [ih.2.2]; omega

structure Parameters where
  K : ℕ
  S : ℕ
  depth : ℕ
  work : ℕ

def prepare (m k : ℕ) : Parameters :=
  let labels := powerRun (7+k)
  let scale := GeneralPaperPowerCeiling.ceiling (m*labels.power)
  ⟨labels.power,scale.power,scale.doublings+1,labels.work+scale.work+16⟩

theorem label_power (m k : ℕ) : (prepare m k).K=2^(7+k) := (power_data (7+k)).1

theorem labels_positive (m k : ℕ) : 0<(prepare m k).K := by
  rw [label_power]
  exact Nat.two_pow_pos _

theorem scale_lower (m k : ℕ) : m*(prepare m k).K≤(prepare m k).S :=
  GeneralPaperPowerCeiling.ceiling_lower _

theorem scale_upper (m k : ℕ) (hm : 0<m) : (prepare m k).S<2*(m*(prepare m k).K) :=
  GeneralPaperPowerCeiling.ceiling_upper _ (Nat.mul_pos hm (labels_positive m k))

theorem scale_dyadic (m k : ℕ) : ∃ r,(prepare m k).S=2^r ∧ (prepare m k).depth=r+1 := by
  refine ⟨(GeneralPaperPowerCeiling.ceiling (m*(powerRun (7+k)).power)).doublings,?_,rfl⟩
  exact GeneralPaperPowerCeiling.ceiling_power _

theorem score_cap (m k : ℕ) : (prepare m k).S<2^(prepare m k).depth := by
  obtain ⟨r,hs,hd⟩ := scale_dyadic m k
  rw [hs,hd]
  exact GeneralPaperBoundedQuotient.dyadic_cap r

theorem scale_minimal (m k r : ℕ) (h : m*(prepare m k).K≤2^r) : (prepare m k).depth≤r+1 :=
  Nat.add_le_add_right (GeneralPaperPowerCeiling.ceiling_minimal _ r h) 1

theorem scale_le_of_power (m k r : ℕ) (h : m*(prepare m k).K≤2^r) : (prepare m k).S≤2^r := by
  obtain ⟨a,hs,hd⟩ := scale_dyadic m k
  have hm := scale_minimal m k r h
  rw [hd] at hm
  rw [hs]
  exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)

theorem depth_bound (m k : ℕ) : (prepare m k).depth≤binaryWordWidth (m*(prepare m k).K)+1 :=
  Nat.add_le_add_right (GeneralPaperPowerCeiling.loop_depth _ 1 (by decide)) 1

theorem prepare_work (m k : ℕ) :
    (prepare m k).work≤8*(7+k)+12*binaryWordWidth (m*(prepare m k).K)+20 := by
  have hp := (power_data (7+k)).2.2
  have hc := GeneralPaperPowerCeiling.ceiling_work (m*(powerRun (7+k)).power)
  change (powerRun (7+k)).work+(GeneralPaperPowerCeiling.ceiling (m*(powerRun (7+k)).power)).work+16≤_
  change (powerRun (7+k)).work=8*(7+k)+2 at hp
  change _≤8*(7+k)+12*binaryWordWidth (m*(powerRun (7+k)).power)+20
  omega

theorem labels_accuracy (m k : ℕ) :
    ((prepare m k).K:ℚ)=128/(1/(2:ℚ)^k) := by
  rw [label_power]
  simp only [Nat.cast_pow,Nat.cast_ofNat,pow_add,one_div,div_inv_eq_mul]
  norm_num

theorem dyadic_target (m k : ℕ) :
    ((m*(prepare m k).K:ℕ):ℚ)=128*(m:ℚ)/(1/(2:ℚ)^k) := by
  rw [Nat.cast_mul,labels_accuracy]
  ring

theorem constructed_stage_data {T m : ℕ} (model : RationalCostModel) (W k : ℕ)
    (d : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (budget : ℚ) (v : RationalFieldSelector m) :
    (GeneralPaperScoreStageBits.run model W (prepare m k).depth d budget v (prepare m k).S).1=
      (GeneralPaperComputedThreshold.table d v (prepare m k).S,
        GeneralPaperComputedThreshold.compute d budget v (prepare m k).S) :=
  GeneralPaperScoreStageBits.run_data model W _ d budget v _ (labels_positive m k) (score_cap m k)

theorem constructed_stage_work {T m : ℕ} (model : RationalCostModel) (W k : ℕ)
    (d : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (budget : ℚ) (v : RationalFieldSelector m)
    (V A B : ℕ) (hValues : ∀ j,RationalHeight (v.weight j) V)
    (hAnchors : ∀ j l,RationalHeight (d.anchor j l) A) (hBudget : RationalHeight budget B)
    (hW : 1≤W) (hScore : binaryWordWidth ((prepare m k).S+2)≤W)
    (hLabel : binaryWordWidth ((prepare m k).K+1)≤W) (hField : binaryWordWidth (m+1)≤W) :
    (GeneralPaperScoreStageBits.run model W (prepare m k).depth d budget v (prepare m k).S).2≤
      GeneralPaperScoreStageBits.profile model W (prepare m k).depth m (prepare m k).K (prepare m k).S V A B :=
  GeneralPaperScoreStageBits.run_work model W _ d budget v _ V A B (labels_positive m k) (score_cap m k)
    hValues hAnchors hBudget hW hScore hLabel hField

end Blotto.GeneralPaperScoreScaleParameters
