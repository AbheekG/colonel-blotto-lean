import Blotto.GeneralPaperSharpSourceDPContract

/-! Three separate structural degrees for field count, full-code length and
inverse accuracy. Polynomial logarithms are hidden only after the actual
operand word bounds are proved. Certificates are erased mathematical bounds.
Source phases with different degree tradeoffs are joined as a sum later. -/
namespace Blotto.GeneralPaperSourceRateAlgebra
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperFastRationalModel
set_option autoImplicit false
set_option maxHeartbeats 2000000

def monomial (a b c : ℕ) (x : Input) : ℕ := fields x^a*symbols x^b*accuracy x^c

theorem monomial_positive (a b c : ℕ) (x : Input) : 1≤monomial a b c x := by
  unfold monomial
  have h := Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow a _ (fields_positive x))
    (Nat.one_le_pow b _ (symbols_positive x))) (Nat.one_le_pow c _ (accuracy_positive x))
  simpa only [Nat.one_mul] using h

theorem monomial_mono {a b c a' b' c' : ℕ} (ha : a≤a') (hb : b≤b') (hc : c≤c') (x : Input) :
    monomial a b c x≤monomial a' b' c' x := by
  exact Nat.mul_le_mul (Nat.mul_le_mul
    (Nat.pow_le_pow_right (fields_positive x) ha) (Nat.pow_le_pow_right (symbols_positive x) hb))
    (Nat.pow_le_pow_right (accuracy_positive x) hc)

@[fun_prop]
def Rated (f : Input → ℕ) (a b c : ℕ) : Prop := Soft (monomial a b c) f

theorem poly {f : Input → ℕ} (h : Polylog f) : Rated f 0 0 0 := by
  change Soft (monomial 0 0 0) f
  simpa only [Soft,Polylog,monomial,pow_zero,Nat.one_mul] using h

theorem weaken {f : Input → ℕ} {a b c a' b' c' : ℕ} (hf : Rated f a b c)
    (ha : a≤a') (hb : b≤b') (hc : c≤c') : Rated f a' b' c' :=
  rate_mono hf (monomial_mono ha hb hc)

@[fun_prop]
theorem constant (n : ℕ) : Rated (fun _ => n) 0 0 0 := poly (poly_constant n)

@[fun_prop]
theorem add (f g : Input → ℕ) (a b c a' b' c' : ℕ) (hf : Rated f a b c) (hg : Rated g a' b' c') :
    Rated (fun x => f x+g x) (max a a') (max b b') (max c c') :=
  add_same (weaken hf (le_max_left ..) (le_max_left ..) (le_max_left ..))
    (weaken hg (le_max_right ..) (le_max_right ..) (le_max_right ..))

@[fun_prop]
theorem mul (f g : Input → ℕ) (a b c a' b' c' : ℕ) (hf : Rated f a b c) (hg : Rated g a' b' c') :
    Rated (fun x => f x*g x) (a+a') (b+b') (c+c') := by
  have h := GeneralPaperSourceSoftBounds.mul hf hg
  apply rate_mono h
  intro x
  dsimp only [monomial]
  rw [pow_add,pow_add,pow_add]
  exact le_of_eq (by ring)

@[fun_prop]
theorem sub (f g : Input → ℕ) (a b c : ℕ) (hf : Rated f a b c) : Rated (fun x => f x-g x) a b c :=
  dominated hf (fun _x => Nat.sub_le _ _)

@[fun_prop]
theorem maximum (f g : Input → ℕ) (a b c a' b' c' : ℕ) (hf : Rated f a b c) (hg : Rated g a' b' c') :
    Rated (fun x => max (f x) (g x)) (max a a') (max b b') (max c c') :=
  dominated (add f g a b c a' b' c' hf hg) (fun x => by omega)

@[fun_prop]
theorem minimum (f g : Input → ℕ) (a b c : ℕ) (hf : Rated f a b c) : Rated (fun x => min (f x) (g x)) a b c :=
  dominated hf (fun _x => Nat.min_le_left ..)

@[fun_prop]
theorem power (f : Input → ℕ) (n a b c : ℕ) (hf : Rated f a b c) :
    Rated (fun x => (f x)^n) (a*n) (b*n) (c*n) := by
  induction n with
  | zero => simpa only [pow_zero,Nat.mul_zero] using constant 1
  | succ n ih =>
    simpa only [Nat.mul_succ,pow_succ] using mul _ _ _ _ _ _ _ _ ih hf

theorem word (f : Input → ℕ) (hf : Small f) : Rated (fun x => binaryWordWidth (f x)) 0 0 0 :=
  poly (poly_word f hf)

@[fun_prop]
theorem constant_word (n : ℕ) : Rated (fun _ => binaryWordWidth n) 0 0 0 := word _ (small_constant n)

@[fun_prop]
theorem m_word : Rated (fun x => binaryWordWidth x.m) 0 0 0 := word _ m_small

@[fun_prop]
theorem lambda_word : Rated (fun x => binaryWordWidth (alphabet x).lambda) 0 0 0 := word _ lambda_small

@[fun_prop]
theorem Qv_word : Rated (fun x => binaryWordWidth x.Qv) 0 0 0 := word _ Qv_small

@[fun_prop]
theorem k_word : Rated (fun x => binaryWordWidth x.k) 0 0 0 := word _ k_small

@[fun_prop]
theorem summary_word : Rated (fun x => binaryWordWidth (GeneralPaperSourceParameters.prepare x.k).summarySize) 0 0 0 :=
  word _ GeneralPaperNativeSourceWordGrowth.summary_small

@[fun_prop]
theorem grid_word : Rated (fun x => binaryWordWidth (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.size) 0 0 0 :=
  word _ GeneralPaperNativeSourceWordGrowth.grid_size_small

@[fun_prop]
theorem leaves_word : Rated (fun x => binaryWordWidth (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).leafCount) 0 0 0 :=
  word _ GeneralPaperNativeSourceWordGrowth.profit_leaves_small

@[fun_prop]
theorem height_word : Rated (fun x => binaryWordWidth (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height) 0 0 0 :=
  word _ GeneralPaperNativeSourceWordGrowth.profit_height_small

@[fun_prop]
theorem rows_word : Rated (fun x => binaryWordWidth (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows) 0 0 0 :=
  word _ GeneralPaperNativeSourceWordGrowth.rows_small

@[fun_prop]
theorem epochs_word : Rated (fun x => binaryWordWidth (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) 0 0 0 :=
  word _ GeneralPaperNativeSourceWordGrowth.epochs_small

@[fun_prop]
theorem word_mul (f g : Input → ℕ) (a b c a' b' c' : ℕ)
    (hf : Rated (fun x => binaryWordWidth (f x)) a b c)
    (hg : Rated (fun x => binaryWordWidth (g x)) a' b' c') :
    Rated (fun x => binaryWordWidth (f x*g x)) (max a a') (max b b') (max c c') :=
  dominated (add _ _ a b c a' b' c' hf hg) (fun _x => binaryWordWidth_mul _ _)

@[fun_prop]
theorem word_add (f g : Input → ℕ) (a b c a' b' c' : ℕ)
    (hf : Rated (fun x => binaryWordWidth (f x)) a b c)
    (hg : Rated (fun x => binaryWordWidth (g x)) a' b' c') :
    Rated (fun x => binaryWordWidth (f x+g x)) (max a a') (max b b') (max c c') :=
  dominated (add _ _ a b c a' b' c' hf hg) (fun _x => GeneralPaperReferenceScaling.word_add _ _)

@[fun_prop]
theorem word_maximum (f g : Input → ℕ) (a b c a' b' c' : ℕ)
    (hf : Rated (fun x => binaryWordWidth (f x)) a b c)
    (hg : Rated (fun x => binaryWordWidth (g x)) a' b' c') :
    Rated (fun x => binaryWordWidth (max (f x) (g x))) (max a a') (max b b') (max c c') := by
  apply dominated (add _ _ a b c a' b' c' hf hg)
  intro x
  exact (binaryWordWidth_mono (show max (f x) (g x)≤f x+g x by omega)).trans
    (GeneralPaperReferenceScaling.word_add _ _)

@[fun_prop]
theorem charge (C d : ℕ) (f : Input → ℕ) (a b c : ℕ) (hf : Rated f a b c) (hw : Small f) :
    Rated (fun x => GeneralPaperFastRationalModel.charge C d (f x)) a b c :=
  charge_preserves C d hf hw

@[fun_prop]
theorem m : Rated Input.m 1 0 0 := by
  change Soft (monomial 1 0 0) Input.m
  simpa only [Soft,monomial,pow_zero,pow_one,Nat.mul_one] using
    (bounded 1 (fun x : Input => by dsimp only [fields]; omega) : Soft fields Input.m)

@[fun_prop]
theorem lambda : Rated (fun x => (alphabet x).lambda) 0 1 0 := by
  change Soft (monomial 0 1 0) _
  simpa only [Soft,monomial,pow_zero,pow_one,Nat.one_mul,Nat.mul_one] using
    (bounded 1 (fun x : Input => by dsimp only [symbols]; omega) : Soft symbols (fun x => (alphabet x).lambda))

@[fun_prop]
theorem k : Rated Input.k 0 0 0 := poly (poly_tight _ k_tight)

@[fun_prop]
theorem measure : Rated (fun x => GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv) 0 0 0 :=
  poly (poly_tight _ measure_tight)

@[fun_prop]
theorem short : Rated (fun x => GeneralPaperPowerPreparationEnvelope.operandWidth x.m (alphabet x).lambda x.k x.Qv) 0 0 0 :=
  poly short_poly

@[fun_prop]
theorem scale_word : Rated (fun x => binaryWordWidth (alphabet x).C) 0 1 0 := by
  apply bounded 1
  intro x
  simpa only [monomial,pow_zero,pow_one,Nat.one_mul,Nat.mul_one,symbols] using
    GeneralPaperSourceAlphabetLower.scale_width (alphabet x)

@[fun_prop]
theorem profit_height : Rated (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height) 0 0 0 :=
  poly (poly_tight _ GeneralPaperNativeSourceWordGrowth.profit_height_tight)

@[fun_prop]
theorem profit_leaves : Rated (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).leafCount) 1 0 0 := by
  apply bounded 2
  intro x
  have h := GeneralPaperFastOrderedDPPrice.leaves_bound x.m (alphabet x).lambda x.k x.Qv
  rw [←GeneralPaperProfitParameters.leaf_count_spec] at h
  simp only [monomial,pow_zero,pow_one,Nat.mul_one,fields]
  omega

@[fun_prop]
theorem profit_power_leaves : Rated (fun x => 2^(GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height) 1 0 0 := by
  apply bounded 2
  intro x
  have h := GeneralPaperFastOrderedDPPrice.leaves_bound x.m (alphabet x).lambda x.k x.Qv
  simp only [monomial,pow_zero,pow_one,Nat.mul_one,fields]
  omega

@[fun_prop]
theorem dyadic_accuracy (n : ℕ) : Rated (fun x => 2^(n+x.k)) 0 0 1 := by
  apply bounded (2^n)
  intro x
  simp only [monomial,pow_zero,pow_one,Nat.one_mul,accuracy,pow_add,le_refl]

@[fun_prop]
theorem summary : Rated (fun x => (GeneralPaperSourceParameters.prepare x.k).summarySize) 0 0 1 := by
  have h := dyadic_accuracy 34
  simpa only [(GeneralPaperSourceParameters.data _).2.2.2.2.2] using h

@[fun_prop]
theorem grid_size : Rated grid 0 0 1 := by
  simpa only [Rated,Soft,monomial,pow_zero,pow_one,Nat.one_mul] using grid_rate

@[fun_prop]
theorem grid_depth : Rated (fun x => (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.depth) 0 0 0 :=
  poly depth_poly

@[fun_prop]
theorem actual_grid : Rated (fun x => (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.size) 0 0 1 :=
  grid_size

@[fun_prop]
theorem period : Rated (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) 0 0 1 := by
  simp only [GeneralPaperTrajectoryParameters.period_power]
  exact dyadic_accuracy 11

@[fun_prop]
theorem dp (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Rated (fun x => GeneralPaperFastOrderedDPPrice.fieldProfile C d (W x) x.m (alphabet x).lambda x.k x.Qv
      (options x) (grid x) (symbols x)) 1 1 2 := by
  simpa only [Rated,Soft,monomial,GeneralPaperSharpDPSourceRate.callRate,
    GeneralPaperSharpDPSourceRate.resourceRate,pow_one] using
    GeneralPaperSharpDPSourceRate.field_profile_rate C d W hW

structure Certificate (f : Input → ℕ) where
  fields : ℕ
  symbols : ℕ
  accuracy : ℕ
  bound : Rated f fields symbols accuracy

def batchCertificate : Certificate (fun x => 6*(GeneralPaperSourceParameters.prepare x.k).summarySize+6) := by
  refine ⟨_,_,_,by fun_prop⟩

theorem batch_degrees : (batchCertificate.fields,batchCertificate.symbols,batchCertificate.accuracy)=(0,0,1) := rfl

end Blotto.GeneralPaperSourceRateAlgebra
