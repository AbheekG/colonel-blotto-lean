import Blotto.BinaryNestedComponents
import Blotto.RationalNestedProfile

/-! Actual ordered interior nested profiles compile all three t-regimes into
stored 18-slot Boolean tables. Native guards include equality boundaries and
zero coefficients; every table refines the original rational source profile. -/

namespace Blotto.BinaryNestedProfileCompiler
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment
open BinaryNestedParameters BinaryNestedComponents

def parameters (input : Input) : FixedArrayTable 9 SignedWord := prepare input BinaryRationalOpcode.zero

theorem parameters_canonical (input : Input) (h : input.Canonical) : ∀ j, CanonicalWord ((parameters input).read j) :=
  prepare_canonical input _ h ⟨BinaryRationalOpcode.zero_valid,by decide⟩

theorem parameters_value (input : Input) (source : RationalNestedInput) (h : input.Canonical) (hr : input.Refines source) (j : Fin 9) :
    value ((parameters input).read j) = values source 0 j := by
  have he := prepare_value input _ source h ⟨BinaryRationalOpcode.zero_valid,by decide⟩ hr j
  simpa only [parameters,BinaryRationalOpcode.zero_value] using he

theorem compare_iff (first second : SignedWord) (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) :
    BinaryRationalArithmetic.lessEqual first second = true ↔ value first ≤ value second :=
  BinaryRationalArithmetic.lessEqual_iff first second hFirst.1 hSecond.1

theorem positive_iff (word : SignedWord) (h : CanonicalWord word) :
    (!BinaryRationalArithmetic.lessEqual word BinaryRationalOpcode.zero) = true ↔ 0 < value word := by
  rw [Bool.not_eq_true',Bool.eq_false_iff]
  have he := compare_iff word BinaryRationalOpcode.zero h ⟨BinaryRationalOpcode.zero_valid,by decide⟩
  rw [BinaryRationalOpcode.zero_value] at he
  exact (not_congr he).trans not_le

theorem strict_iff (first second : SignedWord) (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) :
    (!BinaryRationalArithmetic.lessEqual second first) = true ↔ value first < value second := by
  rw [Bool.not_eq_true',Bool.eq_false_iff]
  exact (not_congr (compare_iff second first hSecond hFirst)).trans not_le

def secondProfile (input : Input) (K : ℕ) (bits : Fin K → Bool) : Segment 3 18 :=
  let p := parameters input
  let family := familyLottery input (p.read 6) K bits
  if !BinaryRationalArithmetic.lessEqual input.t (p.read 6) then
    BinarySegmentAssembly.binary (p.read 7) family (secondUniformLottery input)
  else BinarySegmentAssembly.padRight family 9 0

def thirdProfile (input : Input) (K : ℕ) (bits : Fin K → Bool) : Segment 3 18 :=
  let p := parameters input
  let residual := BinarySegmentAssembly.padRight (residualLottery input) 6 0
  if !BinaryRationalArithmetic.lessEqual (p.read 2) BinaryRationalOpcode.zero then
    BinarySegmentAssembly.binary (p.read 8) (familyLottery input (p.read 2) K bits) residual
  else BinarySegmentAssembly.padRight residual 9 0

def profile (input : Input) (K : ℕ) (bits : Fin K → Bool) : Segment 3 18 :=
  let p := parameters input
  if BinaryRationalArithmetic.lessEqual input.t (p.read 2) then
    BinarySegmentAssembly.padRight (BinaryNestedFirstConditional.firstProfile input K bits) 9 0
  else if BinaryRationalArithmetic.lessEqual (p.read 1) input.t then secondProfile input K bits
  else thirdProfile input K bits

theorem secondProfile_canonical (input : Input) (h : input.Canonical) (K : ℕ) (bits : Fin K → Bool) :
    (secondProfile input K bits).Canonical := by
  have hp := parameters_canonical input h
  have hf := familyLottery_canonical input _ h (hp 6) K bits
  unfold secondProfile
  dsimp only
  split
  · exact BinarySegmentAssembly.binary_canonical _ _ _ (hp 7) hf (secondUniformLottery_canonical input h)
  · exact BinarySegmentAssembly.padRight_canonical _ 9 0 hf

theorem thirdProfile_canonical (input : Input) (h : input.Canonical) (K : ℕ) (bits : Fin K → Bool) :
    (thirdProfile input K bits).Canonical := by
  have hp := parameters_canonical input h
  have hr := BinarySegmentAssembly.padRight_canonical _ 6 0 (residualLottery_canonical input h)
  unfold thirdProfile
  dsimp only
  split
  · exact BinarySegmentAssembly.binary_canonical _ _ _ (hp 8) (familyLottery_canonical input _ h (hp 2) K bits) hr
  · exact BinarySegmentAssembly.padRight_canonical _ 9 0 hr

theorem profile_canonical (input : Input) (h : input.Canonical) (K : ℕ) (bits : Fin K → Bool) :
    (profile input K bits).Canonical := by
  unfold profile
  dsimp only
  split
  · exact BinarySegmentAssembly.padRight_canonical _ 9 0 (BinaryNestedFirstConditional.firstProfile_canonical input h K bits)
  · split
    · exact secondProfile_canonical input h K bits
    · exact thirdProfile_canonical input h K bits

theorem secondProfile_refines (input : Input) (source : RationalNestedInput) (h : input.Canonical) (hr : input.Refines source)
    (htu : source.u ≤ source.t) (K : ℕ) (bits : Fin K → Bool) :
    (secondProfile input K bits).Refines (source.secondProfile htu K bits) := by
  have hp := parameters_canonical input h
  have hv := parameters_value input source h hr
  have hMirror : value ((parameters input).read 6) = source.mirrorLength := hv 6
  have hAlpha : value ((parameters input).read 7) = source.secondAlpha := hv 7
  have hGuard := strict_iff ((parameters input).read 6) input.t (hp 6) h.2.2.2.2.1
  rw [hMirror,hr.2.2.2.2.1] at hGuard
  have hf := familyLottery_refines input _ source h (hp 6) hr _ hMirror (source.mirrorLength_bounds htu).1
    (source.mirrorLength_bounds htu).2.1 K bits
  unfold secondProfile RationalNestedInput.secondProfile
  dsimp only
  by_cases hTt : source.mirrorLength < source.t
  · rw [ite_eq_left (hGuard.mpr hTt),dite_eq_left hTt]
    exact BinarySegmentAssembly.binary_refines _ _ _ (hp 7) (familyLottery_canonical input _ h (hp 6) K bits)
      (secondUniformLottery_canonical input h) _ _ hf (secondUniformLottery_refines input source h hr htu hTt) _ hAlpha
        ⟨(source.secondAlpha_bounds htu).1.le,(source.secondAlpha_bounds htu).2⟩
  · rw [ite_eq_right (fun hg => hTt (hGuard.mp hg)),dite_eq_right hTt]
    exact BinarySegmentAssembly.padRight_refines _ _ hf 9 0

theorem thirdProfile_refines (input : Input) (source : RationalNestedInput) (h : input.Canonical) (hr : input.Refines source)
    (hvt : source.v < source.t) (htu : source.t < source.u) (K : ℕ) (bits : Fin K → Bool) :
    (thirdProfile input K bits).Refines (source.thirdProfile hvt htu K bits) := by
  have hp := parameters_canonical input h
  have hv := parameters_value input source h hr
  have hV : value ((parameters input).read 2) = source.v := hv 2
  have hAlpha : value ((parameters input).read 8) = source.thirdAlpha := hv 8
  have hGuard := positive_iff ((parameters input).read 2) (hp 2)
  rw [hV] at hGuard
  have hResidual := BinarySegmentAssembly.padRight_refines _ _ (residualLottery_refines input source h hr hvt htu) 6 0
  have hResidualC := BinarySegmentAssembly.padRight_canonical _ 6 0 (residualLottery_canonical input h)
  unfold thirdProfile RationalNestedInput.thirdProfile
  dsimp only
  by_cases hpos : 0 < source.v
  · rw [ite_eq_left (hGuard.mpr hpos),dite_eq_left hpos]
    exact BinarySegmentAssembly.binary_refines _ _ _ (hp 8) (familyLottery_canonical input _ h (hp 2) K bits) hResidualC _ _
      (familyLottery_refines input _ source h (hp 2) hr source.v hV hpos le_rfl K bits) hResidual _ hAlpha
        ⟨(source.thirdAlpha_bounds hpos hvt).1.le,(source.thirdAlpha_bounds hpos hvt).2.le⟩
  · rw [ite_eq_right (fun hg => hpos (hGuard.mp hg)),dite_eq_right hpos]
    exact BinarySegmentAssembly.padRight_refines _ _ hResidual 9 0

theorem profile_refines (input : Input) (source : RationalNestedInput) (h : input.Canonical) (hr : input.Refines source)
    (K : ℕ) (bits : Fin K → Bool) : (profile input K bits).Refines (source.profile K bits) := by
  have hp := parameters_canonical input h
  have hv := parameters_value input source h hr
  have hV : value ((parameters input).read 2) = source.v := hv 2
  have hU : value ((parameters input).read 1) = source.u := hv 1
  have hFirst := compare_iff input.t ((parameters input).read 2) h.2.2.2.2.1 (hp 2)
  rw [hr.2.2.2.2.1,hV] at hFirst
  have hSecond := compare_iff ((parameters input).read 1) input.t (hp 1) h.2.2.2.2.1
  rw [hU,hr.2.2.2.2.1] at hSecond
  unfold profile RationalNestedInput.profile
  dsimp only
  by_cases htv : source.t ≤ source.v
  · rw [ite_eq_left (hFirst.mpr htv),dite_eq_left htv]
    exact BinarySegmentAssembly.padRight_refines _ _ (BinaryNestedFirstConditional.firstProfile_refines input source h hr htv K bits) 9 0
  · rw [ite_eq_right (fun hg => htv (hFirst.mp hg)),dite_eq_right htv]
    by_cases htu : source.u ≤ source.t
    · rw [ite_eq_left (hSecond.mpr htu),dite_eq_left htu]
      exact secondProfile_refines input source h hr htu K bits
    · rw [ite_eq_right (fun hg => htu (hSecond.mp hg)),dite_eq_right htu]
      exact thirdProfile_refines input source h hr (lt_of_not_ge htv) (lt_of_not_ge htu) K bits

end Blotto.BinaryNestedProfileCompiler
