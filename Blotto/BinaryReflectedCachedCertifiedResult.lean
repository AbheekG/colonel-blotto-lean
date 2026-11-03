import Blotto.BinaryReflectedCachedResourceWork

/-! Cached resource certificates change only their erased capacity index when
handed to original reached-state interfaces. The complete certified result,
none, reader position and all charges are preserved. No resource/system array
is rebuilt by this index transport. -/

namespace Blotto.BinaryReflectedCachedCertifiedResult
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup BinaryReflectedSetupCache
open BinaryThreeResourcePair BinarySharedResourceRun BinaryGeneralResourceExecution

theorem capacity_original {input : BinaryFourParameters.Input} (prepared : Prepared input) :
    prepared.capacity = (prepare input).capacity := prepared.capacity_correct.trans (congrArg System.capacity prepared.system_correct)

def toOriginal {input : BinaryFourParameters.Input} (prepared : Prepared input) (result : Certified prepared.capacity) :
    Certified (prepare input).capacity := capacity_original prepared ▸ result

theorem toOriginal_state {input : BinaryFourParameters.Input} (prepared : Prepared input) (result : Certified prepared.capacity) :
    (toOriginal prepared result).state = result.state := by
  cases prepared with
  | mk parameters hp hpc system hs hsc capacity hc hcc work =>
      cases hs
      cases hc
      rfl

def runWithCharge {input : BinaryFourParameters.Input} (prepared : Prepared input) (N : ℕ) (bits : Fin N → Bool) :
    (Option (Certified (prepare input).capacity) × ℕ) × Charge :=
  let result := BinaryReflectedCachedResourceWork.Prepared.runWithCharge prepared N bits
  ((result.1.1.map (toOriginal prepared),result.1.2),result.2)

theorem runWithCharge_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (prepared : Prepared input)
    (N : ℕ) (bits : Fin N → Bool) : (runWithCharge prepared N bits).1 = setupRun input hC N bits := by
  cases prepared with
  | mk parameters hp hpc system hs hsc capacity hc hcc work =>
      cases hs
      cases hc
      unfold runWithCharge toOriginal BinaryReflectedCachedResourceWork.Prepared.runWithCharge
        BinaryReflectedCachedResourceWork.Prepared.initialWithCharge
      dsimp only
      rw [BinaryReflectedResourceWork.initialWithCharge_state,BinaryThreeResourceRunWork.runIndexed_state]
      change ((setupRun input hC N bits).1.map id,(setupRun input hC N bits).2) = setupRun input hC N bits
      simp only [Option.map_id]
      rfl

theorem runWithCharge_charge (input : BinaryFourParameters.Input) (hC : input.Canonical) (prepared : Prepared input)
    (N : ℕ) (bits : Fin N → Bool) : (runWithCharge prepared N bits).2 = (BinaryReflectedResourceWork.runWithCharge input hC N bits).2 :=
  BinaryReflectedCachedResourceWork.runWithCharge_charge input hC prepared N bits

theorem runWithCharge_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (prepared : Prepared input) (N : ℕ) (bits : Fin N → Bool) :
    (runWithCharge prepared N bits).2.booleanWork ≤ BinaryReflectedResourceWork.bound s N :=
  BinaryReflectedCachedResourceWork.runWithCharge_bound input source hC hR hCase s hs hH prepared N bits

def lowerWithCharge {input : BinaryFourParameters.Input} (prepared : Prepared input) : Certified (prepare input).capacity × Charge :=
  let result := BinaryReflectedCachedResourceWork.Prepared.lowerWithCharge prepared
  (toOriginal prepared result.1,result.2)

theorem lowerWithCharge_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (prepared : Prepared input) :
    (lowerWithCharge prepared).1 = BinaryResourceFallback.setup input hC := by
  cases prepared with
  | mk parameters hp hpc system hs hsc capacity hc hcc work =>
      cases hs
      cases hc
      unfold lowerWithCharge toOriginal BinaryReflectedCachedResourceWork.Prepared.lowerWithCharge
        BinaryReflectedCachedResourceWork.Prepared.initialWithCharge
      dsimp only
      rw [BinaryReflectedResourceWork.initialWithCharge_state,BinaryThreeResourceFallbackWork.chooseWithCharge_state]
      rfl

theorem lowerWithCharge_charge (input : BinaryFourParameters.Input) (hC : input.Canonical) (prepared : Prepared input) :
    (lowerWithCharge prepared).2 = (BinaryThreeResourceFallbackWork.setupWithCharge input hC).2 :=
  BinaryReflectedCachedResourceWork.lowerWithCharge_charge input hC prepared

theorem lowerWithCharge_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (prepared : Prepared input) :
    (lowerWithCharge prepared).2.booleanWork ≤ BinaryThreeResourceFallbackWork.bound s :=
  BinaryReflectedCachedResourceWork.lowerWithCharge_bound input source hC hR hCase s hs hH prepared

end Blotto.BinaryReflectedCachedCertifiedResult
