import Blotto.BinaryReflectedSetupCache
import Blotto.BinaryThreeResourceFallbackWork

/-! Random and deterministic lower resource entry points consume the retained
system/initial/capacity arrays directly. Their complete states/none/positions
and charges equal the original producers, while setup/capacity construction
is charged by the separate cached prefix. Whole request integration and
metadata/physical ownership costs remain further obligations. -/

namespace Blotto.BinaryReflectedCachedResourceWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup BinaryReflectedSetupCache
open BinaryThreeResourcePair BinarySharedResourceRun BinaryGeneralResourceExecution

def Prepared.initialWithCharge {input : BinaryFourParameters.Input} (prepared : Prepared input) : Certified prepared.capacity × Charge :=
  BinaryReflectedResourceWork.initialWithCharge prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2

def Prepared.runWithCharge {input : BinaryFourParameters.Input} (prepared : Prepared input) (N : ℕ) (bits : Fin N → Bool) :
    (Option (Certified prepared.capacity) × ℕ) × Charge :=
  let initial := Prepared.initialWithCharge prepared
  let later := BinaryThreeResourceRunWork.runIndexed N bits
    (.ready initial.1 : Cursor prepared.capacity prepared.capacity_canonical) 0 (Nat.zero_le N)
  (later.1,initial.2.add later.2)

theorem runWithCharge_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (prepared : Prepared input)
    (N : ℕ) (bits : Fin N → Bool) :
    ((Prepared.runWithCharge prepared N bits).1.1.map (fun result => result.state),(Prepared.runWithCharge prepared N bits).1.2) =
      ((setupRun input hC N bits).1.map (fun result => result.state),(setupRun input hC N bits).2) := by
  cases prepared with
  | mk parameters hp hpc system hs hsc capacity hc hcc work =>
      cases hs
      cases hc
      unfold Prepared.runWithCharge Prepared.initialWithCharge
      dsimp only
      rw [BinaryReflectedResourceWork.initialWithCharge_state,BinaryThreeResourceRunWork.runIndexed_state]
      rfl

theorem runWithCharge_charge (input : BinaryFourParameters.Input) (hC : input.Canonical) (prepared : Prepared input)
    (N : ℕ) (bits : Fin N → Bool) :
    (Prepared.runWithCharge prepared N bits).2 = (BinaryReflectedResourceWork.runWithCharge input hC N bits).2 := by
  cases prepared with
  | mk parameters hp hpc system hs hsc capacity hc hcc work =>
      cases hs
      cases hc
      rfl

theorem runWithCharge_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (prepared : Prepared input) (N : ℕ) (bits : Fin N → Bool) :
    (Prepared.runWithCharge prepared N bits).2.booleanWork ≤ BinaryReflectedResourceWork.bound s N := by
  rw [runWithCharge_charge input hC prepared N bits]
  exact BinaryReflectedResourceWork.runWithCharge_bound input source hC hR hCase s hs hH N bits

def Prepared.lowerWithCharge {input : BinaryFourParameters.Input} (prepared : Prepared input) : Certified prepared.capacity × Charge :=
  let initial := Prepared.initialWithCharge prepared
  let later := BinaryThreeResourceFallbackWork.chooseWithCharge prepared.capacity_canonical initial.1
  (later.1,initial.2.add later.2)

theorem lowerWithCharge_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (prepared : Prepared input) :
    (Prepared.lowerWithCharge prepared).1.state = (BinaryResourceFallback.setup input hC).state := by
  cases prepared with
  | mk parameters hp hpc system hs hsc capacity hc hcc work =>
      cases hs
      cases hc
      unfold Prepared.lowerWithCharge Prepared.initialWithCharge
      dsimp only
      rw [BinaryReflectedResourceWork.initialWithCharge_state,BinaryThreeResourceFallbackWork.chooseWithCharge_state]
      rfl

theorem lowerWithCharge_charge (input : BinaryFourParameters.Input) (hC : input.Canonical) (prepared : Prepared input) :
    (Prepared.lowerWithCharge prepared).2 = (BinaryThreeResourceFallbackWork.setupWithCharge input hC).2 := by
  cases prepared with
  | mk parameters hp hpc system hs hsc capacity hc hcc work =>
      cases hs
      cases hc
      rfl

theorem lowerWithCharge_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (prepared : Prepared input) :
    (Prepared.lowerWithCharge prepared).2.booleanWork ≤ BinaryThreeResourceFallbackWork.bound s := by
  rw [lowerWithCharge_charge input hC prepared]
  exact BinaryThreeResourceFallbackWork.setupWithCharge_bound input source hC hR hCase s hs hH

end Blotto.BinaryReflectedCachedResourceWork
