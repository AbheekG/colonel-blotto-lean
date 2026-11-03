import Blotto.BinaryTerminalPacking
import Blotto.BinaryGroupRoutes

/-! The native terminal routing table is prepared from computed member lists
and cached totals. Its semantic partition is transported only by an erased
size equality; every actual route and emission matches the original partition. -/

namespace Blotto.BinaryTerminalRoutes
open BinaryRationalNormalization BinaryRationalEncoding BinaryTerminalGrouping

def prepare {n : ℕ} (input : Input n) : FixedArrayTable n (BinaryGroupRoutes.Route (groups input).length) :=
  BinaryGroupRoutes.prepare input.length (BinaryTerminalPacking.prepare input)

def transportPartition {n m k : ℕ} (he : m=k) (partition : RationalProportionalGroups n m) : RationalProportionalGroups n k := he ▸ partition

theorem transport_length {n m k : ℕ} (he : m=k) (partition : RationalProportionalGroups n m) :
    (transportPartition he partition).length=partition.length := by cases he; rfl

theorem transport_members {n m k : ℕ} (he : m=k) (partition : RationalProportionalGroups n m) (g : Fin k) :
    (transportPartition he partition).members g=partition.members (g.cast he.symm) := by cases he; rfl

theorem transport_total {n m k : ℕ} (he : m=k) (partition : RationalProportionalGroups n m) (g : Fin k) :
    (transportPartition he partition).total g=partition.total (g.cast he.symm) := by cases he; rfl

noncomputable def sourcePartition {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) : RationalProportionalGroups n (groups input).length :=
  transportPartition (congrArg List.length (groups_refines input source hC hr)).symm source.partition

theorem partition_length {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) : (sourcePartition input source hC hr).length = source.length :=
  transport_length _ _

theorem partition_members {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) (g : Fin (groups input).length) :
    (sourcePartition input source hC hr).members g = (groups input).get g := by
  rw [sourcePartition,transport_members]
  change source.groups.get _ = (groups input).get g
  exact (List.getElem_of_eq (groups_refines input source hC hr) (i:=g.val) g.isLt).symm

theorem partition_total {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) (g : Fin (groups input).length) :
    (sourcePartition input source hC hr).total g = value ((BinaryTerminalPacking.prepare input).read g).2 := by
  rw [sourcePartition,transport_total]
  exact (BinaryTerminalPacking.prepare_total input source hC hr g).symm

theorem prepare_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) :
    ∀ j, CanonicalWord ((prepare input).read j).2 :=
  BinaryGroupRoutes.prepare_canonical input.length (BinaryTerminalPacking.prepare input) hC.2.1
    (BinaryTerminalPacking.prepare_canonical input hC)

theorem prepare_refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) :
    ∀ j, BinaryGroupRoutes.routeValue ((prepare input).read j) = (sourcePartition input source hC hr).routes.read j := by
  apply BinaryGroupRoutes.prepare_refines _ _ _ hC.2.1 (BinaryTerminalPacking.prepare_canonical input hC)
  · intro j
    rw [partition_length]
    exact hr.2.1 j
  · intro g
    rw [BinaryTerminalPacking.prepare_members,partition_members]
  · intro g
    exact (partition_total input source hC hr g).symm

end Blotto.BinaryTerminalRoutes
