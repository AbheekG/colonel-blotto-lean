import Blotto.GeneralPaperSummaryConstructionStorage

/-! Outer field-family prefixes own their completed summary payloads and
reserve every field-reference slot. All four family arrays may coexist.
The inner quantile workspace is counted separately once per active callback. -/
namespace Blotto.GeneralPaperSummaryFamilyStorage
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def summaryProfile (W k height : ℕ) : ℕ :=
  (GeneralPaperSourceParameters.prepare k).summarySize*(height+2+W)+32*W

def frames (W m : ℕ) : ℕ :=
  (m+1)*(4*GeneralPaperEncodedScalarStorage.natBits (m+1)+128*W)

def familyProfile (W m k height : ℕ) : ℕ := m*(summaryProfile W k height+W)+64*W+frames W m

theorem native_summary (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node height) (hh : height≤lambda+1) (hv : Valid lambda k node)
    (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    GeneralPaperEncodedNatArray.footprint W (GeneralPaperNativeSummaryArray.run bits index primitive W m lambda k Qv c hc digits height node).1≤
      summaryProfile W k height := by
  apply GeneralPaperEncodedNatArray.bounded W (height+2)
  intro r
  rw [GeneralPaperNativeSummaryArray.data bits index primitive W m lambda k Qv c hc digits height node hh hv hp]
  have h := GeneralPaperInitialSummary.code_bounds c.powers digits (GeneralPaperSourceParameters.prepare k).summarySize height node r
  exact (Nat.add_le_add_left (GeneralPaperCFOperandPrice.small_word height _ h) 1).trans_eq (by omega)

def buffer (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (digits height : ℕ) (nodes : FixedArrayTable m (Node height)) (count : ℕ) (hcount : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperEncodedNatArray.footprint W)
    (PaperIndexedArrayConstruction.fill index (if bits then GeneralPaperSummaryArrayExecution.arrayWord W m else W)
      (fun field =>
        let s := GeneralPaperNativeSummaryArray.run bits index primitive W m lambda k Qv c hc digits height (nodes.read field)
        (s.1,s.2+16*W)) count hcount).1+frames W m

theorem prefix_bound (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (digits height : ℕ) (nodes : FixedArrayTable m (Node height)) (hh : height≤lambda+1)
    (hv : ∀ j,Valid lambda k (nodes.read j)) (hp : ∀ j,PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 (nodes.read j))
    (count : ℕ) (hcount : count≤m) :
    buffer bits index primitive W m lambda k Qv c hc digits height nodes count hcount≤familyProfile W m k height :=
  Nat.add_le_add_right (GeneralPaperEncodedReferenceVector.indexed_reserved_prefix index
    (if bits then GeneralPaperSummaryArrayExecution.arrayWord W m else W) W (summaryProfile W k height)
    (GeneralPaperEncodedNatArray.footprint W)
    (fun field : Fin m =>
      let s := GeneralPaperNativeSummaryArray.run bits index primitive W m lambda k Qv c hc digits height (nodes.read field)
      (s.1,s.2+16*W))
    (fun field => native_summary bits index primitive W m lambda k Qv digits height c hc (nodes.read field) hh (hv field) (hp field)) count hcount) _

theorem family_mono (W m k h H : ℕ) (hh : h≤H) : familyProfile W m k h≤familyProfile W m k H := by
  unfold familyProfile summaryProfile
  gcongr

theorem four_prefixes (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv digits : ℕ)
    (a : GeneralPaperCodeAlphabet.Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (hv : GeneralPaperCatalogueTreeCache.Valid a k trees) (hp : GeneralPaperCatalogueTreeCache.Paths a k trees)
    (count : ℕ) (hcount : count≤m) :
    buffer bits index primitive W m a.lambda k Qv c hc digits a.lambda trees.p count hcount+
      buffer bits index primitive W m a.lambda k Qv c hc digits a.lambda trees.q count hcount+
      buffer bits index primitive W m a.lambda k Qv c hc digits (a.lambda+1) trees.lambda count hcount+
      buffer bits index primitive W m a.lambda k Qv c hc digits (a.lambda+1) trees.mu count hcount≤
      4*familyProfile W m k (a.lambda+1) := by
  have p := (prefix_bound bits index primitive W m a.lambda k Qv c hc digits a.lambda trees.p (by omega) (hv .p) (hp .p) count hcount).trans
    (family_mono W m k a.lambda (a.lambda+1) (by omega))
  have q := (prefix_bound bits index primitive W m a.lambda k Qv c hc digits a.lambda trees.q (by omega) (hv .q) (hp .q) count hcount).trans
    (family_mono W m k a.lambda (a.lambda+1) (by omega))
  have l := prefix_bound bits index primitive W m a.lambda k Qv c hc digits (a.lambda+1) trees.lambda (Nat.le_refl _) (hv .lambda) (hp .lambda) count hcount
  have u := prefix_bound bits index primitive W m a.lambda k Qv c hc digits (a.lambda+1) trees.mu (Nat.le_refl _) (hv .mu) (hp .mu) count hcount
  omega

end Blotto.GeneralPaperSummaryFamilyStorage
