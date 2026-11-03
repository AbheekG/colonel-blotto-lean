import Blotto.GeneralPaperEncodedScalarStorage

/-! Full retained prepared powers: four format scalars, the base, every
degree/mantissa/signed exponent in the linked table, and native work.
All sizes follow from actual construction, including every table prefix. -/
namespace Blotto.GeneralPaperEncodedPreparedPowers
open GeneralPaperSourcePreparationSizes GeneralPaperEncodedScalarStorage
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def formatFootprint (W : ℕ) (f : GeneralPaperPowerPrecision.Parameters) : ℕ :=
  fields W [f.unit,f.fractionalBits,f.columns,f.work]

theorem format_bound (W m lambda k Qv : ℕ) :
    formatFootprint W (GeneralPaperPowerPrecision.prepare lambda k)≤
      4*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let M := measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hm := GeneralPaperSourcePreparationControls.metadata m lambda k Qv
  have hp := hm.fractionalBits
  have hc := hm.columns
  have hw := hm.precisionWork
  change f.fractionalBits≤128*M at hp
  change f.columns≤32*M at hc
  change f.work≤8192*M at hw
  have hu := GeneralPaperParameterOperandBounds.dyadic_word f.fractionalBits
  rw [(GeneralPaperScoreScaleParameters.power_data _).1,←GeneralPaperPowerPrecision.unit_power lambda k] at hu
  have hpu := GeneralPaperInitializerControlCounters.word_le_self f.fractionalBits
  have hcu := GeneralPaperInitializerControlCounters.word_le_self f.columns
  have hwu := GeneralPaperInitializerControlCounters.word_le_self f.work
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  dsimp only [f] at hp hc hw hu hpu hcu hwu
  apply fields_bound W H
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl <;> dsimp [natBits,H,GeneralPaperPowerPreparationEnvelope.operandWidth] <;> omega

def entryBits (W : ℕ) (e : Entry) : ℕ := natBits e.degree+GeneralPaperStoredNumberBits.bits e.number+32*W

theorem entry_bound (W m lambda k Qv columns : ℕ)
    (hc : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns)
    (e : Entry)
    (he : e∈(GeneralPaperRoundedPowerTable.build
      (GeneralPaperPowerPrecision.prepare lambda k).unit
      (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
      (GeneralPaperPreparedPowers.prepare lambda k).base columns).entries) :
    entryBits W e≤2*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+32*W := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := (GeneralPaperPreparedPowers.prepare lambda k).base
  have hb := GeneralPaperPreparedPowers.prepared_base lambda k
  have hn := (build_good f.unit f.fractionalBits (GeneralPaperPowerPrecision.unit_positive lambda k)
    (GeneralPaperPowerPrecision.unit_power lambda k) b hb.1 hb.2.1 columns).2 e he
  have hex := (GeneralPaperPowerTableExponent.prefix_exponents lambda k columns hc).2 e he
  have hf := GeneralPaperStoredNumberBits.operand m lambda k Qv e.number hn.2.1
    (hex.trans (by unfold GeneralPaperQuantileExponentRange.cap; omega))
  have hd := (GeneralPaperPowerTableExponent.entries_degree_le_top f.unit f.fractionalBits columns b e he).trans
    (GeneralPaperPowerTableExponent.prefix_degree_cap lambda k columns hc)
  have hdw := (Nat.add_le_add_left (binaryWordWidth_mono hd) 1).trans
    (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
  unfold entryBits natBits
  omega

def tableFootprint (W : ℕ) (entries : List Entry) : ℕ := listFootprint W (entryBits W) entries

theorem table_prefix (W m lambda k Qv columns : ℕ)
    (hc : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns) :
    let f := GeneralPaperPowerPrecision.prepare lambda k
    tableFootprint W (build f.unit f.fractionalBits (GeneralPaperPreparedPowers.prepare lambda k).base columns).entries≤
      columns*(2*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+34*W)+32*W := by
  have hs := list_bound W (2*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+32*W)
    (entryBits W) _ (entry_bound W m lambda k Qv columns hc)
  rw [entries_length] at hs
  exact hs.trans_eq (by ring)

def footprint (W : ℕ) (p : GeneralPaperPreparedPowers.Prepared) : ℕ :=
  formatFootprint W p.format+GeneralPaperStoredNumberBits.bits p.base+tableFootprint W p.table+natBits p.work+64*W

def profile (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let c := (GeneralPaperPowerPrecision.prepare lambda k).columns
  4*(H+W)+c*(2*H+34*W)+2*H+128*W

theorem native (W m lambda k Qv : ℕ) :
    footprint W (GeneralPaperPreparedPowers.prepare lambda k)≤profile W m lambda k Qv := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
  let t := build f.unit f.fractionalBits b.number f.columns
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hFormat := format_bound W m lambda k Qv
  have hTable := table_prefix W m lambda k Qv f.columns (Nat.le_refl _)
  have hb := GeneralPaperPreparedPowers.prepared_base lambda k
  have hBase : GeneralPaperStoredNumberBits.bits b.number≤H := by
    apply GeneralPaperStoredNumberBits.operand m lambda k Qv _ hb.1
    change b.number.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k
    have he : b.number.exponent.natAbs=f.fractionalBits+1 := by
      simp only [b,GeneralPaperStoredGeometricBase.construct,Int.natAbs_neg,Int.natAbs_natCast]
    rw [he]
    unfold GeneralPaperQuantileExponentRange.cap
    dsimp only [f]
    have hg := GeneralPaperPowerTableExponent.level_positive lambda k
    omega
  have hWrap := (GeneralPaperPowerPreparationEnvelope.sizes m lambda k Qv).wrapper
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add f.work b.work
  have ha' := GeneralPaperRayOperandWidthEnvelope.word_add (f.work+b.work) t.work
  have ha'' := GeneralPaperRayOperandWidthEnvelope.word_add (f.work+b.work+t.work) 24
  have h24 : binaryWordWidth 24=5 := by decide
  have hWork : natBits (GeneralPaperPreparedPowers.prepare lambda k).work≤H := by
    change 64+8*(binaryWordWidth f.work+binaryWordWidth b.work+binaryWordWidth t.work)≤H at hWrap
    change 1+binaryWordWidth (f.work+b.work+t.work+24)≤H
    omega
  change formatFootprint W f≤4*(H+W)+32*W at hFormat
  change tableFootprint W t.entries≤f.columns*(2*H+34*W)+32*W at hTable
  change formatFootprint W f+GeneralPaperStoredNumberBits.bits b.number+tableFootprint W t.entries+
    natBits (GeneralPaperPreparedPowers.prepare lambda k).work+64*W≤4*(H+W)+f.columns*(2*H+34*W)+2*H+128*W
  omega

theorem materialized (W m lambda k Qv : ℕ) (primitive : ℕ → ℕ) (localW : ℕ) :
    footprint W (GeneralPaperMaterializedPowerCache.prepare primitive localW m lambda k Qv).1.powers≤profile W m lambda k Qv := by
  rw [GeneralPaperMaterializedPowerCache.data]
  exact native W m lambda k Qv

end Blotto.GeneralPaperEncodedPreparedPowers
