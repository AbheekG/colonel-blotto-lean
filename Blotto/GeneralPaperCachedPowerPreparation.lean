import Blotto.GeneralPaperPowerTableArithmetic

/-! Materialize powers from the returned source precision cache. Base and
table execute once; native work fields are copied as metadata. Arithmetic
and fast-bit implementations preserve the entire native prepared object.
The parameter constructor is not replayed to obtain format or annotations.
-/
namespace Blotto.GeneralPaperCachedPowerPreparation
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def wrapWidth (formatWork baseWork tableWork : ℕ) : ℕ :=
  64+8*(binaryWordWidth formatWork+binaryWordWidth baseWork+binaryWordWidth tableWork)

def wrapWork (primitive : ℕ → ℕ) (formatWork baseWork tableWork : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) formatWork baseWork+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (formatWork+baseWork) tableWork+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (formatWork+baseWork+tableWork) 24

theorem wrap_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (f b t : ℕ) :
    wrapWork primitive f b t≤6*primitive (wrapWidth f b t) := by
  let L := wrapWidth f b t
  have h1 := GeneralPaperRayOperandWidthEnvelope.word_add f b
  have h2 := GeneralPaperRayOperandWidthEnvelope.word_add (f+b) t
  have h3 := GeneralPaperRayOperandWidthEnvelope.word_add (f+b+t) 24
  have h24 : binaryWordWidth 24=5 := by decide
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) f b L
    (by dsimp [L,wrapWidth]; omega) (by dsimp [L,wrapWidth]; omega) (by dsimp [L,wrapWidth]; omega)
  have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (f+b) t L
    (by dsimp [L,wrapWidth]; omega) (by dsimp [L,wrapWidth]; omega) (by dsimp [L,wrapWidth]; omega)
  have hc := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (f+b+t) 24 L
    (by dsimp [L,wrapWidth]; omega) (by dsimp [L,wrapWidth]; omega) (by dsimp [L,wrapWidth]; omega)
  change _≤6*primitive L
  unfold wrapWork
  omega

def fromCache (primitive : ℕ → ℕ) (W k : ℕ) (c : GeneralPaperSourcePreparationCache.Cache) :
    GeneralPaperPreparedPowers.Prepared × ℕ :=
  let f := c.precision.parameters
  let base := GeneralPaperStoredBasePrice.run primitive W f.unit f.fractionalBits k
  let table := GeneralPaperPowerTablePrice.run primitive W f.unit f.fractionalBits base.1.number f.columns
  (⟨f,base.1.number,table.1.entries,f.work+base.1.work+table.1.work+24⟩,
    base.2+table.2+wrapWork primitive f.work base.1.work table.1.work+96*W)

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (fromCache primitive W k c).1=GeneralPaperPreparedPowers.prepare lambda k := by
  subst c
  let f := GeneralPaperPowerPrecision.prepare lambda k
  have hn := GeneralPaperStoredGeometricBase.construct_normal f.unit f.fractionalBits k
    (by have hh:=GeneralPaperPowerPrecision.unit_positive lambda k; exact Nat.zero_lt_of_lt hh)
    (GeneralPaperPowerPrecision.unit_power lambda k)
  unfold fromCache
  dsimp only [GeneralPaperSourcePreparationCache.specification,GeneralPaperPrecisionParameterPrice.specification]
  rw [GeneralPaperStoredBasePrice.data,GeneralPaperPowerTablePrice.data primitive W _ _
    (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k) _ hn.1 hn.2]
  rfl

def profile (primitive : ℕ → ℕ) (W lambda k : ℕ) : ℕ :=
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let base := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
  let table := GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits base.number f.columns
  GeneralPaperStoredBasePrice.profile primitive W f.unit f.fractionalBits k+
    1024*(f.columns+1)*(W+primitive (GeneralPaperPowerTableBounds.width f.fractionalBits f.columns base.number))+
    6*primitive (wrapWidth f.work base.work table.work)+96*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperSourcePreparationCache.Cache) (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (fromCache primitive W k c).2≤profile primitive W lambda k := by
  subst c
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
  let t := GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits b.number f.columns
  have hn := GeneralPaperStoredGeometricBase.construct_normal f.unit f.fractionalBits k
    (by have hh:=GeneralPaperPowerPrecision.unit_positive lambda k; exact Nat.zero_lt_of_lt hh)
    (GeneralPaperPowerPrecision.unit_power lambda k)
  have hb := GeneralPaperStoredBasePrice.work primitive hMono W f.unit f.fractionalBits k
  have ht := GeneralPaperPowerTablePrice.work primitive hMono W f.unit f.fractionalBits
    (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k) b.number hn.1 hn.2 f.columns
  have hw := wrap_work primitive hMono f.work b.work t.work
  unfold fromCache profile
  dsimp only [GeneralPaperSourcePreparationCache.specification,GeneralPaperPrecisionParameterPrice.specification]
  rw [GeneralPaperStoredBasePrice.data,GeneralPaperPowerTablePrice.data primitive W _ _
    (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k) _ hn.1 hn.2]
  dsimp only [f,b,t] at *
  omega

def arithmetic (k : ℕ) (c : GeneralPaperSourcePreparationCache.Cache) : GeneralPaperPreparedPowers.Prepared × ℕ :=
  let f := c.precision.parameters
  let base := GeneralPaperStoredBasePrice.run (fun _ => 1) 1 f.unit f.fractionalBits k
  let table := GeneralPaperPowerTableArithmetic.run f.unit f.fractionalBits base.1.number f.columns
  (⟨f,base.1.number,table.1.entries,f.work+base.1.work+table.1.work+24⟩,base.2+table.2+128)

theorem arithmetic_data (m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (arithmetic k c).1=GeneralPaperPreparedPowers.prepare lambda k := by
  subst c
  simp only [arithmetic,GeneralPaperStoredBasePrice.data,GeneralPaperPowerTableArithmetic.data,
    GeneralPaperSourcePreparationCache.specification,GeneralPaperPrecisionParameterPrice.specification]
  rfl

def arithmeticProfile (lambda k : ℕ) : ℕ :=
  let f := GeneralPaperPowerPrecision.prepare lambda k
  512*(f.fractionalBits+2)+f.columns*(12*(f.fractionalBits+1)+194)+144

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (arithmetic k c).2≤arithmeticProfile lambda k := by
  subst c
  let f := GeneralPaperPowerPrecision.prepare lambda k
  have hb := GeneralPaperStoredBasePrice.arithmetic_work f.unit f.fractionalBits k
  have ht := GeneralPaperPowerTableArithmetic.work f.unit f.fractionalBits f.columns
    (GeneralPaperStoredBasePrice.run (fun _ => 1) 1 f.unit f.fractionalBits k).1.number
  unfold arithmetic arithmeticProfile
  dsimp only [GeneralPaperSourcePreparationCache.specification,GeneralPaperPrecisionParameterPrice.specification]
  dsimp only [f] at *
  omega

theorem same_data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (fromCache primitive W k c).1=(arithmetic k c).1 := by rw [data _ _ _ _ _ _ _ hc,arithmetic_data _ _ _ _ _ hc]

end Blotto.GeneralPaperCachedPowerPreparation
