import LeanCH.BR.BRFiniteThresholdExchange
import LeanCH.BR.BRWeightedExtremalExchange
import LeanCH.BR.BRWeightedNativePressureRepair
import LeanCH.BR.BRWeightedNonnegativePressure

/-! An exact-threshold deletion followed by an actual safe new arc.
The endpoint receives its own positive pair; equality concerns level only. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix FiniteCutInverse BRq2 BRq3 BR45 BRsub ThresholdUnit
open scoped Matrix

theorem realMatrix_exchange_difference {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h w t b : V) (hhw : D h w=true) (hnew : ¬eraseArc D h w t b=true) (i j : V) :
    realMatrix q (insertArc (eraseArc D h w) t b) V i j-realMatrix q D V i j=
      (if i=t ∧ j=b then (q:ℝ) else 0)-(if i=h ∧ j=w then (q:ℝ) else 0) := by
  linear_combination realMatrix_insert_difference (q := q) t b hnew i j -
    realMatrix_erase_difference (q := q) h w hhw i j

theorem arcSet_exchange_card {D : CH.Digraph} {V : Finset ℕ}
    (h w t b : V) (hhw : D h w=true) (hnew : ¬eraseArc D h w t b=true) :
    (arcSet (insertArc (eraseArc D h w) t b) V).card=(arcSet D V).card := by
  have hmem : (h.val,w.val)∈arcSet D V := mem_filter.mpr ⟨mem_product.mpr ⟨h.property,w.property⟩,hhw⟩
  have hn : (t.val,b.val)∉arcSet (eraseArc D h w) V := fun hh => hnew (mem_filter.mp hh).2
  rw [arcSet_insert t.property b.property,card_insert_of_notMem hn,arcSet_erase,card_erase_of_mem hmem]
  have hp := card_pos.mpr ⟨(h.val,w.val),hmem⟩
  omega

theorem exact_threshold_inverse_row_pos {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) (h w : V)
    (hhw : D h w=true) (ht : (q:ℝ)*H w h=1) : ∀t,0<H w t := by
  obtain ⟨p,hp,_,_,hpi⟩ := exact_arc_threshold_pair hq hH h w hhw ht
  intro t
  have hpR : (0:ℝ)<p t := by exact_mod_cast hp t t.property
  rw [hpi] at hpR
  change 0<H w t/(∑j,H w j) at hpR
  have hs := inverse_row_sum_pos hH w
  have hh := mul_pos hpR hs
  rwa [div_mul_cancel₀ _ (ne_of_gt hs)] at hh

theorem threshold_exchange_not_smallRow {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) (h w t b : V)
    (hhw : D h w=true) (ht : (q:ℝ)*H w h=1) (hnew : ¬eraseArc D h w t b=true) :
    ¬SmallRow q (insertArc (eraseArc D h w) t b) V := by
  obtain ⟨a,p,ha,hm,hr,_,_,_,_,_⟩ := exact_arc_threshold_two_laws hq hH h w hhw ht
  exact positive_feasible_extension_not_smallRow hq
    (fun x _ y _ hxy => insertArc_mono (eraseArc D h w) t b x y hxy)
    a ha (fun x hx => by rw [hm,hr x hx]) t.property b.property hnew (by simp [insertArc])

theorem threshold_exchange_normal_form {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hsmall : SmallerSmallRow q V.card) (hH : CommonInverse (realMatrix q D V) H)
    (h w t b : V) (hhw : D h w=true) (ht : (q:ℝ)*H w h=1)
    (hnew : ¬eraseArc D h w t b=true) (hf : QFree (insertArc (eraseArc D h w) t b) V q) :
    ∃ a' p' : ℕ→ℚ, ∃ c' : ℚ, 1<c' ∧ (∀x∈V,0<a' x) ∧ (∀x∈V,0<p' x) ∧
      mass V a'=1 ∧ mass V p'=1 ∧
      (∀x∈V,row q (insertArc (eraseArc D h w) t b) V a' x=c') ∧
      (∀x∈V,col q (insertArc (eraseArc D h w) t b) V p' x=c') := by
  have hbad := threshold_exchange_not_smallRow hq hH h w t b hhw ht hnew
  obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow hbad
  exact strict_pair_of_proper_smallRow (hsmall.induced hf) hV z hz hzr

theorem NativeExtremal.threshold_exchange_price {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {c : ℚ} {H : Matrix V V ℝ}
    (hsel : NativeExtremal q D V c) (hsmall : SmallerSmallRow q V.card)
    (hH : CommonInverse (realMatrix q D V) H)
    (a p : ℕ→ℚ) (hp : ∀x∈V,0<p x) (hma : mass V a=1) (hmp : mass V p=1)
    (hr : ∀x∈V,row q D V a x=c) (hc : ∀x∈V,col q D V p x=c)
    (h w t b : V) (hhw : D h w=true) (ht : (q:ℝ)*H w h=1)
    (hnew : ¬eraseArc D h w t b=true) (hf : QFree (insertArc (eraseArc D h w) t b) V q) :
    let S := ThresholdExchange.thresholdPrice H (fun i : V => (a i:ℝ)) (fun i : V => (p i:ℝ)) q h w t b
    ∃ a' p' : ℕ→ℚ, ∃ c' : ℚ, 1<c' ∧ c' ≤ c ∧ (∀x∈V,0<a' x) ∧ (∀x∈V,0<p' x) ∧
      mass V a'=1 ∧ mass V p'=1 ∧
      (∀x∈V,row q (insertArc (eraseArc D h w) t b) V a' x=c') ∧
      (∀x∈V,col q (insertArc (eraseArc D h w) t b) V p' x=c') ∧
      (p' t:ℝ)*S=H w t*(p h:ℝ)*((c:ℝ)-(c':ℝ)) ∧ 0 ≤ S ∧ (S=0 ↔ c'=c) := by
  dsimp only
  obtain ⟨a',p',c',hlev,ha',hp',hma',hmp',hr',hc'⟩ :=
    threshold_exchange_normal_form hq hsmall hH h w t b hhw ht hnew hf
  have hbad := threshold_exchange_not_smallRow hq hH h w t b hhw ht hnew
  have hmax := hsel.level_max _ hf hbad (arcSet_exchange_card h w t b hhw hnew) a' c' hma' hr'
  have hid := ThresholdExchange.threshold_price_identity hH.right
    (realMatrix_exchange_difference h w t b hhw hnew) ht
    (fun i : V => (a i:ℝ)) (fun i : V => (p i:ℝ)) (fun i : V => (p' i:ℝ))
    (real_mass_of_rational_probability a hma) (real_mass_of_rational_probability p hmp)
    (real_mass_of_rational_probability p' hmp') (c:ℝ) (c':ℝ)
    (realMatrix_rational_rows a c hr) (realMatrix_rational_columns p c hc)
    (realMatrix_rational_columns p' c' hc')
  have hpt : (0:ℝ)<p' t := by exact_mod_cast hp' t t.property
  have hph : (0:ℝ)<p h := by exact_mod_cast hp h h.property
  have hHt := exact_threshold_inverse_row_pos hq hH h w hhw ht t
  have hfactor : 0<H w t*(p h:ℝ) := mul_pos hHt hph
  have hdiff : 0 ≤ (c:ℝ)-(c':ℝ) := sub_nonneg.mpr (by exact_mod_cast hmax)
  have hnonneg := mul_nonneg hfactor.le hdiff
  rw [←hid] at hnonneg
  have hprice := (mul_nonneg_iff_of_pos_left hpt).mp hnonneg
  refine ⟨a',p',c',hlev,hmax,ha',hp',hma',hmp',hr',hc',hid,hprice,?_⟩
  constructor
  · intro hs
    rw [hs,mul_zero] at hid
    have he := (mul_eq_zero.mp hid.symm).resolve_left (ne_of_gt hfactor)
    have hreal : (c':ℝ)=(c:ℝ) := by linarith
    exact_mod_cast hreal
  · intro he
    subst c'
    simp only [sub_self,mul_zero] at hid
    exact (mul_eq_zero.mp hid).resolve_left (ne_of_gt hpt)

end LeanCH.BR.WeightedSD
