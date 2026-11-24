import LeanCH.BR.BRWeightedExtremalSelection

/-! Competitors use their OWN positive dual. Safe graph membership and arc
count equality are explicit; no joint-switch safety is inferred. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse WeightedArithmetic
open scoped Matrix

theorem rational_cross_rows (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (a p : ℕ→ℚ) :
    (∑ x∈V,p x*row q D V a x)=∑ x∈V,a x*col q D V p x := by
  have hh := real_cross_rows q D V (fun x => (a x : ℝ)) (fun x => (p x : ℝ))
  simp only [realRow_rat,realCol_rat] at hh
  exact_mod_cast hh

theorem row_laws_unique_on {q : ℕ} (hq : 2≤q) {D : CH.Digraph} {V : Finset ℕ}
    {a b : ℕ→ℚ} {c : ℚ} (ha : ∀ x∈V,row q D V a x=c)
    (hb : ∀ x∈V,row q D V b x=c) : ∀ x∈V,a x=b x := by
  have hu : IsUnit (rationalMatrix q (adjacencyMatrix D V)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (rational_det_ne_zero hq _))
  have he := (Matrix.mulVec_injective_iff_isUnit.mpr hu) (show
      rationalMatrix q (adjacencyMatrix D V) *ᵥ (fun i : V => a i)=
      rationalMatrix q (adjacencyMatrix D V) *ᵥ (fun i : V => b i) by
    funext i
    rw [matrix_row,matrix_row,ha i i.property,hb i i.property])
  exact fun x hx => congrFun he ⟨x,hx⟩

/-- Any weakly row-improving equal-size safe competitor is neutral on every
old primal row and has its own positive pair at the same extremal level. -/
theorem NativeExtremal.competitor_rows {q : ℕ} {D E : CH.Digraph} {V : Finset ℕ} {c : ℚ}
    (h : NativeExtremal q D V c) (hsmall : SmallerSmallRow q V.card)
    (hc : 1<c) (a : ℕ→ℚ) (ha : ∀ x∈V,0<a x) (hm : mass V a=1)
    (hE : QFree E V q) (hcount : (arcSet E V).card=(arcSet D V).card)
    (hgain : ∀ x∈V,c≤row q E V a x) :
    (∀ x∈V,row q E V a x=c) ∧ ∃ b p' : ℕ→ℚ,
      (∀ x∈V,0<b x) ∧ (∀ x∈V,0<p' x) ∧ mass V b=1 ∧ mass V p'=1 ∧
      (∀ x∈V,row q E V b x=c) ∧ (∀ x∈V,col q E V p' x=c) := by
  obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow h.bad
  have hbadE : ¬ SmallRow q E V := fun hs => hs.no_strict hV a
    (fun x hx => (ha x hx).le) (fun x hx => by rw [hm]; exact hc.trans_le (hgain x hx))
  obtain ⟨z',hz',_,hzr'⟩ := strict_witness_of_not_smallRow hbadE
  obtain ⟨b,p',d,hd,hb,hp',hbm,hpm,hbr,hpc⟩ :=
    strict_pair_of_proper_smallRow (hsmall.induced hE) hV z' hz' hzr'
  have hmax := h.level_max E hE hbadE hcount b d hbm hbr
  have hpair : (∑ x∈V,p' x*row q E V a x)=d := by
    rw [rational_cross_rows]
    rw [sum_congr rfl (fun x hx => by rw [hpc x hx])]
    rw [← sum_mul]
    change mass V a*d=d
    rw [hm,one_mul]
  have htight : ∀ x∈V,row q E V a x=c := by
    intro x hx
    apply le_antisymm ?_ (hgain x hx)
    by_contra hh
    have hl : (∑ y∈V,p' y*c)<∑ y∈V,p' y*row q E V a y := by
      apply sum_lt_sum
      · exact fun y hy => mul_le_mul_of_nonneg_left (hgain y hy) (hp' y hy).le
      · exact ⟨x,hx,mul_lt_mul_of_pos_left (lt_of_not_ge hh) (hp' x hx)⟩
    rw [← sum_mul] at hl
    change mass V p'*c< _ at hl
    rw [hpm,one_mul,hpair] at hl
    exact (not_lt_of_ge hmax) hl
  have hd : c=d := equalizer_level_eq a p' hm hpm c d htight hpc
  rw [← hd] at hbr hpc
  exact ⟨htight,b,p',hb,hp',hbm,hpm,hbr,hpc⟩

theorem NativeExtremal.competitor_preserves_primal {q : ℕ} (hq : 2≤q)
    {D E : CH.Digraph} {V : Finset ℕ} {c : ℚ}
    (h : NativeExtremal q D V c) (hsmall : SmallerSmallRow q V.card)
    (hc : 1<c) (a : ℕ→ℚ) (ha : ∀ x∈V,0<a x) (hm : mass V a=1)
    (hE : QFree E V q) (hcount : (arcSet E V).card=(arcSet D V).card)
    (hgain : ∀ x∈V,c≤row q E V a x) :
    (∀ x∈V,row q E V a x=c) ∧ ∃ p' : ℕ→ℚ,
      (∀ x∈V,0<p' x) ∧ mass V p'=1 ∧ (∀ x∈V,col q E V p' x=c) ∧
      ∀ b : ℕ→ℚ, (∀ x∈V,row q E V b x=c) → ∀ x∈V,b x=a x := by
  obtain ⟨ht,b,p',_,hp',_,hpm,_,hpc⟩ := h.competitor_rows hsmall hc a ha hm hE hcount hgain
  exact ⟨ht,p',hp',hpm,hpc,fun b hb => row_laws_unique_on hq hb ht⟩

theorem arcSet_reverse_card (D : CH.Digraph) (V : Finset ℕ) :
    (arcSet (fun x y => D y x) V).card=(arcSet D V).card := by
  have he : arcSet (fun x y => D y x) V=(arcSet D V).image Prod.swap := by
    ext e
    rcases e with ⟨x,y⟩
    simp [arcSet,and_comm,and_left_comm,and_assoc]
  rw [he,card_image_of_injective]
  intro a b hab
  simpa using congrArg Prod.swap hab

theorem not_smallRow_reverse_of_global {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) (hbad : ¬ SmallRow q D V) :
    ¬ SmallRow q (fun x y => D y x) V := by
  obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow hbad
  obtain ⟨a,p,c,hc,ha,hp,hm,hpm,hr,hpc⟩ :=
    strict_pair_of_proper_smallRow (hsmall.induced hf) hV z hz hzr
  exact fun hs => hs.not_strictPositiveRows (reverse_strict_of_pair hc hp hpm hpc)

/-- Reverse extremality uses the global competitor class and each competing
graph's own pair. It is not inherited from arbitrary matrix reversal. -/
theorem NativeExtremal.reverse {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {c : ℚ}
    (h : NativeExtremal q D V c) (hsmall : SmallerSmallRow q V.card) :
    NativeExtremal q (fun x y => D y x) V c := by
  refine ⟨h.free.reverse,not_smallRow_reverse_of_global hsmall h.free h.bad,?_,?_⟩
  · intro E hE hbad
    have hb := not_smallRow_reverse_of_global hsmall hE hbad
    have hh := h.arc_min (fun x y => E y x) hE.reverse hb
    simpa only [arcSet_reverse_card] using hh
  · intro E hE hbad hcount b d hbm hbr
    obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow hbad
    obtain ⟨a,p,t,ht,ha,hp,hm,hpm,hr,hpc⟩ :=
      strict_pair_of_proper_smallRow (hsmall.induced hE) hV z hz hzr
    have hd := equalizer_level_eq b p hbm hpm d t hbr hpc
    rw [hd]
    apply h.level_max (fun x y => E y x) hE.reverse
      (not_smallRow_reverse_of_global hsmall hE hbad) ?_ p t hpm hpc
    simpa only [arcSet_reverse_card] using hcount

end LeanCH.BR.WeightedSD
