import LeanCH.BR.BRUnionCrossIncidence

/-! A safe rectangle has safe union at every cutoff, and is jointly neutral
at the selected native source. Distinctness forced by the actual old/missing
incidences is not separately imposed on the algebra. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def rectangle (D : CH.Digraph) (a b c d : ℕ) : CH.Digraph := fun x y =>
  if (x=a ∧ y=d) ∨ (x=b ∧ y=c) then true
  else if (x=a ∧ y=c) ∨ (x=b ∧ y=d) then false else D x y

theorem rectangle_cross_incidence (D : CH.Digraph) (V : Finset ℕ) (a b c d : ℕ) :
    CrossIncidence D (rectangle D a b c d) V := by
  intro x hx y hy z hz t ht hxy hnxy hzt hnzt
  have hold : (x=a ∧ y=c) ∨ (x=b ∧ y=d) := by
    by_contra hh
    simp [rectangle,hh,hxy] at hnxy
  have hnew : (z=a ∧ t=d) ∨ (z=b ∧ t=c) := by
    by_contra hh
    simp [rectangle,hh,hnzt] at hzt
  rcases hold with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hnew with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

theorem qfree_rectangle_union {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {a b c d : ℕ}
    (hD : QFree D V q) (hE : QFree (rectangle D a b c d) V q) :
    QFree (arcUnion D (rectangle D a b c d)) V q :=
  qfree_union_cross_incidence hD hE (rectangle_cross_incidence D V a b c d)

theorem saturated_qfree_union_sub {q : ℕ} (hq : 1 ≤ q)
    {D E : CH.Digraph} {V : Finset ℕ} (hsat : Sat q D V)
    (hU : QFree (arcUnion D E) V q) : ∀a∈V,∀b∈V,E a b=true → D a b=true := by
  intro a ha b hb hab
  by_contra hn
  obtain ⟨_,k,hk,w⟩ := mem_ball.mp (hsat b hb a ha hn)
  have wu : Walk (arcUnion D E) V b a k := walk_sub
    (fun x y hxy => by simp [arcUnion,hxy]) w
  exact hU b (k+1) (by omega) (by omega) (wu.snoc hb (by simp [arcUnion,hab]))

theorem saturated_cross_incidence_eq_on {q : ℕ} (hq : 1 ≤ q)
    {D E : CH.Digraph} {V : Finset ℕ} (hD : QFree D V q) (hsat : Sat q D V)
    (hE : QFree E V q) (hcross : CrossIncidence D E V)
    (hcard : (arcSet E V).card=(arcSet D V).card) : ∀a∈V,∀b∈V,E a b=D a b := by
  have hsub := saturated_qfree_union_sub hq hsat (qfree_union_cross_incidence hD hE hcross)
  have hs : arcSet E V ⊆ arcSet D V := by
    intro e he
    obtain ⟨hv,hedge⟩ := mem_filter.mp he
    obtain ⟨ha,hb⟩ := mem_product.mp hv
    exact mem_filter.mpr ⟨hv,hsub e.1 ha e.2 hb hedge⟩
  have heq := eq_of_subset_of_card_le hs hcard.ge
  intro a ha b hb
  have hh : E a b=true ↔ D a b=true := by
    have := congrArg (fun S => (a,b)∈S) heq
    simpa [arcSet,ha,hb] using this
  exact Bool.eq_iff_iff.mpr hh

theorem saturated_rectangle_impossible {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {a b c d : ℕ}
    (hD : QFree D V q) (hsat : Sat q D V) (ha : a∈V) (hd : d∈V)
    (had : ¬D a d=true) (hE : QFree (rectangle D a b c d) V q) : False :=
  had (saturated_qfree_union_sub hq hsat (qfree_rectangle_union hD hE) a ha d hd (by simp [rectangle]))

theorem qfree_exchange_of_union {q : ℕ} {D E : CH.Digraph} {V : Finset ℕ}
    {r s u t : ℕ} (hf : QFree (arcUnion D E) V q) (hnew : E u t=true) :
    QFree (insertArc (eraseArc D r s) u t) V q := by
  apply qfree_sub (fun x y hxy => ?_) hf
  by_cases hh : x=u ∧ y=t
  · rcases hh with ⟨rfl,rfl⟩
    simp [arcUnion,hnew]
  · have he : eraseArc D r s x y=true := by simpa [insertArc,hh] using hxy
    simp [arcUnion,eraseArc_sub D r s x y he]

theorem rectangle_sequential {D : CH.Digraph} {a b c d : ℕ}
    (hab : a≠b) (hcd : c≠d) : rectangle D a b c d=
      insertArc (eraseArc (insertArc (eraseArc D a c) a d) b d) b c := by
  funext x y
  by_cases hxa : x=a <;> by_cases hxb : x=b <;>
    by_cases hyc : y=c <;> by_cases hyd : y=d <;>
    simp_all [rectangle,insertArc,eraseArc]

theorem row_rectangle (q : ℕ) {D : CH.Digraph} {V : Finset ℕ} {a b c d : ℕ}
    (hc : c∈V) (hd : d∈V) (hac : D a c=true) (hbd : D b d=true)
    (had : ¬D a d=true) (hbc : ¬D b c=true) (w : ℕ→ℚ) (x : ℕ) :
    row q (rectangle D a b c d) V w x=row q D V w x+
      (if x=a then (q:ℚ)*(w d-w c) else 0)+(if x=b then (q:ℚ)*(w c-w d) else 0) := by
  have hab : a≠b := fun hh => hbc (by simpa [hh] using hac)
  have hcd : c≠d := fun hh => had (by simpa [hh] using hac)
  have hba : b≠a := Ne.symm hab
  have hbd' : insertArc (eraseArc D a c) a d b d=true := by simp [insertArc,eraseArc,hba,hbd]
  have hbc' : ¬insertArc (eraseArc D a c) a d b c=true := by simp [insertArc,eraseArc,hba,hbc]
  rw [rectangle_sequential hab hcd,row_same_tail_exchange q hd hc hbd' hbc',
    row_same_tail_exchange q hc hd hac had]

theorem rectangle_reverse (D : CH.Digraph) (a b c d : ℕ) :
    (fun x y => rectangle D a b c d y x)=rectangle (fun x y => D y x) c d a b := by
  funext x y
  simp only [rectangle,and_comm,or_comm]

theorem NativeExtremal.rectangle_preserves_two_laws {q : ℕ} (hq : 0<q)
    {D : CH.Digraph} {V : Finset ℕ} {level : ℚ}
    (h : NativeExtremal q D V level) (hsmall : SmallerSmallRow q V.card) (hlevel : 1<level)
    (w p : ℕ→ℚ) (hw : ∀x∈V,0<w x) (hp : ∀x∈V,0<p x)
    (hmw : mass V w=1) (hmp : mass V p=1)
    (hr : ∀x∈V,row q D V w x=level) (hcol : ∀x∈V,col q D V p x=level)
    {a b c d : ℕ} (ha : a∈V) (hb : b∈V) (hc : c∈V) (hd : d∈V)
    (hac : D a c=true) (hbd : D b d=true) (had : ¬D a d=true) (hbc : ¬D b c=true)
    (hE : QFree (rectangle D a b c d) V q) :
    w c=w d ∧ p a=p b ∧
      (∀x∈V,row q (rectangle D a b c d) V w x=level) ∧
      (∀x∈V,col q (rectangle D a b c d) V p x=level) := by
  have hU := qfree_rectangle_union h.free hE
  have had' : rectangle D a b c d a d=true := by simp [rectangle]
  have hbc' : rectangle D a b c d b c=true := by simp [rectangle]
  have hwdc := h.same_tail_weight_le hq hsmall hlevel w hw hmw hr ha hc hd hac had
    (qfree_exchange_of_union hU had')
  have hwcd := h.same_tail_weight_le hq hsmall hlevel w hw hmw hr hb hd hc hbd hbc
    (qfree_exchange_of_union hU hbc')
  have hwcd' : w c=w d := le_antisymm hwcd hwdc
  have hpba := h.same_head_weight_le hq hsmall hlevel p hp hmp hcol hc ha hb hac hbc
    (qfree_exchange_of_union hU hbc')
  have hpab := h.same_head_weight_le hq hsmall hlevel p hp hmp hcol hd hb ha hbd had
    (qfree_exchange_of_union hU had')
  have hpab' : p a=p b := le_antisymm hpab hpba
  refine ⟨hwcd',hpab',?_,?_⟩
  · intro x hx
    rw [row_rectangle q hc hd hac hbd had hbc]
    simpa only [hwcd',sub_self,mul_zero,ite_self,add_zero] using hr x hx
  · intro x hx
    change row q (fun y z => rectangle D a b c d z y) V p x=level
    rw [rectangle_reverse,row_rectangle q ha hb hac hbd hbc had]
    simp only [hpab',sub_self,mul_zero,ite_self,add_zero]
    exact hcol x hx

end LeanCH.BR.WeightedSD
