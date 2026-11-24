import checkpoints.puncture_law_20261119.FlatExchange
import checkpoints.shen_extension.SingleArcAlternative

namespace LeanCH.BR.Closure.SingleArcDoubleExchange
open Finset Matrix FiniteCutInverse WeightedSD BRq2 BRq3 BR45
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcFlatResponse

private theorem eliminate {A B u d t x z : ℝ} (pa : 0<A) (wb : 0<B) (low : u<B)
    (first : x-1=x*(u/B)) (second : z-d/A=x*(t/(A*B))) :
    1≤z ↔ (B-u)*(A-d)≤t := by
  have gap := sub_pos.mpr low
  have eqx : x=B/(B-u) := by
    apply (eq_div_iff gap.ne').mpr
    field_simp [wb.ne'] at first
    linarith only [first]
  have eqz : z=(d*(B-u)+t)/(A*(B-u)) := by
    calc
      z = d/A+x*(t/(A*B)) := by linarith only [second]
      _ = _ := by rw [eqx]; field_simp [pa.ne',wb.ne',gap.ne']
  rw [eqz,le_div_iff₀ (mul_pos pa gap)]
  constructor <;> intro h <;> linarith only [h]

/-- For each old a→v and k→b, the interior tensor entry decides whether
both cuts pay together. The result uses the real graph after both cuts. -/
theorem pair {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b=false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ→ℚ}
    (wp : ∀i∈V, 0<w i ∧ 0<p i) (wm : mass V w=1)
    (wr : ∀i∈V,WeightedSD.row q E V w i=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1)
    (v k : V) (av : E a v=true) (kb : E k b=true) :
    let T := test (realMatrix q E V)⁻¹ (fun i : V => (w i:ℝ)) (fun i : V => (p i:ℝ)) q a b
    SmallRow q (eraseArc (eraseArc (insertArc E a b) a v) k b) V ↔
      w b≤w v ∨ ((w b:ℝ)-(w v:ℝ))*((p a:ℝ)-(p k:ℝ))≤T v k := by
  intro T
  let G := insertArc E a b
  let C := eraseArc G a v
  have cut := FlatExchange.tail_exchange hq small a b off safe wp wm wr pc v av
  by_cases heavy : w b≤w v
  · refine ⟨fun _ => Or.inl heavy, fun _ => ?_⟩
    intro s sn live
    obtain ⟨i,iv,le⟩ := cut.mpr heavy s sn live
    exact ⟨i,iv,le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph (fun u _ j _ => eraseArc_sub C k b u j) sn iv) (Nat.cast_nonneg q))) le⟩
  rw [or_iff_right heavy]
  obtain ⟨H,inv,scale⟩ := inverse_test hq small a b off safe wp wm wr pc
  have bad : ¬SmallRow q C V := fun h => heavy (cut.mp h)
  obtain ⟨s,sn,_,ss⟩ := strict_witness_of_not_smallRow bad
  obtain ⟨J,jinv⟩ := strict_inverse_of_proper_smallRow
    (small.induced (qfree_sub (eraseArc_sub G a v) safe)) s sn ss
  have ne : (b:ℕ)≠v := by intro eq; exact Bool.noConfusion (off.symm.trans (eq ▸ av))
  have kept : C k b=true := by simp [C,eraseArc,ne,G,insertArc_mono E a b k b kb]
  change SmallRow q (eraseArc C k b) V ↔ _
  rw [deletion_smallRow_iff jinv k b kept]
  have pa : (0:ℝ)<p a := by exact_mod_cast (wp a a.property).2
  have wb : (0:ℝ)<w b := by exact_mod_cast (wp b b.property).1
  have low : (w v:ℝ)<w b := by exact_mod_cast lt_of_not_ge heavy
  have val (i j : V) : (q:ℝ)*H i j=T i j/((p a:ℝ)*(w b:ℝ)) := by
    apply (eq_div_iff (mul_pos pa wb).ne').mpr
    linear_combination -(scale i j)
  have atA (i : V) : (q:ℝ)*H i a=(w i:ℝ)/(w b:ℝ) := by
    rw [val]
    have edge : T i a=(w i:ℝ)*(p a:ℝ) := by dsimp [T,test]; ring
    rw [edge]; field_simp [pa.ne',wb.ne']
  have atB (j : V) : (q:ℝ)*H b j=(p j:ℝ)/(p a:ℝ) := by
    rw [val]
    have edge : T b j=(w b:ℝ)*(p j:ℝ) := by dsimp [T,test]; ring
    rw [edge]; field_simp [pa.ne',wb.ne']
  have one : (q:ℝ)*H b a=1 := by rw [atB,div_self pa.ne']
  have update (j : V) : (q:ℝ)*J b j-(q:ℝ)*H b j=((q:ℝ)*J b a)*((q:ℝ)*H v j) := by
    have diff := single_increment_identity jinv inv a v (q:ℝ)
      (realMatrix_erase_difference a v (insertArc_mono E a b a v av)) b j
    linear_combination (q:ℝ)*diff
  apply eliminate pa wb low
  · simpa only [one,atA v] using update a
  · simpa only [atB k,val v k] using update k

/-- Specialization to an actual missing native arc. The old graph may omit
additional native arcs. Safety follows from inclusion in the native graph. -/
theorem native {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) (f : SharedArcFlatCut.Missing X F)
    (v k : X.V) (av : graph X.D F f.val.1 v=true) (kb : graph X.D F k f.val.2=true) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q a b
    SmallRow q (eraseArc (eraseArc (insertArc E a b) a v) k b) X.V ↔
      max 0 ((w b:ℝ)-(w v:ℝ))*max 0 ((p a:ℝ)-(p k:ℝ))≤T v k := by
  intro E a b T
  have safe : QFree (insertArc E a b) X.V q := by
    apply qfree_sub _ X.free
    intro i j ed
    by_cases hit : i=(a:ℕ) ∧ j=(b:ℕ)
    · exact hit.1 ▸ hit.2 ▸ f.property.1
    have old : E i j=true := by simpa [insertArc,hit] using ed
    exact (mem_col.mp (active.mp old).choose_spec).2.2.2
  have nn : 0≤T v k := safe_test hq small a b f.property.2 safe wp wm wr pc v k
  refine (pair hq small a b f.property.2 safe wp wm wr pc v k av kb).trans ?_
  change (w b≤w v ∨ _≤T v k) ↔ _
  by_cases h : w b≤w v
  · have d : (w b:ℝ)-(w v:ℝ)≤0 := sub_nonpos.mpr (by exact_mod_cast h)
    rw [max_eq_left d,zero_mul]
    exact iff_of_true (Or.inl h) nn
  · have d : 0≤(w b:ℝ)-(w v:ℝ) := sub_nonneg.mpr (by exact_mod_cast (le_of_not_ge h))
    rw [or_iff_right h,max_eq_right d]
    by_cases c : (p a:ℝ)-(p k:ℝ)≤0
    · rw [max_eq_left c,mul_zero]
      exact iff_of_true ((mul_nonpos_of_nonneg_of_nonpos d c).trans nn) nn
    · rw [max_eq_right (le_of_not_ge c)]

end LeanCH.BR.Closure.SingleArcDoubleExchange
#print axioms LeanCH.BR.Closure.SingleArcDoubleExchange.pair
#print axioms LeanCH.BR.Closure.SingleArcDoubleExchange.native
