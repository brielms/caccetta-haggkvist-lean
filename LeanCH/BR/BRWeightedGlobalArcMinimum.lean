import LeanCH.BR.BRWeightedThresholdExchange

/-! The global fixed-label arc minimum is independent of maximum level. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse

structure NativeArcMinimum (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop where
  free : QFree D V q
  bad : ¬SmallRow q D V
  arc_min : ∀ E : CH.Digraph, QFree E V q → ¬SmallRow q E V →
    (arcSet D V).card≤(arcSet E V).card

theorem NativeExtremal.arcMinimum {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {c : ℚ}
    (h : NativeExtremal q D V c) : NativeArcMinimum q D V :=
  ⟨h.free,h.bad,h.arc_min⟩

theorem NativeArcMinimum.same_count {q : ℕ} {D E : CH.Digraph} {V : Finset ℕ}
    (h : NativeArcMinimum q D V) (hf : QFree E V q) (hb : ¬SmallRow q E V)
    (hn : (arcSet E V).card=(arcSet D V).card) : NativeArcMinimum q E V := by
  refine ⟨hf,hb,?_⟩
  intro K hK hbad
  rw [hn]
  exact h.arc_min K hK hbad

theorem NativeArcMinimum.critical {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : NativeArcMinimum q D V) : ArcCritical q D V := by
  intro a ha b hb hab
  by_contra hbad
  have hh := h.arc_min (eraseArc D a b) (qfree_sub (eraseArc_sub D a b) h.free) hbad
  have hmem : (a,b)∈arcSet D V := mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab⟩
  rw [arcSet_erase,card_erase_of_mem hmem] at hh
  have hp : 0<(arcSet D V).card := card_pos.mpr ⟨(a,b),hmem⟩
  omega

theorem NativeArcMinimum.reverse {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : NativeArcMinimum q D V) (hsmall : SmallerSmallRow q V.card) :
    NativeArcMinimum q (fun x y => D y x) V := by
  refine ⟨h.free.reverse,not_smallRow_reverse_of_global hsmall h.free h.bad,?_⟩
  intro E hE hb
  have hh := h.arc_min (fun x y => E y x) hE.reverse
    (not_smallRow_reverse_of_global hsmall hE hb)
  simpa only [arcSet_reverse_card] using hh

theorem NativeArcMinimum.normal_form {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : NativeArcMinimum q D V) (hsmall : SmallerSmallRow q V.card) :
    ArcCritical q D V ∧ ∃ a p : ℕ→ℚ, ∃ c : ℚ, 1<c ∧
      (∀ x∈V,0<a x) ∧ (∀ x∈V,0<p x) ∧ mass V a=1 ∧ mass V p=1 ∧
      (∀ x∈V,row q D V a x=c) ∧ (∀ x∈V,col q D V p x=c) ∧
      ∃ H : Matrix V V ℝ, CommonInverse (realMatrix q D V) H := by
  obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow h.bad
  have hp := hsmall.induced h.free
  obtain ⟨a,p,c,hc,ha,hpp,hm,hpm,hr,hpc⟩ := strict_pair_of_proper_smallRow hp hV z hz hzr
  obtain ⟨H,hH⟩ := strict_inverse_of_proper_smallRow hp z hz hzr
  exact ⟨h.critical,a,p,c,hc,ha,hpp,hm,hpm,hr,hpc,H,hH⟩

theorem NativeArcMinimum.threshold_exchange {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hmin : NativeArcMinimum q D V) (hsmall : SmallerSmallRow q V.card)
    (hH : CommonInverse (realMatrix q D V) H) (h w t b : V)
    (hhw : D h w=true) (ht : (q:ℝ)*H w h=1) (hnew : ¬eraseArc D h w t b=true)
    (hf : QFree (insertArc (eraseArc D h w) t b) V q) :
    NativeArcMinimum q (insertArc (eraseArc D h w) t b) V ∧
    NativeArcMinimum q (fun x y => insertArc (eraseArc D h w) t b y x) V := by
  have hm := hmin.same_count hf (threshold_exchange_not_smallRow hq hH h w t b hhw ht hnew)
    (arcSet_exchange_card h w t b hhw hnew)
  exact ⟨hm,hm.reverse hsmall⟩

end LeanCH.BR.WeightedSD
