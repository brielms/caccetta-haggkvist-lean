import LeanCH.BR.BRWeightedOutUniformSaturation

/-! Actual same-label repair of a nonsaturated single-excess source.
The reversed strict law comes from the deletion's own positive unit dual. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse

theorem positive_feasible_extension_not_smallRow {q : ℕ} (hq : 2 ≤ q)
    {D E : CH.Digraph} {V : Finset ℕ}
    (hDE : ∀ x∈V, ∀ y∈V, D x y=true → E x y=true)
    (a : ℕ → ℚ) (ha : ∀ x∈V, 0<a x)
    (hr : ∀ x∈V, mass V a≤row q D V a x)
    {u v : ℕ} (hu : u∈V) (hv : v∈V)
    (hD : ¬ D u v=true) (hE : E u v=true) : ¬ SmallRow q E V :=
  fun hs => positive_feasible_no_added_arc hq hDE hs a ha hr hu hv hD hE

/-- No equalized or positive source is needed for this selection step.
The actual smaller-order hypothesis supplies positivity after minimization. -/
theorem native_core_below_degree {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hbad : ¬ SmallRow q D V) {w : ℕ}
    (hdeg : 1+q*(outN D V w).card<V.card) :
    ∃ E : CH.Digraph, (∀ x y, E x y=true → D x y=true) ∧
      QFree E V q ∧ ArcCritical q E V ∧ StrictPositiveRows q E V ∧
      1+q*(outN E V w).card<V.card := by
  obtain ⟨E,hED,hEf,hEb,hEc⟩ := exists_arc_critical_subgraph hf hbad
  obtain ⟨z,hz,hV,hzr⟩ := strict_witness_of_not_smallRow hEb
  obtain ⟨a,p,c,hc,ha,hp,hm,hpm,hr,hpc⟩ :=
    strict_pair_of_proper_smallRow (hsmall.induced hEf) hV z hz hzr
  refine ⟨E,hED,hEf,hEc,⟨a,ha,hm,fun x hx => by rw [hr x hx]; exact hc⟩,?_⟩
  have hle : (outN E V w).card≤(outN D V w).card := card_le_card (by
    intro x hx
    exact mem_outN.mpr ⟨(mem_outN.mp hx).1,hED w x (mem_outN.mp hx).2⟩)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left q hle) 1).trans_lt hdeg

/-- A q-free single-excess profile cannot have base degree one. -/
theorem qfree_single_excess_base_ge_two {q r : ℕ} (hq : 1≤q) (hr : 1≤r)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (h : V)
    (hn : V.card=q*r+1) (hdh : (outN D V h).card=r+1)
    (hdegree : ∀ i : V, i≠h → (outN D V i).card=r) : 2≤r := by
  by_contra hlt
  have he : r=1 := by omega
  subst r
  have hmin : ∀ x∈V, 1≤(outN D V x).card := by
    intro x hx
    by_cases hh : (⟨x,hx⟩ : V)=h
    · have hv : x=(h : ℕ) := congrArg Subtype.val hh
      rw [hv,hdh]; omega
    · rw [hdegree ⟨x,hx⟩ hh]
  have hh := (dt_reg hq (ball_q_one q hq) hf hmin hn).1 h h.property
  omega

/-- The actual edited graph is the only safety premise. No saturation,
arc-criticality, or single-excess profile is required for this master. -/
theorem threshold_deletion_add_negative_reverse {q r : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) (h w a b : V)
    (hhw : D h w=true) (ht : (q : ℝ)*H w h=1)
    (hn : V.card=q*r+1) (hwin : (inN D V w).card=r)
    (hwb : w≠b) (hab : ¬ eraseArc D h w a b=true)
    (hf : QFree (insertArc (eraseArc D h w) a b) V q) :
    QFree (insertArc (eraseArc D h w) a b) V q ∧
    ¬ SmallRow q (fun x y => insertArc (eraseArc D h w) a b y x) V ∧
    1+q*(inN (insertArc (eraseArc D h w) a b) V w).card<V.card := by
  let G := eraseArc D h w
  let K := insertArc G a b
  obtain ⟨p,hp,hpm,hpc,_⟩ := exact_arc_threshold_pair hq hH h w hhw ht
  have hfeas : ∀ x∈V, mass V p≤row q (fun x y => G y x) V p x := by
    intro x hx
    change mass V p≤col q G V p x
    rw [hpm,hpc x hx]
  have hbad : ¬ SmallRow q (fun x y => K y x) V := by
    exact positive_feasible_extension_not_smallRow hq
      (D := fun x y => G y x) (fun x _ y _ he => insertArc_mono G a b y x he)
      p hp hfeas b.property a.property hab (by simp [K,insertArc])
  have hwbN : (w : ℕ)≠b := fun he => hwb (Subtype.ext he)
  have hinK : inN K V w=(inN D V w).erase h := by
    ext x
    simp [inN,K,G,insertArc,eraseArc,hwbN,and_comm,and_left_comm,and_assoc]
  have hdegree : (inN K V w).card=r-1 := by
    rw [hinK,card_erase_of_mem (mem_inN.mpr ⟨h.property,hhw⟩),hwin]
  have hr : 1≤r := by
    rw [← hwin]
    exact card_pos.mpr ⟨h,mem_inN.mpr ⟨h.property,hhw⟩⟩
  refine ⟨hf,hbad,?_⟩
  change 1+q*(inN K V w).card<V.card
  rw [hdegree,hn]
  have he : q*(r-1)+q=q*r := by
    nlinarith [Nat.sub_add_cancel hr]
  omega

/-- Nonsaturation supplies a safe missing arc; at least three heads allow
the deleted head to avoid both the incoming excess and the new target. -/
theorem single_excess_repair_negative_reverse {q r : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (hr : 2≤r) (h g : V)
    (hn : V.card=q*r+1) (hdh : (outN D V h).card=r+1)
    (hcol : ∀ i : V, H i h=1/(q : ℝ))
    (hin : ∀ i : V, i≠g → (inN D V i).card=r)
    (hns : ¬ Sat q D V) :
    ∃ K : CH.Digraph, QFree K V q ∧ ¬ SmallRow q (fun x y => K y x) V ∧
      ∃ w∈V, 1+q*(inN K V w).card<V.card := by
  classical
  unfold BRsub.Sat at hns
  push Not at hns
  obtain ⟨b,hb,a,ha,hab,hsafe⟩ := hns
  have hthree : 2<(outN D V h).card := by omega
  have hnot : ¬ outN D V h ⊆ {g.val,b} := by
    intro hs
    have hh := (card_le_card hs).trans (card_insert_le g.val {b})
    simp only [card_singleton] at hh
    omega
  obtain ⟨w,hw,hex⟩ := not_subset.mp hnot
  have hwV := (mem_outN.mp hw).1
  have hhw := (mem_outN.mp hw).2
  have hex' : w≠g.val ∧ w≠b := by
    simpa only [mem_insert,mem_singleton,not_or] using hex
  let G := eraseArc D h w
  let K := insertArc G a b
  have hDK : ∀ x y, K x y=true → insertArc D a b x y=true := by
    intro x y he
    by_cases hh : x=a ∧ y=b
    · simp [insertArc,hh]
    · have heG : G x y=true := by simpa only [K,insertArc,hh,ite_false] using he
      exact insertArc_mono D a b x y (eraseArc_sub D h w x y heG)
  have hKf : QFree K V q := qfree_sub hDK (qfree_insertArc hf ⟨a,ha⟩ ⟨b,hb⟩ hsafe)
  have ht : (q : ℝ)*H ⟨w,hwV⟩ h=1 := by
    rw [hcol]
    have hq0 : (q : ℝ)≠0 := by exact_mod_cast (show q≠0 by omega)
    field_simp
  obtain ⟨_,hbad,hdegree⟩ := threshold_deletion_add_negative_reverse hq hH
    h ⟨w,hwV⟩ ⟨a,ha⟩ ⟨b,hb⟩ hhw ht hn
    (hin ⟨w,hwV⟩ (fun he => hex'.1 (congrArg Subtype.val he)))
    (fun he => hex'.2 (congrArg Subtype.val he))
    (fun he => hab (eraseArc_sub D h w a b he)) hKf
  exact ⟨K,hKf,hbad,w,hwV,hdegree⟩

end LeanCH.BR.WeightedSD
