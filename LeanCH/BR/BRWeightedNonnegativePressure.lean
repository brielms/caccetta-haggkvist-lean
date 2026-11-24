import LeanCH.BR.BRFiniteNonnegativePressure
import LeanCH.BR.BRWeightedUniformInverse
import LeanCH.BR.BRWeightedDeletionThreshold
import LeanCH.BR.BRWeightedRepair

/-! Actual native arc-core dichotomy and boundary deletions. The deletion
graphs are q-free and SmallRow but explicitly not saturated. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix BRq2 BRq3 BR45 BRsub FiniteCutInverse ThresholdUnit WeightedArithmetic
open scoped Matrix

theorem arc_core_pressure_dichotomy {q : ℕ} (hq : 3 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hV : V.Nonempty)
    (hf : QFree D V q) (hcritical : ArcCritical q D V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H) :
    (∃ v ∈ V, 1+q*(outN D V v).card < V.card) ∨
    ∃ r : ℕ, 1 ≤ r ∧ ∃ h : V, V.card=q*r+1 ∧
      (outN D V h).card=r+1 ∧
      (∀ i : V, i≠h → (outN D V i).card=r) ∧
      ∀ i : V, H i h=1/(q : ℝ) := by
  let : Nonempty V := ⟨⟨hV.choose,hV.choose_spec⟩⟩
  by_cases hn : ∃ v ∈ V, 1+q*(outN D V v).card < V.card
  · exact Or.inl hn
  push Not at hn
  rcases NonnegativePressure.classify hq (fun i j : V => D i j) hH
    (by intro i j; exact realMatrix_entry q D V i j)
    (inverse_arc_charge hcritical hH)
    (fun i => by simpa only [Fintype.card_coe,subtype_out_card] using hn i i.property)
    with ⟨hdeg,hcard⟩ | hs
  · have hnq : V.card ≤ q := by simpa only [Fintype.card_coe] using hcard
    obtain ⟨v,hv,hsink⟩ := exists_sink hf hV hnq
    have he : outN D V v=∅ := eq_empty_iff_forall_notMem.mpr (by
      intro j hj; exact hsink j (mem_outN.mp hj).1 (mem_outN.mp hj).2)
    have hh := hdeg ⟨v,hv⟩
    rw [subtype_out_card,he,card_empty] at hh
    omega
  · exact Or.inr (by simpa only [Fintype.card_coe,subtype_out_card] using hs)

/-- Real exact unit columns of an integer graph matrix are rational. -/
theorem real_unit_column_rational {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (x : V → ℝ)
    (hx : x ᵥ* realMatrix q D V = fun _ => 1) :
    ∃ p : V → ℚ, (∀ i, (p i : ℝ)=x i) ∧
      p ᵥ* rationalMatrix q (adjacencyMatrix D V)=fun _ => 1 := by
  let A := adjacencyMatrix D V
  obtain ⟨p,hp⟩ := rational_surjective hq A.transpose (fun _ => 1)
  have ht : rationalMatrix q A.transpose=(rationalMatrix q A).transpose := by
    ext i j
    simp [rationalMatrix,closedMatrix,Matrix.transpose_apply,eq_comm]
  rw [ht,Matrix.mulVec_transpose] at hp
  have hdet : (realMatrix q D V).det ≠ 0 := by
    change ((Rat.castHom ℝ).mapMatrix (rationalMatrix q A)).det ≠ 0
    rw [← RingHom.map_det]
    change ((rationalMatrix q A).det : ℝ)≠0
    exact_mod_cast rational_det_ne_zero hq A
  have hu : IsUnit (realMatrix q D V) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hpR : (fun i => (p i : ℝ)) ᵥ* realMatrix q D V=fun _ => 1 := by
    funext i
    have hh := congrFun hp i
    change (∑ j, p j*rationalMatrix q A j i)=1 at hh
    change (∑ j, (p j : ℝ)*(rationalMatrix q A j i : ℝ))=1
    exact_mod_cast hh
  have he := (Matrix.vecMul_injective_iff_isUnit.mpr hu) (hpR.trans hx.symm)
  exact ⟨p,fun i => congrFun he i,hp⟩

theorem exact_arc_threshold_pair {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) (h v : V) (hav : D h v=true)
    (ht : (q : ℝ)*H v h=1) :
    ∃ p : ℕ → ℚ, (∀ i ∈ V, 0 < p i) ∧ mass V p=1 ∧
      (∀ i ∈ V, col q (eraseArc D h v) V p i=1) ∧
      (∀ i : V, (p i : ℝ)=inverseRowLaw H v i) := by
  let E := eraseArc D h v
  have hrep : ∀ i j : V, realMatrix q E V i j =
      (if i=j then 1 else 0)+(q : ℝ)*(adjacencyMatrix E V i j : ℝ) := by
    intro i j
    rw [realMatrix_entry]
    simp only [adjacencyMatrix]
    split_ifs <;> norm_num
  have hd : ∀ i j : V, realMatrix q D V i j-realMatrix q E V i j=
      if i=h ∧ j=v then q else 0 := by
    intro i j
    simpa only [Nat.cast_ite,Nat.cast_zero] using realMatrix_erase_difference h v hav i j
  obtain ⟨hpos,hm,hcol,_⟩ := exact_threshold_unit hq (adjacencyMatrix E V) hH hrep h v hd ht
  obtain ⟨p,hp,hpc⟩ := real_unit_column_rational hq (inverseRowLaw H v) (funext hcol)
  refine ⟨extendWeight V p,?_,?_,?_,?_⟩
  · intro i hi
    rw [extendWeight_on V p ⟨i,hi⟩]
    have he := hp ⟨i,hi⟩
    have hh := hpos ⟨i,hi⟩
    rw [← he] at hh
    exact_mod_cast hh
  · rw [mass_extendWeight]
    have hh : ∑ i, (p i : ℝ)=1 := by simp_rw [hp]; exact hm
    exact_mod_cast hh
  · intro i hi
    rw [col_extendWeight q E V p ⟨i,hi⟩]
    exact congrFun hpc ⟨i,hi⟩
  · intro i
    rw [extendWeight_on]
    exact hp i

theorem erase_actual_arc_not_sat {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (h v : V) (hav : D h v=true) : ¬ Sat q (eraseArc D h v) V := by
  intro hs
  have hb := hs v v.property h h.property (by simp [eraseArc])
  obtain ⟨_,l,hl,hw⟩ := mem_ball.mp hb
  have hw' := walk_mono_graph_on (fun x _ y _ hxy => eraseArc_sub D h v x y hxy) hw v.property
  exact no_back_arc hf v.property (mem_ball.mpr ⟨h.property,l,hl,hw'⟩)
    (by omega : q-1+1 ≤ q) hav

theorem single_excess_deletion_pair {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hcritical : ArcCritical q D V) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) {r : ℕ} (h : V)
    (hn : V.card=q*r+1) (hdh : (outN D V h).card=r+1)
    (hdegree : ∀ i : V, i≠h → (outN D V i).card=r)
    (hcolumn : ∀ i : V, H i h=1/(q : ℝ)) (v : V) (hav : D h v=true) :
    QFree (eraseArc D h v) V q ∧ SmallRow q (eraseArc D h v) V ∧
    ¬ Sat q (eraseArc D h v) V ∧
    (∀ i ∈ V, row q (eraseArc D h v) V (fun _ => 1/(V.card : ℚ)) i=1) ∧
    mass V (fun _ => 1/(V.card : ℚ))=1 ∧
    (∀ i ∈ V, 0 < (1/(V.card : ℚ))) ∧
    ∃ p : ℕ → ℚ, (∀ i ∈ V, 0 < p i) ∧ mass V p=1 ∧
      (∀ i ∈ V, col q (eraseArc D h v) V p i=1) ∧
      (∀ i : V, (p i : ℝ)=inverseRowLaw H v i) := by
  have hn0 : V.card≠0 := by omega
  have hnR : (V.card : ℚ)≠0 := by exact_mod_cast hn0
  have hqR : (q : ℝ)≠0 := by exact_mod_cast (show q≠0 by omega)
  have ht : (q : ℝ)*H v h=1 := by rw [hcolumn]; field_simp
  have hdel (i : ℕ) (hi : i∈V) : (outN (eraseArc D h v) V i).card=r := by
    by_cases he : i=h
    · subst i
      have hs : outN (eraseArc D h v) V h=(outN D V h).erase v := by
        ext j
        simp [outN,eraseArc,and_comm,and_left_comm,and_assoc]
      rw [hs,card_erase_of_mem (mem_outN.mpr ⟨v.property,hav⟩),hdh]
      omega
    · have hs : outN (eraseArc D h v) V i=outN D V i := by
        ext j
        simp [outN,eraseArc,he]
      rw [hs]
      exact hdegree ⟨i,hi⟩ (fun heq => he (congrArg Subtype.val heq))
  refine ⟨qfree_sub (eraseArc_sub D h v) hf,hcritical h h.property v v.property hav,
    erase_actual_arc_not_sat (by omega) hf h v hav,?_,?_,?_,
    exact_arc_threshold_pair hq hH h v hav ht⟩
  · intro i hi
    have ho : outW (eraseArc D h v) V (fun _ => 1/(V.card : ℚ)) i =
        (r : ℚ)/(V.card : ℚ) := by
      unfold outW
      rw [← sum_filter]
      simp only [sum_const,nsmul_eq_mul]
      change ((outN (eraseArc D h v) V i).card : ℚ)*(1/(V.card : ℚ))=_
      rw [hdel i hi]
      ring
    rw [row,ho]
    have hnQ : (V.card : ℚ)=(q : ℚ)*r+1 := by exact_mod_cast hn
    field_simp
    nlinarith
  · simp [mass,hnR]
  · intro i hi
    positivity

/-- Two distinct exact deletions cannot both have uniform column laws. -/
theorem two_deletions_not_both_uniform {q : ℕ} (hq : 0 < q)
    {D : CH.Digraph} {V : Finset ℕ} (h v w : V)
    (hv : D h v=true) (hw : D h w=true) (hvw : v≠w)
    (p t : ℕ → ℚ)
    (hp : ∀ i∈V, col q (eraseArc D h v) V p i=1)
    (ht : ∀ i∈V, col q (eraseArc D h w) V t i=1) :
    (¬ ∀ i∈V, p i=1/(V.card : ℚ)) ∨ (¬ ∀ i∈V, t i=1/(V.card : ℚ)) := by
  by_contra hn
  push Not at hn
  obtain ⟨hpu,htu⟩ := hn
  let a : ℕ → ℝ := fun _ => 1/(V.card : ℝ)
  have hvR : realCol q (eraseArc D h v) V a v=1 := by
    have hh := hp v v.property
    unfold col inW at hh
    rw [hpu v v.property] at hh
    have hs : (∑ u ∈ V, if eraseArc D h v u v=true then p u else 0)=
        ∑ u ∈ V, if eraseArc D h v u v=true then 1/(V.card : ℚ) else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [hpu i hi]
    rw [hs] at hh
    change 1/(V.card : ℝ)+(q : ℝ)*(∑ u ∈ V, if eraseArc D h v u v=true then 1/(V.card : ℝ) else 0)=1
    have hc := congrArg (fun z : ℚ => (z : ℝ)) hh
    push_cast at hc
    simp only [apply_ite] at hc
    push_cast at hc
    exact hc
  have hwR : realCol q (eraseArc D h w) V a v=1 := by
    have hh := ht v v.property
    unfold col inW at hh
    rw [htu v v.property] at hh
    have hs : (∑ u ∈ V, if eraseArc D h w u v=true then t u else 0)=
        ∑ u ∈ V, if eraseArc D h w u v=true then 1/(V.card : ℚ) else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [htu i hi]
    rw [hs] at hh
    change 1/(V.card : ℝ)+(q : ℝ)*(∑ u ∈ V, if eraseArc D h w u v=true then 1/(V.card : ℝ) else 0)=1
    have hc := congrArg (fun z : ℚ => (z : ℝ)) hh
    push_cast at hc
    simp only [apply_ite] at hc
    push_cast at hc
    exact hc
  have hvwN : (v : ℕ)≠w := fun he => hvw (Subtype.ext he)
  have he := realCol_eraseArc (q := q) (p := a) h.property hv (z := v)
  have he' := realCol_eraseArc (q := q) (p := a) h.property hw (z := v)
  simp only [hvR,hwR,ite_true,hvwN,ite_false,add_zero] at he he'
  have hnpos : 0 < (V.card : ℝ) := by exact_mod_cast (card_pos.mpr ⟨(h : ℕ),h.property⟩ : 0 < V.card)
  have hqpos : (0 : ℝ)<q := by exact_mod_cast hq
  have ha : 0 < a h := one_div_pos.mpr hnpos
  nlinarith

/-- Single excess gives an actual nonsaturated boundary graph whose dual is
nonuniform. The primal is uniform; neither old strict law is transferred. -/
theorem single_excess_nonuniform_deletion {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hcritical : ArcCritical q D V) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) {r : ℕ} (hr : 1 ≤ r) (h : V)
    (hn : V.card=q*r+1) (hdh : (outN D V h).card=r+1)
    (hdegree : ∀ i : V, i≠h → (outN D V i).card=r)
    (hcolumn : ∀ i : V, H i h=1/(q : ℝ)) :
    ∃ v : V, D h v=true ∧ QFree (eraseArc D h v) V q ∧
      SmallRow q (eraseArc D h v) V ∧ ¬ Sat q (eraseArc D h v) V ∧
      (∀ i∈V, row q (eraseArc D h v) V (fun _ => 1/(V.card : ℚ)) i=1) ∧
      mass V (fun _ => 1/(V.card : ℚ))=1 ∧
      (∀ i∈V, 0 < (1/(V.card : ℚ))) ∧
      ∃ p : ℕ → ℚ, (∀ i∈V, 0 < p i) ∧ mass V p=1 ∧
        (∀ i∈V, col q (eraseArc D h v) V p i=1) ∧
        (∀ i : V, (p i : ℝ)=inverseRowLaw H v i) ∧
        ¬ ∀ i∈V, p i=1/(V.card : ℚ) := by
  obtain ⟨v,hv,w,hw,hvw⟩ := one_lt_card.mp (by omega : 1 < (outN D V h).card)
  obtain ⟨hvV,hav⟩ := mem_outN.mp hv
  obtain ⟨hwV,haw⟩ := mem_outN.mp hw
  let v' : V := ⟨v,hvV⟩
  let w' : V := ⟨w,hwV⟩
  obtain ⟨hvf,hvs,hvn,hvr,hvm,hva,p,hp,hpm,hpc,hpi⟩ :=
    single_excess_deletion_pair hq hf hcritical hH h hn hdh hdegree hcolumn v' hav
  obtain ⟨hwf,hws,hwn,hwr,hwm,hwa,t,ht,htm,htc,hti⟩ :=
    single_excess_deletion_pair hq hf hcritical hH h hn hdh hdegree hcolumn w' haw
  rcases two_deletions_not_both_uniform (by omega : 0 < q) h v' w' hav haw
    (fun he => hvw (congrArg Subtype.val he)) p t hpc htc with hpn | htn
  · exact ⟨v',hav,hvf,hvs,hvn,hvr,hvm,hva,p,hp,hpm,hpc,hpi,hpn⟩
  · exact ⟨w',haw,hwf,hws,hwn,hwr,hwm,hwa,t,ht,htm,htc,hti,htn⟩

/-- Native descent alternative. The boundary witness is an actual arc
deletion with its own rational laws, and is not saturated. -/
theorem arc_core_negative_pressure_or_unequal_boundary {q : ℕ} (hq : 3 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hV : V.Nonempty)
    (hf : QFree D V q) (hcritical : ArcCritical q D V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H) :
    (∃ v∈V, 1+q*(outN D V v).card < V.card) ∨
    ∃ h v : V, D h v=true ∧ QFree (eraseArc D h v) V q ∧
      SmallRow q (eraseArc D h v) V ∧ ¬ Sat q (eraseArc D h v) V ∧
      (∀ i∈V, row q (eraseArc D h v) V (fun _ => 1/(V.card : ℚ)) i=1) ∧
      mass V (fun _ => 1/(V.card : ℚ))=1 ∧
      (∀ i∈V, 0 < (1/(V.card : ℚ))) ∧
      ∃ p : ℕ → ℚ, (∀ i∈V, 0 < p i) ∧ mass V p=1 ∧
        (∀ i∈V, col q (eraseArc D h v) V p i=1) ∧
        (∀ i : V, (p i : ℝ)=inverseRowLaw H v i) ∧
        ¬ ∀ i∈V, p i=1/(V.card : ℚ) := by
  rcases arc_core_pressure_dichotomy hq hV hf hcritical hH with hn | ⟨r,hr,h,hn,hdh,hd,hc⟩
  · exact Or.inl hn
  · exact Or.inr ⟨h,single_excess_nonuniform_deletion (by omega) hf hcritical hH hr h hn hdh hd hc⟩

/-- Explicit inverse charges transpose; no reverse induction is needed. -/
theorem arcCritical_reverse_of_commonInverse {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hcritical : ArcCritical q D V) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) : ArcCritical q (fun i j => D j i) V := by
  apply (arcCritical_iff_inverse_thresholds (commonInverse_reverse hH)).mpr
  intro i j hij
  exact inverse_arc_charge hcritical hH j i hij

/-- A single exact threshold supplies both actual rational unit laws. -/
theorem exact_arc_threshold_two_laws {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) (u v : V) (huv : D u v=true)
    (ht : (q : ℝ)*H v u=1) :
    ∃ a p : ℕ → ℚ, (∀ i∈V, 0<a i) ∧ mass V a=1 ∧
      (∀ i∈V, row q (eraseArc D u v) V a i=1) ∧
      (∀ i : V, (a i : ℝ)=inverseRowLaw H.transpose u i) ∧
      (∀ i∈V, 0<p i) ∧ mass V p=1 ∧
      (∀ i∈V, col q (eraseArc D u v) V p i=1) ∧
      (∀ i : V, (p i : ℝ)=inverseRowLaw H v i) := by
  obtain ⟨p,hp,hpm,hpc,hpi⟩ := exact_arc_threshold_pair hq hH u v huv ht
  obtain ⟨a,ha,ham,hac,hai⟩ := exact_arc_threshold_pair hq (commonInverse_reverse hH) v u huv ht
  have har : ∀ i∈V, row q (eraseArc D u v) V a i=1 := by
    simpa only [eraseArc_reverse,col,inW,row,outW] using hac
  exact ⟨a,p,ha,ham,har,hai,hp,hpm,hpc,hpi⟩

/-- Two distinct exact-threshold heads force an unequal positive unit pair
on one actual deletion. No girth, criticality, or IH is used. -/
theorem exact_star_unequal_pair {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) (u v w : V)
    (huv : D u v=true) (huw : D u w=true) (hvw : v≠w)
    (htv : (q : ℝ)*H v u=1) (htw : (q : ℝ)*H w u=1) :
    ∃ j : V, (j=v ∨ j=w) ∧ D u j=true ∧ SmallRow q (eraseArc D u j) V ∧
      ∃ a p : ℕ → ℚ, (∀ i∈V, 0<a i) ∧ mass V a=1 ∧
        (∀ i∈V, row q (eraseArc D u j) V a i=1) ∧
        (∀ i : V, (a i : ℝ)=inverseRowLaw H.transpose u i) ∧
        (∀ i∈V, 0<p i) ∧ mass V p=1 ∧
        (∀ i∈V, col q (eraseArc D u j) V p i=1) ∧
        (∀ i : V, (p i : ℝ)=inverseRowLaw H j i) ∧ ¬ ∀ i∈V, a i=p i := by
  obtain ⟨a,p,ha,ham,har,hai,hp,hpm,hpc,hpi⟩ := exact_arc_threshold_two_laws hq hH u v huv htv
  obtain ⟨b,t,hb,hbm,hbr,hbi,htt,htm,htc,hti⟩ := exact_arc_threshold_two_laws hq hH u w huw htw
  have hvs := (deletion_smallRow_iff hH u v huv).mpr htv.ge
  have hws := (deletion_smallRow_iff hH u w huw).mpr htw.ge
  by_cases hap : ∀ i∈V, a i=p i
  · have hbt : ¬ ∀ i∈V, b i=t i := by
      intro he
      apply hvw
      apply inverseRowLaw_injective hH
      funext i
      calc
        inverseRowLaw H v i = (p i : ℝ) := (hpi i).symm
        _ = (a i : ℝ) := by rw [hap i i.property]
        _ = inverseRowLaw H.transpose u i := hai i
        _ = (b i : ℝ) := (hbi i).symm
        _ = (t i : ℝ) := by rw [he i i.property]
        _ = inverseRowLaw H w i := hti i
    exact ⟨w,Or.inr rfl,huw,hws,b,t,hb,hbm,hbr,hbi,htt,htm,htc,hti,hbt⟩
  · exact ⟨v,Or.inl rfl,huv,hvs,a,p,ha,ham,har,hai,hp,hpm,hpc,hpi,hap⟩

/-- The exact-star witness stays on a genuine q-free deletion, which is
explicitly nonsaturated. Its SmallRow law is constructed, not assumed. -/
theorem exact_star_qfree_unequal_deletion {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H) (u v w : V)
    (huv : D u v=true) (huw : D u w=true) (hvw : v≠w)
    (htv : (q : ℝ)*H v u=1) (htw : (q : ℝ)*H w u=1) :
    ∃ j : V, (j=v ∨ j=w) ∧ D u j=true ∧ QFree (eraseArc D u j) V q ∧
      SmallRow q (eraseArc D u j) V ∧ ¬ Sat q (eraseArc D u j) V ∧
      ∃ a p : ℕ → ℚ, (∀ i∈V, 0<a i) ∧ mass V a=1 ∧
        (∀ i∈V, row q (eraseArc D u j) V a i=1) ∧
        (∀ i : V, (a i : ℝ)=inverseRowLaw H.transpose u i) ∧
        (∀ i∈V, 0<p i) ∧ mass V p=1 ∧
        (∀ i∈V, col q (eraseArc D u j) V p i=1) ∧
        (∀ i : V, (p i : ℝ)=inverseRowLaw H j i) ∧ ¬ ∀ i∈V, a i=p i := by
  obtain ⟨j,hj,huj,hs,hpair⟩ := exact_star_unequal_pair hq hH u v w huv huw hvw htv htw
  exact ⟨j,hj,huj,qfree_sub (eraseArc_sub D u j) hf,hs,
    erase_actual_arc_not_sat (by omega) hf u j huj,hpair⟩

end LeanCH.BR.WeightedSD
