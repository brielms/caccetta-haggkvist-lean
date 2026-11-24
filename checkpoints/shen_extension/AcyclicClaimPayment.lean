import checkpoints.shen_extension.CycleClaimLedger

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- Count the high rows on the physical cycle at a common lower price.
The turn and omission factors come from the whole set of booked cycles. -/
theorem stock_from_rows {D V q r k b c} (free : QFree D V q) (time : c+2≤q)
    (reg : OutEq r D V) (sel : Selection D V q r k b)
    (cap : ∀C∈booked sel,omissions D V C r≤c) {C} (cm : C∈booked sel)
    (high : (c+1)*2^c < (C.filter (fun v=>b<(ball D V v k).card)).card) :
    (1:ℚ)<∑v∈C,share D V (booked sel) r (fun v=>surplus b (ball D V v k).card) C v := by
  classical
  let F := booked sel
  let G := C.filter (fun v=>b<(ball D V v k).card)
  let p := fun v=>(surplus b (ball D V v k).card:ℚ)
  let cost : ℚ := ((c+1 : ℕ):ℚ)*2^c
  have pos : 0<cost := by dsimp [cost]; positivity
  have rooted H (hm : H∈F) : ∀x∈H,Rooted D V x H := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp hm
    exact sel.rooted _ (sel.assigned _ ym)
  have unit v (vm : v∈G) : 1/cost≤share D V F r p C v := by
    obtain ⟨vc,h⟩ := mem_filter.mp vm
    have hp : (1:ℚ)≤p v := by
      have hN : 1≤surplus b (ball D V v k).card := by simp [surplus,h]; omega
      dsimp [p]; exact_mod_cast hN
    have turnsCap := turns_bound (v:=v) free time rooted reg cap
    have occ : C∈through F v := mem_filter.mpr ⟨cm,vc⟩
    have tp : 0<(turns D F v).card := card_pos.mpr ⟨_,mem_image_of_mem _ occ⟩
    have denom : (0:ℚ)<((turns D F v).card:ℚ)*2^(omissions D V C r) := by positivity
    have tc : ((turns D F v).card:ℚ)≤((c+1 : ℕ):ℚ) := by exact_mod_cast turnsCap
    have pc : (2:ℚ)^(omissions D V C r)≤2^c := pow_le_pow_right₀ (by norm_num) (cap _ cm)
    have upper : ((turns D F v).card:ℚ)*2^(omissions D V C r)≤cost :=
      mul_le_mul tc pc (by positivity) (by positivity)
    unfold share
    rw [←div_eq_mul_one_div, div_div]
    exact div_le_div₀ (by positivity) hp denom upper
  have bill := sum_le_sum unit
  simp only [sum_const,nsmul_eq_mul] at bill
  have large : cost<G.card := by dsimp [cost]; exact_mod_cast high
  have worth : (1:ℚ)<(G.card:ℚ)*(1/cost) := by
    rw [←div_eq_mul_one_div]; exact (one_lt_div pos).mpr large
  have sub : ∑v∈G,share D V F r p C v ≤ ∑v∈C,share D V F r p C v :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v _ _=>by dsimp [share,p]; positivity)
  exact (worth.trans_le bill).trans_le sub

/-- Geometry supplied on one acyclic representative. The signature names
the third shell for use at a collision with a different representative. -/
structure ClaimData (D : CH.Digraph) (V Y C : Finset ℕ) (q r u target : ℕ) : Prop where
  width : Y.card=r
  inside : C⊆Y
  loss : omissions D V C r≤1
  scores : C.card≤(C.filter (fun v=>4+target≤(ball D V v 3).card)).card+(r-C.card)*(r-q)
  single : C=Y ∨ ∃a,Y\C={a} ∧
    (((exterior D V C).card=r ∧ Y=C∪mutualExterior D V C) ∨
     ((exterior D V C).card=r-1 ∧ exterior D V C=N3 D V u))

theorem claim_data {D V q r target Y} (free : QFree D V q) (reg : OutEq r D V) (hr : 0<r)
    (sel : Selection D V q r 3 (3*r)) (ym : Y∈classes D V 3 (3*r))
    (regime : Room q r) (dag : QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card)
    (one : r≤q+2) (fit : r+1<2*(q-1)) (dist : (r-(q+1))*(r-q)+3≤q)
    (guard : ScoreRoom q r (r-1) target) :
    ClaimData D V Y (sel.pay Y) q r (sel.rep Y) target := by
  classical
  let u := sel.rep Y
  let C := sel.pay Y
  have entry := sel.represents Y ym
  have uv := rep_native sel ym
  have low := (mem_filter.mp (mem_filter.mp entry).1).2
  have key := rep_key sel ym
  have cc := sel.length _ (sel.assigned Y ym)
  have rc := sel.rooted _ (sel.assigned Y ym)
  have hq := regime.1
  have info := selected_stock free reg hr sel ym regime dag (by omega) dist guard
  dsimp only at info
  obtain ⟨cy,zsize,count,paid⟩ := info
  have width : Y.card=r := by
    obtain ⟨_,a,b,c,d,_⟩ := regime
    have cap := low_third_second free hq reg uv a b c d low
    have h1 := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    rw [reg _ uv] at h1
    have h2 := @card_B2 D V (sel.rep Y)
    rw [key] at h2
    have rank := reg _ uv
    obtain ⟨s,sm,ss⟩ := exists_sink dag (card_pos.mp (by omega)) le_rfl
    have inc : outN D V s⊆N2 D V (sel.rep Y) := fun z zm=>(mem_union.mp (headX (free.mono_bound (by omega : 4≤q))
      uv sm (outN_subset zm) (mem_outN.mp zm).2)).resolve_left (fun xx=>ss z xx (mem_outN.mp zm).2)
    rw [key] at inc
    have := card_le_card inc
    rw [reg _ (outN_subset sm)] at this
    omega
  have outer : exterior D V C⊆(Y\C)∪N3 D V u := by
    intro z zm
    obtain ⟨hits,off⟩ := mem_sdiff.mp zm
    obtain ⟨x,xm,arc⟩ := mem_biUnion.mp hits
    have src : x∈N2 D V u := key.symm ▸ cy xm
    rcases headY (free.mono_bound (by omega : 4≤q)) uv src (outN_subset arc) (mem_outN.mp arc).2 with early|late
    · have wy : N2 D V u=Y := key
      have nback := no_back (C:=C) free (by omega) reg uv (by exact dag) ((congrArg card wy).trans width) (by omega)
      have yy := (mem_union.mp early).resolve_left (fun xx=>nback (cy.trans wy.symm.subset) cc rc x xm z xx (mem_outN.mp arc).2)
      exact mem_union_left _ (mem_sdiff.mpr ⟨wy ▸ yy,off⟩)
    · exact mem_union_right _ late
  have exsize := (card_le_card outer).trans (card_union_le _ _)
  have sub := card_le_card cy
  have es := card_sdiff_of_subset cy
  have n2 : (N2 D V u).card=r := (congrArg card key).trans width
  have extra : (Y\C).card≤1 := by dsimp [C]; omega
  have Gsub : (C.filter (fun a=>N3 D V u⊆outN D V a))⊆C.filter (fun a=>4+target≤(ball D V a 3).card) :=
    fun a am=>mem_filter.mpr ⟨(mem_filter.mp am).1,paid a am⟩
  refine ⟨width,cy,?_,?_,?_⟩
  · change (exterior D V C).card-(r-1)≤1; change (N3 D V u).card+1=r at zsize; omega
  · have gcap := card_le_card Gsub
    change C.card≤(C.filter (fun a=>N3 D V u⊆outN D V a)).card+(r-C.card)*(r-q) at count
    exact count.trans (Nat.add_le_add_right gcap _)
  · by_cases eq : C=Y
    · exact Or.inl eq
    · have strict := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨cy,eq⟩)
      have ex : (Y\C).card=1 := by dsimp [C] at *; omega
      obtain ⟨a,oneA⟩ := card_eq_one.mp ex
      have marked : N2 D V u\C={a} := by rw [key]; exact oneA
      have data := one_extra_signature free (by omega) reg uv dag n2 (by omega) (cy.trans key.symm.subset)
        cc rc marked fit (by omega)
      refine Or.inr ⟨a,oneA,?_⟩
      change _ ∨ _ at data
      exact data.imp_left (fun h=>⟨h.1,key.symm.trans h.2⟩)


/-- Distinct second shells using the same physical cycle leave two missed directions. -/
theorem separate_claims {D V q r C u v target Y Z} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (hr : 0<r) (uv : u∈V) (vv : v∈V)
    (ky : N2 D V u=Y) (kz : N2 D V v=Z) (ne : Y≠Z)
    (A : ClaimData D V Y C q r u target) (B : ClaimData D V Z C q r v target) :
    v∉ball D V u 3 := by
  rcases A.single with eq|⟨a,one,left⟩
  · exact (ne (eq_of_subset_of_card_le (eq ▸ B.inside) (by rw [A.width,B.width]))).elim
  rcases B.single with eq|⟨b,two,right⟩
  · exact (ne (eq_of_subset_of_card_le (eq ▸ A.inside) (by rw [A.width,B.width])).symm).elim
  subst Y
  subst Z
  exact (collision_holes free hq reg uv vv ne A.inside B.inside one two left right hr).1

theorem cyclic_representative {D V q r target} (free : QFree D V q) (reg : OutEq r D V)
    (hr : 0<r) (live : V.Nonempty) (regime : Room q r) (mixed : ShellBankOrders.MixedRoom q r)
    (size : V.card≤2*(3*r)) (one : r≤q+2) (fit : r+1<2*(q-1))
    (dist : (r-(q+1))*(r-q)+3≤q) (guard : ScoreRoom q r (r-1) target)
    (pay : 3*r<4+target) (stock : 4+(r-(q+1))*(r-q)<q+1)
    (sel : Selection D V q r 3 (3*r)) :
    ∃Y∈classes D V 3 (3*r),¬QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card := by
  classical
  by_contra! ac
  have hq := regime.1
  have data Y (ym : Y∈classes D V 3 (3*r)) :=
    claim_data free reg hr sel ym regime (ac Y ym) one fit dist guard
  have cap C (cm : C∈booked sel) : omissions D V C r≤1 := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    exact (data Y ym).loss
  apply unit_claim_exit free (by omega) reg (by omega)
    (fun v vm=>by have := ShellBankOrders.mixed_third free mixed reg vm; omega) size live sel
  · intro Y ym
    exact (acyclic_class_debit free reg hr sel ym regime (ac Y ym) (by omega) dist).2
  · intro Y ym Z zm ne eq
    have bdata := data Z zm
    rw [←eq] at bdata
    exact separate_claims free (by omega) reg hr (rep_native sel ym) (rep_native sel zm)
      (rep_key sel ym) (rep_key sel zm) ne (data Y ym) bdata
  · intro C cm
    apply stock_from_rows free (by omega : 1+2≤q) reg sel cap cm
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    have scores := (data Y ym).scores
    have cc := sel.length _ (sel.assigned _ ym)
    have delta := Nat.mul_le_mul_right (r-q) (show r-(sel.pay Y).card≤r-(q+1) by omega)
    have sub : (sel.pay Y).filter (fun v=>4+target≤(ball D V v 3).card)⊆
        (sel.pay Y).filter (fun v=>3*r<(ball D V v 3).card) :=
      fun a am=>mem_filter.mpr ⟨(mem_filter.mp am).1,pay.trans_le (mem_filter.mp am).2⟩
    have cnt := card_le_card sub
    change 4 < _
    omega


/-- On every exact thinning and for every choice of representatives, the
low class and cycle below share the same root on that thinning. -/
structure CyclicOrigin (p : CHRuleCatalog.Input) : Prop where
  on_graph : ∀q≤CHRuleCatalog.cutoff p,∀target,
    Room q p.s → ShellBankOrders.MixedRoom q p.s → p.n≤2*(3*p.s) → p.s≤q+2 →
    p.s+1<2*(q-1) → (p.s-(q+1))*(p.s-q)+3≤q →
    ScoreRoom q p.s (p.s-1) target → 3*p.s<4+target → 4+(p.s-(q+1))*(p.s-q)<q+1 →
    ∀F,(∀a b,F a b=true → p.D a b=true) → OutEq p.s F (range p.n) →
      ∀sel : Selection F (range p.n) q p.s 3 (3*p.s),
      ∃Y∈classes F (range p.n) 3 (3*p.s),
        ∃C⊆outN F (range p.n) (sel.rep Y),q<C.card ∧ ∀v∈C,Rooted F (range p.n) v C

theorem cyclic_origin_on_bad {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) : CyclicOrigin p := by
  constructor
  intro q cut target regime mixed size one fit dist guard pay stock F sub reg sel
  have free := qfree_sub sub ((qfree_of_noShort bad.loopless bad.missing).mono_bound cut)
  obtain ⟨Y,ym,cyc⟩ := cyclic_representative free reg bad.degree_pos ⟨0,mem_range.mpr bad.order⟩
    regime mixed (by simpa using size) one fit dist guard pay stock sel
  exact ⟨Y,ym,actual_cycle free (by have := regime.1; omega) outN_subset cyc⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] cyclic_origin_on_bad
#print axioms cyclic_origin_on_bad

#print axioms cyclic_representative

#print axioms claim_data
#print axioms stock_from_rows
end LeanCH.BR.LowShellCycleSelection
