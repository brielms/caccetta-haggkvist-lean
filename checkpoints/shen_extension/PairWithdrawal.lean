import checkpoints.shen_extension.LightColumnPacking

namespace LeanCH.BR.Closure.PairWithdrawal
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights ShenPrimeTransition
open MandatoryTwoStep RootedSplice LightColumnPacking DeleteRepair

private abbrev mass (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℕ) (p : ℕ) :=
  ∑ z ∈ outN D V p, w z

private theorem score_eq {q D V w p} : score q D V w p = w p + q*mass D V w p := by
  simp only [score,mass,outN,sum_filter]

/-- Minimality also tests nonnegative weights on a smaller support, provided
at least one vertex retains positive weight. The failing row itself survives. -/
private theorem failed_row {q n} (X : Model q n) {E U w} (safe : QFree E U q)
    (small : U.card < X.V.card) (budget : (∑z∈U,w z) ≤ n)
    (live : ∃ z∈U, 0 < w z) :
    ∃ p∈U, 0 < w p ∧ score q E U w p ≤ ∑z∈U,w z := by
  classical
  let S := U.filter fun z => 0 < w z
  have sub : S ⊆ U := filter_subset _ _
  have zero (z) (zu : z∈U) (zs : z∉S) : w z=0 := by
    by_contra! h
    exact zs (mem_filter.mpr ⟨zu,by omega⟩)
  have tot : (∑z∈S,w z) = ∑z∈U,w z := sum_subset sub zero
  obtain ⟨z,zu,pos⟩ := live
  have fail : ¬Strict q E S w := fun h => ((card_le_card sub).trans_lt small).not_ge
    (X.minimal E S w ⟨z,mem_filter.mpr ⟨zu,pos⟩⟩ (safe.mono_set sub)
      (fun _ hz => (mem_filter.mp hz).2) (tot.le.trans budget) h)
  rw [nat_strict] at fail
  push Not at fail
  obtain ⟨p,ps,low⟩ := fail
  have row : score q E S w p = score q E U w p := by
    unfold score
    rw [sum_subset sub (fun i hi miss => by simp [zero i hi miss])]
  exact ⟨p,sub ps,(mem_filter.mp ps).2,row ▸ tot ▸ low⟩

private theorem anchor_mem {D V x} : x∈closedN D V x := mem_insert_self _ _
private theorem out_mem {D V x y} (yv : y∈V) (xy : D x y=true) : y∈closedN D V x :=
  mem_insert_of_mem (mem_union_left _ (mem_outN.mpr ⟨yv,xy⟩))
private theorem in_mem {D V x p} (pv : p∈V) (px : D p x=true) : p∈closedN D V x :=
  mem_insert_of_mem (mem_union_right _ (mem_inN.mpr ⟨pv,px⟩))

/-- Remove x and j, bypass j, and withdraw integral amounts from heads of x.
Both anchors' parent rows are paid. A surviving third row sees enough debit,
including its own withdrawal, to pay the total loss and its old strict margin. -/
theorem partial_withdrawal {q n} (X : Model q n) (hq : 2≤q) {x j}
    (xv : x∈X.V) (jv : j∈X.V) (ne : x≠j)
    (xj : Forces X.D X.V q x j) (jx : Forces X.D X.V q j x)
    (separate : Disjoint (closedN X.D X.V x) (closedN X.D X.V j))
    (heads : (q-2)*X.weights x ≤ ∑z∈outN X.D X.V j,X.weights z)
    (nonempty : (outN X.D X.V j).Nonempty)
    (δ : ℕ → ℕ) (cap : ∀ z∈X.V, δ z≤X.weights z)
    (support : ∀ z∈X.V, 0<δ z → X.D x z=true)
    (bill : (∑z∈X.V,δ z)+X.weights j+X.weights x = q*X.weights x) :
    ∃p∈(X.V.erase x).erase j, δ p<X.weights p ∧ X.D p x=false ∧ X.D p j=false ∧
      score q X.D X.V X.weights p+q*X.weights x ≤
        (∑z∈X.V,X.weights z)+δ p+q*(∑z∈outN X.D X.V p,δ z) := by
  classical
  let W := X.V.erase x
  change (q-2)*X.weights x ≤ mass X.D X.V X.weights j at heads
  let U := W.erase j
  let O := outN X.D U j
  let E := repair X.D (inN X.D U j) (fun _ => O)
  let w := fun z => X.weights z-δ z
  have jw : j∈W := mem_erase.mpr ⟨ne.symm,jv⟩
  have uv : U⊆X.V := (erase_subset j W).trans (erase_subset x X.V)
  have jU {z} (hz : z∈outN X.D X.V j) : z∈U := by
    obtain ⟨zv,jz⟩ := mem_outN.mp hz
    exact mem_erase.mpr ⟨fun eq => loopfree X.free (by omega) jv (eq ▸ jz),
      mem_erase.mpr ⟨fun eq => disjoint_left.mp separate anchor_mem (eq ▸ out_mem zv jz),zv⟩⟩
  have same : O = outN X.D X.V j := by
    ext z
    exact ⟨fun hz => mem_outN.mpr ⟨uv (mem_outN.mp hz).1,(mem_outN.mp hz).2⟩,
      fun hz => mem_outN.mpr ⟨jU hz,(mem_outN.mp hz).2⟩⟩
  have keep {z} (zv : z∈X.V) (miss : ¬X.D x z=true) : δ z=0 := by
    by_contra! pos
    exact miss (support z zv (by omega))
  have dx := keep xv (loopfree X.free (by omega) xv)
  have dj := keep jv (fun edge => disjoint_left.mp separate (out_mem jv edge) anchor_mem)
  have stable {z} (hz : z∈O) : δ z = 0 := by
    rw [same] at hz
    obtain ⟨zv,jz⟩ := mem_outN.mp hz
    exact keep zv (fun xz => disjoint_left.mp separate (out_mem zv xz) (out_mem zv jz))
  have sum2 (f : ℕ→ℕ) : (∑z∈U,f z)+f j+f x=∑z∈X.V,f z := by
    rw [sum_erase_add W f jw,sum_erase_add X.V f xv]
  have split {S : Finset ℕ} (sv : S⊆X.V) :
      (∑z∈S,w z)+(∑z∈S,δ z)=∑z∈S,X.weights z := by
    rw [←sum_add_distrib]
    exact sum_congr rfl fun z zs => Nat.sub_add_cancel (cap z (sv zs))
  have take : (∑z∈U,w z)+q*X.weights x = ∑z∈X.V,X.weights z := by
    have f := sum2 X.weights
    have g := sum2 δ
    have a := split uv
    omega
  obtain ⟨z,zout⟩ := nonempty
  have alive : ∃z∈U,0<w z :=
    ⟨z,jU zout,by simpa [w,stable (same ▸ zout)] using X.positive z (mem_outN.mp zout).1⟩
  have safe := PunctureBypass.safe hq (X.free.mono_set (erase_subset x X.V)) jw (forces_iff.mp jx)
  have less : U.card<X.V.card := (card_le_card (erase_subset _ _)).trans_lt (card_erase_lt_of_mem xv)
  obtain ⟨p,pu,wp,low⟩ := failed_row X (E:=E) (U:=U) safe less
    ((by omega : (∑z∈U,w z)≤∑z∈X.V,X.weights z).trans X.bounded) alive
  have pv := uv pu
  let A := outN X.D U p
  let G := outN E U p
  have av : A⊆X.V := fun _ za => uv (mem_outN.mp za).1
  have inc : A⊆G := fun _ za => mem_outN.mpr ⟨(mem_outN.mp za).1,repair_old (mem_outN.mp za).2⟩
  have gift :
      (∑z∈A,w z)+(if X.D p j=true then mass X.D X.V X.weights j else 0) ≤ ∑z∈G,w z := by
    by_cases pj : X.D p j=true
    · have pp := mem_inN.mpr (show p∈U ∧ X.D p j=true from ⟨pu,pj⟩)
      have og : O⊆G := fun _ hz => mem_outN.mpr ⟨(mem_outN.mp hz).1,repair_new pp hz⟩
      have dis : Disjoint A O := by
        apply disjoint_left.mpr
        intro y ya yo
        have miss := missing_arc X hq jw pv (uv (mem_outN.mp yo).1) pj (mem_outN.mp yo).2 (forces_iff.mp jx)
        exact Bool.noConfusion (miss.symm.trans (mem_outN.mp ya).2)
      have gain := sum_le_sum_of_subset_of_nonneg (f:=w) (union_subset inc og) (by intros;omega)
      rw [sum_union dis] at gain
      have kept : (∑z∈O,w z)=mass X.D X.V X.weights j := by
        unfold mass
        rw [←same]
        exact sum_congr rfl (fun z hz => by simp [w,stable hz])
      simpa [pj,kept] using gain
    · simpa [pj] using sum_le_sum_of_subset_of_nonneg (f:=w) inc (by intros;omega)
  have oldsplit : (∑z∈A,X.weights z)+(if X.D p j=true then X.weights j else 0)+
      (if X.D p x=true then X.weights x else 0) = mass X.D X.V X.weights p := by
    simpa only [A,mass,outN,sum_filter] using sum2 (fun z => if X.D p z=true then X.weights z else 0)
  have ds : (∑z∈A,δ z)=mass X.D X.V δ p := by
    simpa only [A,mass,outN,sum_filter,dj,dx,ite_self,Nat.add_zero] using
      sum2 (fun z => if X.D p z=true then δ z else 0)
  have sA := split av
  rw [ds] at sA
  have self : w p+δ p=X.weights p := Nat.sub_add_cancel (cap p pv)
  let H := ∑z∈X.V,δ z
  have dcap : mass X.D X.V δ p ≤ H :=
    sum_le_sum_of_subset_of_nonneg (fun _ hz => (mem_outN.mp hz).1) (by intros;omega)
  have algebra : score q X.D X.V X.weights p+q*X.weights x+
      q*(if X.D p j=true then mass X.D X.V X.weights j else 0) ≤
      (∑z∈X.V,X.weights z)+δ p+q*mass X.D X.V δ p+
      q*(if X.D p j=true then X.weights j else 0)+q*(if X.D p x=true then X.weights x else 0) := by
    rw [score_eq] at low ⊢
    change w p+q*(∑z∈G,w z)≤_ at low
    have mulgift := Nat.mul_le_mul_left q gift
    have mulold := congrArg (q * ·) oldsplit
    have mulsplit := congrArg (q * ·) sA
    simp only [Nat.mul_add] at mulgift mulold mulsplit
    omega
  have high := nat_strict.mp X.strict p pv
  have nopx : X.D p x=false := by
    apply Bool.eq_false_iff.mpr
    intro px
    have pj : X.D p j=false := Bool.eq_false_iff.mpr (fun edge =>
      disjoint_left.mp separate (in_mem pv px) (in_mem pv edge))
    have d0 := keep pv (fun xp => X.free x 2 (by decide) hq (.step pv xp (.step xv px (.refl _))))
    have none : mass X.D X.V δ p=0 := by
      apply sum_eq_zero
      intro y yh
      obtain ⟨yv,py⟩ := mem_outN.mp yh
      exact keep yv (fun xy => Bool.noConfusion ((missing_arc X hq (mem_erase.mpr ⟨ne,xv⟩) pv yv
        px xy (forces_iff.mp xj)).symm.trans py))
    simp only [px,pj,Bool.false_eq_true,ite_true,ite_false,d0,none,Nat.mul_zero,Nat.add_zero] at algebra
    omega
  have nopj : X.D p j=false := by
    apply Bool.eq_false_iff.mpr
    intro pj
    have d0 := keep pv (fun xp => disjoint_left.mp separate (out_mem pv xp) (in_mem pv pj))
    have decomp : (q-2)*X.weights x + X.weights x + X.weights x=q*X.weights x := by
      rw [←Nat.succ_mul,←Nat.succ_mul]
      congr 1
      omega
    have costs : H+X.weights j ≤ X.weights x+mass X.D X.V X.weights j := by
      change (∑z∈X.V,δ z)+X.weights j≤_
      omega
    have scaled := Nat.mul_le_mul_left q ((Nat.add_le_add_right dcap (X.weights j)).trans costs)
    rw [Nat.mul_add,Nat.mul_add] at scaled
    simp only [pj,nopx,d0,Bool.false_eq_true,ite_true,ite_false,Nat.mul_zero,Nat.add_zero] at algebra
    omega
  simp only [nopx,nopj,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero] at algebra
  exact ⟨p,pu,by dsimp [w] at wp; omega,nopx,nopj,algebra⟩

/-- Allocate an exact integral debit under individual capacities. -/
private theorem allocate (S : Finset ℕ) (w : ℕ → ℕ) (k : ℕ) (room : k≤∑z∈S,w z) :
    ∃ δ : ℕ→ℕ, (∀ z,δ z≤w z) ∧ (∀ z,0<δ z → z∈S) ∧ (∑z∈S,δ z)=k := by
  classical
  induction k with
  | zero => exact ⟨fun _ => 0,fun _ => Nat.zero_le _,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨δ,cap,supp,used⟩ := ih (by omega)
    have left : ∃ z∈S,δ z<w z := by
      by_contra! full
      have bound := sum_le_sum full
      omega
    obtain ⟨z,zs,fresh⟩ := left
    let more := fun v => δ v+(if v=z then 1 else 0)
    refine ⟨more,?_,?_,?_⟩
    · intro v
      by_cases same : v=z
      · subst v; simpa [more] using fresh
      · simpa [more,same] using cap v
    · intro v pos
      by_cases same : v=z
      · exact same ▸ zs
      · exact supp v (by simpa [more,same] using pos)
    · simp [more,sum_add_distrib,zs,used]

/-- Every admissible withdrawal from heads of a minimum anchor forces a
positive third row with the exact debit inequality, on the same model. -/
theorem minimum_bill {q n} (X : Model q n) (hq : 2≤q) {x j}
    (xv : x∈X.V) (jv : j∈X.V) (ne : x≠j)
    (xj : Forces X.D X.V q x j) (jx : Forces X.D X.V q j x)
    (minimum : ∀z∈X.V,X.weights x≤X.weights z) (size : q*(q-1)+1≤X.V.card)
    (δ : ℕ→ℕ) (cap : ∀z∈X.V,δ z≤X.weights z)
    (support : ∀z∈X.V,0<δ z → X.D x z=true)
    (bill : (∑z∈X.V,δ z)+X.weights j+X.weights x=q*X.weights x) :
    ∃p∈(X.V.erase x).erase j, δ p<X.weights p ∧ X.D p x=false ∧ X.D p j=false ∧
      score q X.D X.V X.weights p+q*X.weights x ≤
        (∑z∈X.V,X.weights z)+δ p+q*(∑z∈outN X.D X.V p,δ z) := by
  have light := ((PunctureReceiverFrontier.classify X hq xv (mem_erase.mpr ⟨ne.symm,jv⟩)
    minimum size).resolve_left (forces_iff.mp jx)).1
  have sep := disjoint_neighbourhoods X hq xv jv ne minimum size
    (Nat.le_mul_of_pos_left _ (by omega)) light.le (Or.inl xj)
  have floor := PunctureWeightCoverage.flow_floor X jv minimum size
  have nonempty : (outN X.D X.V j).Nonempty := by
    by_contra empty
    rw [not_nonempty_iff_eq_empty.mp empty,sum_empty] at floor
    omega
  exact partial_withdrawal X hq xv jv ne xj jx sep
    ((Nat.mul_le_mul_right (X.weights x) (by omega : q-2≤q-1)).trans floor.le)
    nonempty δ cap support bill

/-- Every other anchor of the same cycle-incidence class as a minimum x has
weight strictly below (q−2) times the minimum. -/
theorem equal_mate_weight {q n} (X : Model q n) (hq : 2≤q) {x j}
    (xv : x∈X.V) (jv : j∈X.V) (ne : x≠j)
    (xj : Forces X.D X.V q x j) (jx : Forces X.D X.V q j x)
    (minimum : ∀z∈X.V,X.weights x≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    X.weights j < (q-2)*X.weights x := by
  classical
  by_contra! large
  have light := ((PunctureReceiverFrontier.classify X hq xv (mem_erase.mpr ⟨ne.symm,jv⟩)
    minimum size).resolve_left (forces_iff.mp jx)).1
  have floor := PunctureWeightCoverage.flow_floor X xv minimum size
  let H := (q-1)*X.weights x-X.weights j
  let S := outN X.D X.V x
  have billH : H+X.weights j+X.weights x=q*X.weights x := by
    dsimp [H]
    rw [Nat.sub_add_cancel light.le,←Nat.succ_mul]
    congr 1
    omega
  have smallH : H≤X.weights x := by
    have step : (q-2)*X.weights x+X.weights x=(q-1)*X.weights x := by
      rw [←Nat.succ_mul]
      congr 1
      omega
    dsimp [H]
    omega
  obtain ⟨δ,cap,supp,total⟩ := allocate S X.weights H
    ((Nat.sub_le ((q-1)*X.weights x) (X.weights j)).trans floor.le)
  have sub : S⊆X.V := fun _ zs => (mem_outN.mp zs).1
  have sumδ : (∑z∈X.V,δ z)=H := by
    rw [←total]
    exact (sum_subset sub (fun z _ no => by
      by_contra! pos
      exact no (supp z (by omega)))).symm
  obtain ⟨p,pu,_,_,_,charge⟩ := minimum_bill X hq xv jv ne xj jx minimum size δ
    (fun z _ => cap z) (fun z _ pos => (mem_outN.mp (supp z pos)).2) (sumδ ▸ billH)
  have pv := mem_of_mem_erase (mem_of_mem_erase pu)
  have self : p∉outN X.D X.V p := fun e => loopfree X.free (by omega) pv (mem_outN.mp e).2
  have subset : insert p (outN X.D X.V p)⊆X.V := insert_subset pv fun _ hz => (mem_outN.mp hz).1
  have closed := sum_le_sum_of_subset_of_nonneg (f:=δ) subset (by intros;omega)
  rw [sum_insert self,sumδ] at closed
  have mult := Nat.mul_le_mul_left q (closed.trans smallH)
  rw [Nat.mul_add] at mult
  have selfbound : δ p ≤ q*δ p := Nat.le_mul_of_pos_left _ (by omega)
  have high := nat_strict.mp X.strict p pv
  omega

/-- Uniform entry from the graph order n and the degree lower bound r. -/
theorem from_input {n r q D} (hn : 0<n) (hq : 2≤q) (order : n≤q*r)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (no : ¬CH.HasDirectedCycleAtMost D n q) :
    ∃ X : Model q n, q*(q-1)+1≤X.V.card →
      ∀ x∈X.V, (∀z∈X.V,X.weights x≤X.weights z) → ∀j∈X.V, x≠j →
        Forces X.D X.V q x j → Forces X.D X.V q j x → X.weights j<(q-2)*X.weights x := by
  obtain ⟨X⟩ := normalize hq hn order loop degree no
  exact ⟨X,fun size _ xv minimum _ jv ne xj jx =>
    equal_mate_weight X hq xv jv ne xj jx minimum size⟩

#print axioms from_input
#print axioms minimum_bill
#print axioms equal_mate_weight
#print axioms partial_withdrawal
end LeanCH.BR.Closure.PairWithdrawal
