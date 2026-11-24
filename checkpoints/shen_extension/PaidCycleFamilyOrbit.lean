import checkpoints.shen_extension.JointCycleFamilyBarrier

namespace LeanCH.BR.Closure.PaidCycleFamilyOrbit
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier
open JointCycleFamilyBarrier ShenPrimeTransition

/-- Any ordered pair of distinct members starts an orbit. A closed segment
has at least three steps, keeps the same source weights throughout, and has
an actual failed transfer and a crossing arc at each step. -/
theorem orbit {q n} (X : Model q n) {F w M A} (sub : F⊆family X)
    (wp : ∀v∈X.V,0<w v) (budget : (∑v∈X.V,w v)≤n) (strict : Strict q (graph X.D F) X.V w)
    (mf : M∈F) (af : A∈F) (ne : M≠A) :
    ∃c : ℕ→Finset ℕ,c 0=M ∧ c 1=A ∧
      (∀i,c i∈F ∧ c i≠c (i+1) ∧ ExitTo X F w (c (i+1)) (c i) (c (i+2))) ∧
      ∃i l,3≤l ∧ i+l≤F.card*F.card ∧ c (i+l)=c i ∧ c (i+l+1)=c (i+1) := by
  classical
  let P := (F ×ˢ F).filter (fun pair => pair.1≠pair.2)
  have split {p : Finset ℕ × Finset ℕ} (mem : p∈P) :
      p.1∈F ∧ p.2∈F ∧ p.1≠p.2 := ⟨(mem_product.mp (mem_filter.mp mem).1).1,
        (mem_product.mp (mem_filter.mp mem).1).2,(mem_filter.mp mem).2⟩
  have next (p) (mem : p∈P) : ∃t∈P,t.1=p.2 ∧ ExitTo X F w p.2 p.1 t.2 := by
    obtain ⟨left,right,diff⟩ := split mem
    obtain ⟨L,hit⟩ := exit_any X sub wp budget strict right left (Ne.symm diff)
    exact ⟨(p.2,L),mem_filter.mpr ⟨mem_product.mpr ⟨right,hit.1⟩,Ne.symm hit.2.1⟩,rfl,hit⟩
  choose! g gp edge using next
  let f (i : ℕ) := g^[i] (M,A)
  have stay (i) : f i∈P := by
    induction i with
    | zero => exact mem_filter.mpr ⟨mem_product.mpr ⟨mf,af⟩,ne⟩
    | succ i ih => simpa only [f,Function.iterate_succ_apply'] using gp _ ih
  have joins (i) : (f (i+1)).1=(f i).2 ∧ ExitTo X F w (f i).2 (f i).1 (f (i+1)).2 := by
    simpa only [f,Function.iterate_succ_apply'] using edge _ (stay i)
  let c (i : ℕ) := (f i).1
  have step (i) : c i∈F ∧ c i≠c (i+1) ∧ ExitTo X F w (c (i+1)) (c i) (c (i+2)) := by
    have here := split (stay i)
    exact ⟨here.1,(by change (f i).1≠(f (i+1)).1; rw [(joins i).1]; exact here.2.2),by
      change ExitTo X F w (f (i+1)).1 (f i).1 (f (i+2)).1
      rw [(joins i).1,(joins (i+1)).1]
      exact (joins i).2⟩
  refine ⟨c,rfl,(joins 0).1,step,?_⟩
  obtain ⟨i,ib,j,jb,ij,same⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s:=range (P.card+1)) (t:=P) (f:=f) (by simp) (fun i _ => stay i)
  have cap : P.card≤F.card*F.card := (card_le_card (filter_subset _ _)).trans (card_product F F).le
  have close (u v) (lt : u<v) (vb : v∈range (P.card+1)) (eq : f u=f v) :
      ∃i l,3≤l ∧ i+l≤F.card*F.card ∧ c (i+l)=c i ∧ c (i+l+1)=c (i+1) := by
    have cs : c v=c u := congrArg Prod.fst eq.symm
    have cs' : c (v+1)=c (u+1) := (joins v).1.trans ((congrArg Prod.snd eq.symm).trans (joins u).1.symm)
    have no1 : v≠u+1 := fun e => (step u).2.1 (e ▸ cs.symm)
    have no2 : v≠u+2 := fun e => (step u).2.2.2.2.1 (e ▸ cs)
    have last := mem_range.mp vb
    exact ⟨u,v-u,by omega,by omega,by simpa [show u+(v-u)=v by omega] using cs,
      by simpa [show u+(v-u)=v by omega] using cs'⟩
  rcases Nat.lt_or_gt_of_ne ij with lt|lt
  · exact close i j lt jb same
  · exact close j i lt ib same.symm

/-- Vertex-by-vertex cancellation around a closed segment, valid for every
nonnegative test weight. Each row of the incidence tensor balances separately. -/
theorem boundary_balance (c : ℕ→Finset ℕ) (w : ℕ→ℕ) (i l) (closed : c (i+l)=c i) :
    (∑k∈range l,∑z∈c (i+k+1)\c (i+k),w z)=(∑k∈range l,∑z∈c (i+k)\c (i+k+1),w z) := by
  classical
  have diff (A B : Finset ℕ) :
      (∑z∈A\B,w z)+(∑z∈B,w z)=(∑z∈B\A,w z)+(∑z∈A,w z) := by
    have a := sum_sdiff (inter_subset_left : A∩B⊆A) (f:=w)
    have b := sum_sdiff (inter_subset_right : A∩B⊆B) (f:=w)
    have a' : A\(A∩B)=A\B := by ext; simp
    have b' : B\(A∩B)=B\A := by ext; simp
    rw [a'] at a
    rw [b'] at b
    omega
  have tel (j) : (∑k∈range j,∑z∈c (i+k+1)\c (i+k),w z)+(∑z∈c i,w z)=
      (∑k∈range j,∑z∈c (i+k)\c (i+k+1),w z)+(∑z∈c (i+j),w z) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [sum_range_succ,sum_range_succ]
      have d := diff (c (i+j+1)) (c (i+j))
      rw [show i+(j+1)=i+j+1 by omega]
      omega
  have eq := tel l
  rw [closed] at eq
  omega

/-- The failed row of one transfer becomes a deleted label in the next.
Charge its entire old weight either to the next unused mass or to one
specific deposit on the preceding cycle outside the new one. -/
theorem next_charge {q n} (X : Model q n) {F w A M L}
    (sub : F⊆family X) (af : A∈F) (step : ExitTo X F w A M L) :
    let E := graph X.D F
    let U := X.V\(A\M)
    let g := TwoCycleTransfer.deposit E A M w
    ∃p∈L\A,∃z∈L∩(A\M),E p z=true ∧
      score q E U (fun v => w v+g v) p≤(∑v∈U,(w v+g v)) ∧
      (w p≤TwoCycleTransfer.unused E L A w ∨
       ∃u∈L∩A, ∃r∈A\L,E u p=true ∧ E u r=true ∧ TwoCycleTransfer.deposit E L A w r=w p) := by
  classical
  intro E U g
  obtain ⟨lf,_,_,p,pa,z,zh,arc,fail,_⟩ := step
  have ac : Cycle E X.V q A := retain_cycle (show Cycle X.D X.V q A from (mem_filter.mp (sub af)).2) af
  have lc : Cycle E X.V q L := retain_cycle (show Cycle X.D X.V q L from (mem_filter.mp (sub lf)).2) lf
  refine ⟨p,pa,z,zh,arc,fail,?_⟩
  let B := TwoCycleTransfer.crossing E L A
  by_cases sent : p∈B.image (TwoCycleTransfer.succHead E L)
  · obtain ⟨u,ub,up⟩ := mem_image.mp sent
    have both : u∈L∩A := (mem_filter.mp ub).1
    let r := TwoCycleTransfer.succHead E A u
    have edge {C} (c : Cycle E X.V q C) (uc : u∈C) : E u (TwoCycleTransfer.succHead E C u)=true := by
      have pos : (outN E C u).Nonempty := card_pos.mp (by rw [c.heads u uc]; decide)
      have hit := (outN E C u).min'_mem pos
      exact (mem_outN.mp (show TwoCycleTransfer.succHead E C u∈outN E C u by
        simpa only [TwoCycleTransfer.succHead,dite_eq_left pos] using hit)).2
    exact Or.inr ⟨u,both,r,TwoCycleTransfer.recipient_location lc ac ub,up ▸ edge lc (mem_inter.mp both).1,
      edge ac (mem_inter.mp both).2,(TwoCycleTransfer.paired_deposit ac w ub).trans (congrArg w up)⟩
  · exact Or.inl (single_le_sum (f:=w) (fun _ _ => Nat.zero_le _) (mem_sdiff.mpr ⟨pa,sent⟩))

/-- The same marked rows work for every finite sum of transitions. In
particular a closed segment must pay at least one additional unit per step
after unused mass, diagonal credits and transported head credits are counted. -/
theorem orbit_bill {q n} (X : Model q n) {F w} (sub : F⊆family X)
    (strict : Strict q (graph X.D F) X.V w) (c : ℕ→Finset ℕ)
    (steps : ∀i,ExitTo X F w (c (i+1)) (c i) (c (i+2))) :
    let E := graph X.D F
    let Z (i : ℕ) := c (i+1)\c i
    let U (i : ℕ) := X.V\Z i
    let g (i : ℕ) := TwoCycleTransfer.deposit E (c (i+1)) (c i) w
    ∃p z : ℕ→ℕ,(∀i,p i∈c (i+2)\c (i+1) ∧ z i∈c (i+2)∩Z i ∧ E (p i) (z i)=true) ∧
      ∀I : Finset ℕ, I.card+
        (∑i∈I,(TwoCycleTransfer.unused E (c (i+1)) (c i) w+g i (p i)+
          q*(∑v∈outN E (U i) (p i),g i v))) ≤
        q*(∑i∈I,∑v∈outN E (Z i) (p i),w v) := by
  classical
  intro E Z U g
  choose p pm z zm arc _ deb using fun i => (steps i).2.2.2
  refine ⟨p,z,fun i => ⟨pm i,zm i,arc i⟩,?_⟩
  intro I
  have one (i) (_ : i∈I) :
      1+(TwoCycleTransfer.unused E (c (i+1)) (c i) w+g i (p i)+q*(∑v∈outN E (U i) (p i),g i v)) ≤
        q*(∑v∈outN E (Z i) (p i),w v) := by
    have nextC : Cycle X.D X.V q (c (i+2)) := (mem_filter.mp (sub (steps i).1)).2
    have old := nat_strict.mp strict (p i) (nextC.sub (mem_sdiff.mp (pm i)).1)
    change (∑v∈X.V,w v)<score q E X.V w (p i) at old
    have d := deb i
    change score q E X.V w (p i)+TwoCycleTransfer.unused E (c (i+1)) (c i) w+g i (p i)+
      q*(∑v∈outN E (U i) (p i),g i v)≤(∑v∈X.V,w v)+q*(∑v∈outN E (Z i) (p i),w v) at d
    omega
  have total := sum_le_sum one
  simpa only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,mul_sum] using total

#print axioms orbit_bill
#print axioms next_charge
#print axioms orbit
#print axioms boundary_balance
end LeanCH.BR.Closure.PaidCycleFamilyOrbit
