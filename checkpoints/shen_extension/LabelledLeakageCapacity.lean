import checkpoints.shen_extension.PortParentInvariant

namespace LeanCH.BR.Closure.LabelledLeakageCapacity
open Finset BRq2 BRq3 BR45 WeightedSD

noncomputable def region (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (a : ℕ) :=
  BRsub.ballSet E V (outN E V a) (q-2)

def flow (q : ℕ) (E : CH.Digraph) (w p : ℕ → ℚ) (i j : ℕ) : ℚ :=
  if E i j=true then q*p i*w j else 0

/-- The inner flow cancels even when the two laws have different normalizations. -/
theorem cut {q E V w p c d} (rows : ∀ i∈V, WeightedSD.row q E V w i=c)
    (cols : ∀ i∈V, WeightedSD.col q E V p i=d) {S : Finset ℕ} (sub : S⊆V) :
    (∑ i∈S, ∑ j∈V\S, flow q E w p i j) - (∑ i∈S, ∑ j∈V\S, flow q E w p j i) =
      c*mass S p-d*mass S w := by
  classical
  have outgoing (i) : ∑ j∈V, flow q E w p i j = (q*p i)*outW E V w i := by
    simp only [outW,mul_sum]; apply sum_congr rfl; intro j _; by_cases e : E i j=true <;> simp [flow,e]
  have incoming (i) : ∑ j∈V, flow q E w p j i = (q*w i)*inW E V p i := by
    simp only [inW,mul_sum]; apply sum_congr rfl; intro j _; by_cases e : E j i=true <;> simp [flow,e,mul_right_comm]
  have individual (i) (hi : i∈S) :
      (∑ j∈V, flow q E w p i j)-(∑ j∈V, flow q E w p j i) = c*p i-d*w i := by
    rw [outgoing,incoming,← rows i (sub hi),← cols i (sub hi)]
    unfold WeightedSD.row WeightedSD.col
    ring
  have split (f : ℕ→ℕ→ℚ) :
      (∑ i∈S, ∑ j∈V\S, f i j)+(∑ i∈S, ∑ j∈S, f i j)=∑ i∈S, ∑ j∈V, f i j := by
    rw [←sum_add_distrib]; exact sum_congr rfl (fun i _ => sum_sdiff sub)
  have h := sum_congr (s₂:=S) rfl individual
  simp only [sum_sub_distrib,←mul_sum,mass] at h ⊢
  have symm := sum_comm (s:=S) (t:=S) (f:=flow q E w p)
  linarith only [h,split (flow q E w p),split (fun i j=>flow q E w p j i),symm]

theorem saturated_region {q E V a i} (hq : 2≤q) (free : QFree E V q)
    (sat : BRsub.Sat q E V) (av : a∈V) (iv : i∈V) :
    i∈region q E V a ↔ i≠a ∧ E i a≠true := by
  constructor
  · intro h
    obtain ⟨z,hz,reach⟩ := BRsub.mem_ballSet.mp h
    obtain ⟨_,k,le,path⟩ := mem_ball.mp reach
    have pth := Walk.step (mem_outN.mp hz).1 (mem_outN.mp hz).2 path
    exact ⟨fun eq => free a _ (by omega) (by omega) (eq ▸ pth),
      fun back => free a _ (by omega) (by omega) (pth.snoc av back)⟩
  · rintro ⟨ne,missing⟩
    obtain ⟨_,k,le,path⟩ := mem_ball.mp (sat a av i iv missing)
    cases path with
    | refl => exact (ne rfl).elim
    | step hv edge tail =>
      exact BRsub.mem_ballSet.mpr ⟨_,mem_outN.mpr ⟨hv,edge⟩,mem_ball.mpr ⟨iv,_,by omega,tail⟩⟩

/-- Exact reverse incidence of a crossing on a saturated native graph. -/
theorem crossing {q E V i j} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (iv : i∈V) (jv : j∈V) (edge : E i j=true) :
    V.filter (fun a => i∈region q E V a ∧ j∉region q E V a) =
      outN E V j \ outN E V i := by
  classical
  ext a
  by_cases av : a∈V
  · simp only [mem_filter, av, true_and, mem_sdiff, mem_outN,
      saturated_region hq free sat av iv, saturated_region hq free sat av jv]
    have noBack : E j i≠true := no_back_arc free iv (ball_of_adj jv edge) (by omega)
    constructor
    · rintro ⟨⟨_,ia⟩,nj⟩
      exact ⟨by by_contra miss; exact nj ⟨fun eq => ia (eq ▸ edge),miss⟩,ia⟩
    · rintro ⟨ja,ia⟩
      exact ⟨⟨fun eq => noBack (eq ▸ ja),ia⟩,fun h => h.2 ja⟩
  · simp [av,mem_outN]

noncomputable def owners (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (r : ℕ→ℕ) (i j : ℕ) :=
  V.filter (fun a => r a=i ∧ j∉region q E V a)

/-- Roots reached via j but via no other head of i; direct heads of i are excluded. -/
def privateRoots (E : CH.Digraph) (V : Finset ℕ) (i j : ℕ) : Finset ℕ :=
  (outN E V j \ outN E V i) \ (((outN E V i).erase j).biUnion (outN E V))

theorem sole_exit {q E V i j a} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (av : a∈V) (iv : i∈V) (jv : j∈V) (ij : E i j=true) :
    (i∈region q E V a ∧ outN E (V\region q E V a) i={j}) ↔ a∈privateRoots E V i j := by
  classical
  have cross {k} (kv : k∈V) (ik : E i k=true) :
      i∈region q E V a ∧ k∉region q E V a ↔ a∈outN E V k \ outN E V i := by
    rw [←crossing hq free sat iv kv ik,mem_filter]; simp [av]
  constructor
  · rintro ⟨ir,one⟩
    have exitj : j∈outN E (V\region q E V a) i := one ▸ mem_singleton_self _
    have eligible := (cross jv ij).mp ⟨ir,(mem_sdiff.mp (mem_outN.mp exitj).1).2⟩
    refine mem_sdiff.mpr ⟨eligible,?_⟩
    intro other
    obtain ⟨k,hk,ka⟩ := mem_biUnion.mp other
    obtain ⟨ne,head⟩ := mem_erase.mp hk
    obtain ⟨kv,ik⟩ := mem_outN.mp head
    have ko := ((cross kv ik).mpr (mem_sdiff.mpr ⟨ka,(mem_sdiff.mp eligible).2⟩)).2
    have leak : k∈outN E (V\region q E V a) i := mem_outN.mpr ⟨mem_sdiff.mpr ⟨kv,ko⟩,ik⟩
    exact ne (mem_singleton.mp (one ▸ leak))
  · intro h
    obtain ⟨eligible,unique⟩ := mem_sdiff.mp h
    obtain ⟨ir,jo⟩ := (cross jv ij).mpr eligible
    refine ⟨ir,?_⟩
    ext k; rw [mem_singleton]
    constructor
    · intro hk; by_contra ne
      obtain ⟨out,ik⟩ := mem_outN.mp hk
      obtain ⟨kv,ko⟩ := mem_sdiff.mp out
      exact unique (mem_biUnion.mpr ⟨k,mem_erase.mpr ⟨ne,mem_outN.mpr ⟨kv,ik⟩⟩,
        (mem_sdiff.mp ((cross kv ik).mp ⟨ir,ko⟩)).1⟩)
    · rintro rfl; exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨jv,jo⟩,ij⟩

/-- Each root keeps its chosen leaking row. Arbitrary nonnegative root weights are allowed. -/
theorem labelled {q E V w p c} (r : ℕ→ℕ) (h : ℕ→ℚ) (hn : ∀a∈V,0≤h a)
    (pn : ∀i∈V,0≤p i) (rv : ∀a∈V,r a∈V)
    (bill : ∀a∈V,c-mass (region q E V a) w ≤
      q*mass ((V\region q E V a).filter (fun j=>E (r a) j=true)) w) :
    (∑ a∈V,h a*p (r a)*(c-mass (region q E V a) w)) ≤
      ∑ i∈V,∑ j∈V,flow q E w p i j * mass (owners q E V r i j) h := by
  classical
  have reindex (a) (av : a∈V) :
      h a*p (r a)*(q*mass ((V\region q E V a).filter (fun j=>E (r a) j=true)) w) =
      ∑ i∈V, ∑ j∈V, if r a=i ∧ j∉region q E V a then flow q E w p i j*h a else 0 := by
    rw [sum_eq_single (r a)]
    · simp only [true_and,mass,sum_filter,←filter_notMem_eq_sdiff,sum_filter,mul_sum]
      apply sum_congr rfl; intro j _
      by_cases inside : j∈region q E V a <;> by_cases arc : E (r a) j=true <;> simp [inside,arc,flow]
      ring
    · intro i _ ne; simp [Ne.symm ne]
    · intro outside; exact (outside (rv a av)).elim
  calc
    _ ≤ ∑ a∈V,h a*p (r a)*(q*mass ((V\region q E V a).filter (fun j=>E (r a) j=true)) w) :=
      sum_le_sum (fun a av => mul_le_mul_of_nonneg_left (bill a av) (mul_nonneg (hn a av) (pn _ (rv a av))))
    _ = _ := by
      rw [sum_congr rfl reindex,sum_comm]
      apply sum_congr rfl; intro i _
      rw [sum_comm]
      apply sum_congr rfl; intro j _
      simp only [owners,mass,sum_filter,mul_sum]
      apply sum_congr rfl; intro a _; split_ifs <;> simp

theorem private_capacity {q E V w p} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (wn : ∀j∈V,0≤w j) (pn : ∀i∈V,0≤p i) (r : ℕ→ℕ) (rr : ∀a∈V,r a∈region q E V a)
    (h : ℕ→ℚ) (hn : ∀a∈V,0≤h a) :
    (∑ i∈V,∑ j∈V,flow q E w p i j * mass (owners q E V r i j) h) ≤
      ∑ i∈V,∑ j∈V,flow q E w p i j * mass (outN E V j \ outN E V i) h := by
  classical
  apply sum_le_sum; intro i iv; apply sum_le_sum; intro j jv
  by_cases arc : E i j=true
  · have sub : owners q E V r i j ⊆ outN E V j \ outN E V i := by
      rw [←crossing hq free sat iv jv arc]
      intro a ha
      obtain ⟨av,eq,nj⟩ := mem_filter.mp ha
      exact mem_filter.mpr ⟨av,eq ▸ rr a av,nj⟩
    exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg sub
      (fun a ha _ => hn a (mem_outN.mp (mem_sdiff.mp ha).1).1))
      (by simpa [flow,arc] using mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (pn i iv)) (wn j jv))
  · simp [flow,arc]

/-- If each chosen row has a sole exit, charge only roots for which the
two-step path via j is unique. -/
theorem sole_capacity {q E V w p} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (wn : ∀j∈V,0≤w j) (pn : ∀i∈V,0≤p i) (r : ℕ→ℕ) (rr : ∀a∈V,r a∈region q E V a)
    (one : ∀a∈V,(outN E (V\region q E V a) (r a)).card≤1)
    (h : ℕ→ℚ) (hn : ∀a∈V,0≤h a) :
    (∑ i∈V,∑ j∈V,flow q E w p i j * mass (owners q E V r i j) h) ≤
      ∑ i∈V,∑ j∈V,flow q E w p i j * mass (privateRoots E V i j) h := by
  classical
  apply sum_le_sum; intro i iv; apply sum_le_sum; intro j jv
  by_cases arc : E i j=true
  · have sub : owners q E V r i j ⊆ privateRoots E V i j := by
      intro a ha
      obtain ⟨av,eq,jo⟩ := mem_filter.mp ha
      subst i
      have leak : j∈outN E (V\region q E V a) (r a) := mem_outN.mpr ⟨mem_sdiff.mpr ⟨jv,jo⟩,arc⟩
      exact (sole_exit hq free sat av iv jv arc).mp ⟨rr a av,
        (eq_of_subset_of_card_le (singleton_subset_iff.mpr leak) (by simpa using one a av)).symm⟩
    apply mul_le_mul_of_nonneg_left (mass_mono sub (fun a ha=>hn a (mem_outN.mp (mem_sdiff.mp (mem_sdiff.mp ha).1).1).1))
    simpa [flow,arc] using mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (pn i iv)) (wn j jv)
  · simp [flow,arc]

/-- A fixed root can contribute at most one parent of j. Taking M(j) to be
the largest dual weight of a parent of j retains that restriction. -/
theorem head_peak {q E V w p c} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (wn : ∀i∈V,0≤w i) (rows : ∀i∈V,WeightedSD.row q E V w i=c)
    (r : ℕ→ℕ)
    (u : ℕ→ℚ) (un : ∀j∈V,0≤u j)
    (upper : ∀i∈V,∀j∈V,E i j=true → p i≤u j)
    (rr : ∀a∈V,r a∈region q E V a) :
    (∑ i∈V,∑ j∈V,flow q E w p i j*mass (owners q E V r i j) w) ≤
      ∑ j∈V,w j*(c-w j)*u j := by
  classical
  rw [sum_comm]; apply sum_le_sum; intro j jv
  have expand (i) : flow q E w p i j*mass (owners q E V r i j) w =
      ∑ a∈V,if r a=i ∧ j∉region q E V a then flow q E w p i j*w a else 0 := by
    simp only [owners,mass,sum_filter,mul_sum]
    apply sum_congr rfl; intro a _; split_ifs <;> simp
  simp_rw [expand]; rw [sum_comm]
  calc
    _ ≤ ∑ a∈V,if E j a=true then (q*w j*u j)*w a else 0 := by
      apply sum_le_sum; intro a av
      have iv : r a∈V := BRsub.ballSet_subset (rr a av)
      rw [sum_eq_single (r a)]
      · simp only [true_and]
        by_cases use : j∉region q E V a ∧ E (r a) j=true
        · have eligible : a∈outN E V j \ outN E V (r a) := by
            rw [←crossing hq free sat iv jv use.2]
            exact mem_filter.mpr ⟨av,rr a av,use.1⟩
          simp only [use.1,(mem_outN.mp (mem_sdiff.mp eligible).1).2,flow,use.2,ite_true]
          rw [mul_right_comm (q:ℚ) (p (r a)) (w j)]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (upper _ iv j jv use.2)
            (mul_nonneg (Nat.cast_nonneg q) (wn j jv))) (wn a av)
        · have zero : (if j∉region q E V a then flow q E w p (r a) j*w a else 0)=0 := by
            by_cases out : j∉region q E V a
            · have miss : E (r a) j≠true := fun arc=>use ⟨out,arc⟩
              simp [out,flow,miss]
            · simp [out]
          rw [zero]; split_ifs
          · exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (wn j jv)) (un j jv)) (wn a av)
          · exact le_rfl
      · intro i _ ne; simp [Ne.symm ne]
      · exact fun h=>(h iv).elim
    _ = _ := by
      have fact : (∑ a∈V,if E j a=true then (q*w j*u j)*w a else 0) = (q*w j*u j)*outW E V w j := by
        rw [outW,mul_sum]; apply sum_congr rfl; intro a _; split_ifs <;> simp
      rw [fact,←rows j jv,WeightedSD.row]; ring

/-- Both flat laws evaluate gross capacity. Common heads are precisely the deduction. -/
theorem gross_capacity {q E V w p c d} (rows : ∀i∈V,WeightedSD.row q E V w i=c)
    (cols : ∀j∈V,WeightedSD.col q E V p j=d) :
    (q:ℚ)*(∑ i∈V,∑ j∈V,flow q E w p i j *
      (mass (outN E V j \ outN E V i) w + mass (outN E V j ∩ outN E V i) w)) =
      ∑ j∈V,w j*(d-p j)*(c-w j) := by
  classical
  rw [sum_comm,mul_sum]; apply sum_congr rfl; intro j jv
  have parts (i) : mass (outN E V j \ outN E V i) w + mass (outN E V j ∩ outN E V i) w =
      outW E V w j := by
    have eq : outN E V j \ (outN E V j ∩ outN E V i) = outN E V j \ outN E V i := by
      ext a; simp
    simpa only [outW_eq_mass,mass,←eq] using
      (sum_sdiff (f:=w) (inter_subset_left : outN E V j ∩ outN E V i ⊆ outN E V j))
  simp_rw [parts]; rw [←sum_mul]
  have col : ∑ i∈V,flow q E w p i j=(q*w j)*inW E V p j := by
    rw [inW,mul_sum]; apply sum_congr rfl; intro i _
    by_cases arc : E i j=true <;> simp [flow,arc,mul_right_comm]
  rw [col,←rows j jv,←cols j jv]; unfold WeightedSD.row WeightedSD.col; ring

/-- Sum over the root balls without replacing their incidences by a mean. -/
theorem ball_cuts {q E V w p c d} (rows : ∀ i∈V, WeightedSD.row q E V w i=c)
    (cols : ∀ i∈V, WeightedSD.col q E V p i=d) (h : ℕ→ℚ) :
    (∑ a∈V,h a*((∑ i∈region q E V a,∑ j∈V\region q E V a,flow q E w p i j) -
      ∑ i∈region q E V a,∑ j∈V\region q E V a,flow q E w p j i)) =
    ∑ a∈V,h a*(c*mass (region q E V a) p-d*mass (region q E V a) w) := by
  apply sum_congr rfl; intro a _
  rw [cut rows cols (show region q E V a⊆V from BRsub.ballSet_subset)]

/-- Use the two native equalizers on the saturated model's own graph. -/
theorem native {q n} (X : ShortestCycleWeights.Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card) :
    ∃ (w p : ℕ→ℚ) (c : ℚ) (r : ℕ→ℕ), 1<c ∧ mass X.V w=1 ∧ mass X.V p=1 ∧
      (∀i∈X.V,0<w i) ∧ (∀i∈X.V,0<p i) ∧
      (∀i∈X.V,WeightedSD.row q X.D X.V w i=c) ∧ (∀j∈X.V,WeightedSD.col q X.D X.V p j=c) ∧
      (∀a∈X.V,r a∈region q X.D X.V a ∧ r a∉BRsub.ballSet X.D X.V (outN X.D X.V a) (q-3)) ∧
      ((∑ a∈X.V,w a*p (r a)*(c-mass (region q X.D X.V a) w)) ≤
        ∑ i∈X.V,∑ j∈X.V,flow q X.D w p i j*mass (owners q X.D X.V r i j) w) ∧
      ((∑ i∈X.V,∑ j∈X.V,flow q X.D w p i j*mass (owners q X.D X.V r i j) w) ≤
        ∑ i∈X.V,∑ j∈X.V,flow q X.D w p i j*mass (outN X.D X.V j \ outN X.D X.V i) w) := by
  classical
  obtain ⟨w,p,c,hi,wp,pp,wm,pm,rows,cols⟩ := strict_pair_of_proper_smallRow
    (small.induced X.free) X.live (fun i => (X.weights i : ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  have positive_row {G z} (zp : ∀i∈X.V,0<z i) (zm : mass X.V z=1)
      (row : ∀i∈X.V,WeightedSD.row q G X.V z i=c) (a) (av : a∈X.V) : (outN G X.V a).Nonempty := by
    by_contra! empty
    have low : z a≤mass X.V z := single_le_sum (fun i iv=>(zp i iv).le) av
    have eq := row a av
    rw [WeightedSD.row,outW_eq_mass,empty] at eq
    simp [mass] at eq
    linarith
  have witness (a) (av : a∈X.V) : ∃i,i∈region q X.D X.V a ∧
      i∉BRsub.ballSet X.D X.V (outN X.D X.V a) (q-3) ∧
      c-mass (region q X.D X.V a) w ≤ q*mass ((X.V\region q X.D X.V a).filter (fun j=>X.D i j=true)) w := by
    obtain ⟨b,bv⟩ := positive_row (G:=fun i j => X.D j i) pp pm (fun i iv=>cols i iv) a av
    have par := mem_outN.mp bv
    obtain ⟨i,ir,last,all⟩ := PortParentInvariant.common_leaking_row hq X.free av
      ⟨b,par.1,par.2⟩ (positive_row wp wm rows a av) small w wp (wm ▸ hi) rows
    obtain ⟨_,bill⟩ := all b par.1 par.2
    rw [(PortParentInvariant.same_ball (d:=q-2) X.free av par.1 par.2 (by omega)).2] at bill
    exact ⟨i,ir,last,bill⟩
  let r a := if av : a∈X.V then (witness a av).choose else a
  have spec (a) (av : a∈X.V) := (witness a av).choose_spec
  have rs (a) (av : a∈X.V) : r a∈region q X.D X.V a := by simpa [r,av] using (spec a av).1
  refine ⟨w,p,c,r,hi,wm,pm,wp,pp,rows,cols,fun a av=>⟨rs a av,?_⟩,?_,?_⟩
  · simpa [r,av] using (spec a av).2.1
  · apply labelled r w (fun i iv=>(wp i iv).le) (fun i iv=>(pp i iv).le)
      (fun a av=>BRsub.ballSet_subset (rs a av))
    intro a av; simpa [r,av] using (spec a av).2.2
  · exact private_capacity (by omega) X.free X.sat (fun i iv=>(wp i iv).le) (fun i iv=>(pp i iv).le)
      r rs w (fun i iv=>(wp i iv).le)

#print axioms cut
#print axioms crossing
#print axioms sole_exit
#print axioms labelled
#print axioms private_capacity
#print axioms sole_capacity
#print axioms head_peak
#print axioms gross_capacity
#print axioms ball_cuts
#print axioms native
end LeanCH.BR.Closure.LabelledLeakageCapacity
