import checkpoints.shen_extension.CyclePhaseFork

namespace LeanCH.BR.Closure.ProtectedHeadPayment
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier
open JointCycleFamilyBarrier TwoCycleTransfer

/-- Protect a witness containing the outside row and one of its heads on A.
This row receives no out-neighbour deposit. Its test depends only on its
diagonal deposit, the unused mass, and the weights of its other heads on A. -/
theorem test {D V q A M p y} (a : Cycle D V q A) (m : Cycle D V q M) (pa : p∈M)
    (ym : y∈M) (ya : y∈A) (py : D p y=true) (w : ℕ→ℕ) :
    let Z := A\M
    let U := V\Z
    let g := deposit D A M w
    (∑v∈outN D U p,g v)=0 ∧ outN D Z p=(outN D A p).erase y ∧
      (score q D U (fun v => w v+g v) p≤(∑v∈U,(w v+g v)) ↔
       score q D V w p+unused D A M w+g p≤(∑v∈V,w v)+q*(∑v∈(outN D A p).erase y,w v)) := by
  classical
  intro Z U g
  have yz {z} (zm : z∈M) (pz : D p z=true) : z=y :=
    card_le_one.mp (m.heads p pa).le _ (mem_outN.mpr ⟨zm,pz⟩) _ (mem_outN.mpr ⟨ym,py⟩)
  have zero : (∑v∈outN D U p,g v)=0 := by
    apply sum_eq_zero
    intro v vh
    apply sum_eq_zero
    intro u ub
    have loc := recipient_location a m ub
    apply ite_eq_right
    intro e
    have same := yz (mem_sdiff.mp loc).1 (e ▸ (mem_outN.mp vh).2)
    exact (mem_sdiff.mp loc).2 (same ▸ ya)
  have lost : outN D Z p=(outN D A p).erase y := by
    ext z
    constructor
    · intro hit
      obtain ⟨zm,pz⟩ := mem_outN.mp hit
      obtain ⟨za,no⟩ := mem_sdiff.mp zm
      exact mem_erase.mpr ⟨fun e => no (e ▸ ym),mem_outN.mpr ⟨za,pz⟩⟩
    · intro hit
      obtain ⟨ne,za⟩ := mem_erase.mp hit
      exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨(mem_outN.mp za).1,fun zm => ne (yz zm (mem_outN.mp za).2)⟩,
        (mem_outN.mp za).2⟩
  refine ⟨zero,lost,?_⟩
  have partition := sum_sdiff (sdiff_subset.trans a.sub : Z⊆V) (f:=fun z => if D p z=true then w z else 0)
  have rows : (∑z∈outN D U p,w z)+(∑z∈outN D Z p,w z)=∑z∈outN D V p,w z := by
    simpa only [U,outN,sum_filter] using partition
  have form (S : Finset ℕ) (v : ℕ→ℕ) : score q D S v p=v p+q*(∑z∈outN D S p,v z) := by
    simp only [score,outN,sum_filter]
  rw [form,form,sum_add_distrib,zero,Nat.add_zero]
  have bal := mass_balance a m w
  change (∑v∈U,(w v+g v))+unused D A M w=(∑v∈V,w v) at bal
  rw [lost] at rows
  have mul := congrArg (q * ·) rows
  simp only [Nat.mul_add] at mul
  omega

/-- If the test passes, EVERY other head on A supplies a paid transition,
with its actual arc and its chosen witness. -/
theorem paid {q n} (X : Model q n) {F A M p y} (sub : F⊆family X) (af : A∈F) (mf : M∈F)
    (out : p∉A) (pm : p∈M) (ya : y∈A) (ym : y∈M) (py : graph X.D F p y=true) (w : ℕ→ℕ)
    (bill : score q (graph X.D F) X.V w p+unused (graph X.D F) A M w+deposit (graph X.D F) A M w p ≤
      (∑v∈X.V,w v)+q*(∑v∈(outN (graph X.D F) A p).erase y,w v)) :
    ∀z∈(outN (graph X.D F) A p).erase y,∀L∈F,p∈L → z∈L → ExitTo X F w A M L := by
  classical
  let E := graph X.D F
  have actual (C) (cf : C∈F) : Cycle E X.V q C :=
    retain_cycle (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  obtain ⟨noGift,loss,iff⟩ := test (actual A af) (actual M mf) pm ym ya py w
  intro z hit L lf pl zl
  have del := mem_outN.mp (show z∈outN E (A\M) p from loss.symm ▸ hit)
  refine ⟨lf,fun e => out (e ▸ pl),fun e => (mem_sdiff.mp del.1).2 (e ▸ zl),
    p,mem_sdiff.mpr ⟨pl,out⟩,z,mem_inter.mpr ⟨zl,del.1⟩,del.2,iff.mpr bill,?_⟩
  change score q E X.V w p+unused E A M w+deposit E A M w p+
    q*(∑v∈outN E (X.V\(A\M)) p,deposit E A M w v) ≤ (∑v∈X.V,w v)+q*(∑v∈outN E (A\M) p,w v)
  rw [noGift,Nat.mul_zero,Nat.add_zero,loss]
  exact bill

/-- The protected head and its next head on A both subtract from the cost.
This uses the absence of a digon at the outside row. -/
theorem two_head_credit {q V D A M p y} (hq : 2≤q) (free : QFree D V q)
    (a : Cycle D V q A) (m : Cycle D V q M) (pm : p∈M) (ym : y∈M) (ya : y∈A)
    (py : D p y=true) (w : ℕ→ℕ) :
    unused D A M w+deposit D A M w p+w y+w (succHead D A y)≤∑v∈A,w v := by
  classical
  let Z := A\M
  let U := V\Z
  let g := deposit D A M w
  let s := succHead D A y
  have succMem (C) (c : Cycle D V q C) (yc : y∈C) : succHead D C y∈outN D C y := by
    have pos : (outN D C y).Nonempty := card_pos.mp (by rw [c.heads y yc]; decide)
    simpa only [succHead,dite_eq_left pos] using (outN D C y).min'_mem pos
  obtain ⟨sa,ys⟩ := mem_outN.mp (succMem A a ya)
  change D y s=true at ys
  have sy : s≠y := fun eq => loopfree free (by omega) (a.sub ya) (by simpa only [eq] using ys)
  have mu (z) (zm : z∈M) : z∈U := mem_sdiff.mpr ⟨m.sub zm,fun zz => (mem_sdiff.mp zz).2 zm⟩
  have bal := mass_balance a m w
  change (∑v∈U,(w v+g v))+unused D A M w=∑v∈V,w v at bal
  rw [sum_add_distrib] at bal
  have vz := sum_sdiff (sdiff_subset.trans a.sub : Z⊆V) (f:=w)
  change (∑v∈U,w v)+(∑v∈Z,w v)=_ at vz
  have az := sum_sdiff (inter_subset_left : A∩M⊆A) (f:=w)
  have diff : A\(A∩M)=Z := by ext; simp [Z]
  rw [diff] at az
  have inside := single_le_sum (f:=g) (fun _ _ => Nat.zero_le _) (mu p pm)
  have inter : y∈A∩M := mem_inter.mpr ⟨ya,ym⟩
  have first := single_le_sum (f:=w) (fun _ _ => Nat.zero_le _) inter
  change unused D A M w+g p+w y+w s≤_
  by_cases sm : s∈M
  · have other : s∈(A∩M).erase y := mem_erase.mpr ⟨sy,mem_inter.mpr ⟨sa,sm⟩⟩
    have sec := single_le_sum (f:=w) (fun _ _ => Nat.zero_le _) other
    have mass := sum_erase_add (A∩M) w inter
    omega
  · have crosses : y∈crossing D A M := mem_filter.mpr ⟨inter,mem_sdiff.mpr ⟨sa,sm⟩⟩
    let r := succHead D M y
    obtain ⟨rm,yr⟩ := mem_outN.mp (succMem M m ym)
    have rp : r≠p := fun eq => free p 2 (by decide) hq (.step (m.sub ym) py (.step (m.sub pm) (eq ▸ yr) (.refl _)))
    have received : g r=w s := paired_deposit m w crosses
    have paid := single_le_sum (f:=g) (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨rp,mu r rm⟩ : r∈U.erase p)
    have credits := sum_erase_add U g (mu p pm)
    omega

#print axioms two_head_credit
#print axioms test
#print axioms paid
end LeanCH.BR.Closure.ProtectedHeadPayment
