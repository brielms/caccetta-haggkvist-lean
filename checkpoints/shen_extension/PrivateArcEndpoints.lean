import checkpoints.shen_extension.CriticalCycleFamily

namespace LeanCH.BR.Closure.PrivateArcEndpoints
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier

theorem graph_free {q n} (X : Model q n) (F : Family) : QFree (graph X.D F) X.V q := by
  have lift {a b k} (walk : Walk (graph X.D F) X.V a b k) : Walk X.D X.V a b k := by
    induction walk with
    | refl => exact .refl _
    | step inside edge _ ih =>
      obtain ⟨A,ae⟩ := active.mp edge
      exact .step inside (mem_col.mp ae).2.2.2 ih
  exact fun a k lo hi walk => X.free a k lo hi (lift walk)

theorem separated {q n} (X : Model q n) (hq : 2≤q) {F} (feas : Feasible q n X.D X.V F) :
    ShenParentIntersection.Separated (graph X.D F) X.V X.V := by
  obtain ⟨w,pos,bud,s⟩ := feas
  have free := graph_free X F
  obtain ⟨I⟩ := prime_descent (fun z zv => Bool.eq_false_iff.mpr (loopfree free (by omega) zv)) X.live pos s
  have eq := eq_of_subset_of_card_le I.subset (X.minimal _ _ _ I.nonempty
    (free.mono_set I.subset) I.positive (I.bounded.trans bud) I.strict)
  have rigid : ShenParentIntersection.Rigid I := by
    intro U sub live v positive strict mass
    rw [eq]
    exact X.minimal _ U v live (free.mono_set sub) positive (mass.trans (I.bounded.trans bud)) strict
  exact eq ▸ ShenParentIntersection.separated rigid

/-- In any feasible family on a minimum support, a vertex of a named cycle
has another named witness. The argument applies before choosing a cut. -/
theorem other_witness {q n} (X : Model q n) (hq : 2≤q) {F}
    (sub : F⊆family X) (feas : Feasible q n X.D X.V F) {C y} (cf : C∈F) (yc : y∈C) :
    ∃A∈F,A≠C ∧ y∈A := by
  classical
  let E := graph X.D F
  have actual (A) (af : A∈F) : Cycle E X.V q A :=
    retain_cycle (show Cycle X.D X.V q A from (mem_filter.mp (sub af)).2) af
  have c := actual C cf
  have sep := separated X hq feas
  have free := graph_free X F
  let P := C.filter (fun p => ∀A∈F,p∈A → A=C)
  have unique (p) (pm : p∈P) {z} (edge : E z p=true) : z∈C := by
    obtain ⟨A,hit⟩ := active.mp edge
    obtain ⟨af,za,pa,_⟩ := mem_col.mp hit
    exact (mem_filter.mp pm).2 A af pa ▸ za
  have prev (p) (pm : p∈P) : ∃u∈P,E u p=true := by
    have pc := (mem_filter.mp pm).1
    obtain ⟨u,ui⟩ := card_pos.mp (show 0<(inN E C p).card by rw [show (inN E C p).card=1 from c.incoming p pc]; decide)
    obtain ⟨uc,up⟩ := mem_inN.mp ui
    refine ⟨u,mem_filter.mpr ⟨uc,?_⟩,up⟩
    intro A af ua
    have a := actual A af
    obtain ⟨z,zi⟩ := card_pos.mp (show 0<(outN E A u).card by rw [a.heads u ua]; decide)
    obtain ⟨za,uz⟩ := mem_outN.mp zi
    by_cases same : z=p
    · exact (mem_filter.mp pm).2 A af (same ▸ za)
    obtain ⟨b,_,bp,bz⟩ := sep p (c.sub pc) z (a.sub za) same
    have bu : b=u := card_le_one.mp (c.incoming p pc).le _ (mem_inN.mpr ⟨unique p pm bp,bp⟩) _ ui
    change E b z=false at bz
    rw [bu,uz] at bz
    contradiction
  by_contra! none
  have yp : y∈P := mem_filter.mpr ⟨yc,fun A af ya => by_contra fun ne => none A af ne ya⟩
  have inside : P⊆C := filter_subset _ _
  have deg (z) (zp : z∈P) : 1≤(outN (fun x v => E v x) P z).card := by
    obtain ⟨u,up,uz⟩ := prev z zp
    exact card_pos.mpr ⟨u,mem_outN.mpr ⟨up,uz⟩⟩
  have sz := dt_size (by omega : 1≤q) (ball_q_one q (by omega)) (free.reverse.mono_set (inside.trans c.sub)) deg ⟨y,yp⟩
  have whole : P=C := eq_of_subset_of_card_le inside (by rw [c.size]; simpa using sz)
  obtain ⟨w,_,_,strict⟩ := feas
  obtain ⟨t,tc,minim⟩ := C.exists_min_image w ⟨y,yc⟩
  obtain ⟨p,pin⟩ := card_pos.mp (show 0<(inN E C t).card by rw [show (inN E C t).card=1 from c.incoming t tc]; decide)
  obtain ⟨pc,pt⟩ := mem_inN.mp pin
  have pp : p∈P := whole.symm ▸ pc
  have singleton : outN E X.V p={t} := by
    ext z
    constructor
    · intro hit
      obtain ⟨A,used⟩ := active.mp (mem_outN.mp hit).2
      obtain ⟨af,pa,za,_⟩ := mem_col.mp used
      have zc : z∈C := (mem_filter.mp pp).2 A af pa ▸ za
      exact mem_singleton.mpr (card_le_one.mp (c.heads p pc).le _ (mem_outN.mpr ⟨zc,(mem_outN.mp hit).2⟩) _
        (mem_outN.mpr ⟨tc,pt⟩))
    · intro hit
      exact mem_singleton.mp hit ▸ mem_outN.mpr ⟨c.sub tc,pt⟩
  have high := nat_strict.mp strict p (c.sub pc)
  have form : score q E X.V w p = w p+q*(∑z∈outN E X.V p,w z) := by simp only [score,outN,sum_filter]
  change (∑z∈X.V,w z)<score q E X.V w p at high
  rw [form,singleton,sum_singleton] at high
  have low := sum_le_sum (s:=C.erase p) (fun z (hz : z∈C.erase p) => minim z (mem_of_mem_erase hz))
  have count := card_erase_add_one pc
  rw [c.size] at count
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,show (C.erase p).card=q by omega] at low
  have split := sum_erase_add C w pc
  have mass := sum_le_sum_of_subset_of_nonneg (f:=w) c.sub (by intros;omega)
  omega

/-- Both ends of the very same private arc have alternate witnesses. The
tail witness misses the head; the head witness misses the tail. -/
theorem endpoints {q n} (X : Model q n) (hq : 2≤q) {F C p y}
    (sub : F⊆family X) (feas : Feasible q n X.D X.V F) (cf : C∈F)
    (used : graph X.D F p y=true) (lost : graph X.D (F.erase C) p y=false) :
    ∃A∈F,∃B∈F, A≠C ∧ B≠C ∧ A≠B ∧ p∈A ∧ y∉A ∧ y∈B ∧ p∉B := by
  classical
  obtain ⟨L,l⟩ := active.mp used
  obtain ⟨lf,pl,yl,py⟩ := mem_col.mp l
  have never (K) (kf : K∈F) (diff : K≠C) (pk : p∈K) (yk : y∈K) : False := by
    have keep : graph X.D (F.erase C) p y=true := active.mpr
      ⟨K,mem_col.mpr ⟨mem_erase.mpr ⟨diff,kf⟩,pk,yk,py⟩⟩
    rw [keep] at lost
    contradiction
  have eq : L=C := by_contra fun diff => never L lf diff pl yl
  obtain ⟨A,af,ac,pa⟩ := other_witness X hq sub feas cf (eq ▸ pl)
  obtain ⟨B,bf,bc,yb⟩ := other_witness X hq sub feas cf (eq ▸ yl)
  exact ⟨A,af,B,bf,ac,bc,(fun same => never A af ac pa (same.symm ▸ yb)),
    pa,never A af ac pa,yb,fun pb => never B bf bc pb yb⟩

#print axioms other_witness
#print axioms endpoints
end LeanCH.BR.Closure.PrivateArcEndpoints
