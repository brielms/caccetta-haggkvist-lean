import checkpoints.shen_extension.PrivateArcEndpoints
import checkpoints.shen_extension.TwoCycleTransfer

namespace LeanCH.BR.Closure.JointCycleFamilyBarrier
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier

/-- Keep the row and its used column, the third named cycle containing
both labels, and the exact quantitative deficit on this same row. -/
def ExitTo {q n} (X : Model q n) (F : Family) (w : ℕ→ℕ) (A M L : Finset ℕ) : Prop :=
  let E := graph X.D F
  let Z := A\M
  let U := X.V\Z
  let g := TwoCycleTransfer.deposit E A M w
  L∈F ∧ L≠A ∧ L≠M ∧ ∃p∈L\A,∃z∈L∩Z,E p z=true ∧
    score q E U (fun v => w v+g v) p ≤ (∑v∈U,(w v+g v)) ∧
    score q E X.V w p+TwoCycleTransfer.unused E A M w+g p+q*(∑v∈outN E U p,g v) ≤
      (∑v∈X.V,w v)+q*(∑v∈outN E Z p,w v)

def Exit {q n} (X : Model q n) (F : Family) (w : ℕ→ℕ) (A M : Finset ℕ) : Prop :=
  ∃L,ExitTo X F w A M L

theorem exit_any {q n} (X : Model q n) {F w A M} (sub : F⊆family X)
    (wp : ∀v∈X.V,0<w v) (budget : (∑v∈X.V,w v)≤n) (strict : Strict q (graph X.D F) X.V w)
    (af : A∈F) (mf : M∈F) (ne : A≠M) : Exit X F w A M := by
  classical
  have actual (C) (cf : C∈F) : Cycle (graph X.D F) X.V q C :=
    retain_cycle (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  obtain ⟨_,_,p,pa,⟨z,zm,arc⟩,fail,debit⟩ := TwoCycleTransfer.transfer X
    (PrivateArcEndpoints.graph_free X F) wp budget strict (actual A af) (actual M mf) ne
  obtain ⟨L,used⟩ := active.mp arc
  obtain ⟨lf,pl,zl,_⟩ := mem_col.mp used
  exact ⟨L,lf,fun eq => (mem_sdiff.mp pa).2 (eq ▸ pl),fun eq => (mem_sdiff.mp zm).2 (eq ▸ zl),
    p,mem_sdiff.mpr ⟨pl,(mem_sdiff.mp pa).2⟩,z,mem_inter.mpr ⟨zl,zm⟩,arc,fail,debit⟩

/-- The family is chosen once. For every eligible old weighting and every
member A, retain either alternate endpoint-cycle of the very same failing
private arc. Each repair moves the blocker off A, with a named third witness. -/
theorem joint {q n} (X : Model q n) (hq : 2≤q) :
    ∃F⊆family X, 2≤F.card ∧ Feasible q n X.D X.V F ∧
      (∀G,G ⊂ F → ¬Feasible q n X.D X.V G) ∧
      ∀w : ℕ→ℕ,(∀v∈X.V,0<w v) → (∑v∈X.V,w v)≤n → Strict q (graph X.D F) X.V w →
        ∀A∈F,∃p∈A,∃y∈A,graph X.D F p y=true ∧ graph X.D (F.erase A) p y=false ∧
          score q (graph X.D F) X.V w p=score q (graph X.D (F.erase A)) X.V w p+q*w y ∧
          score q (graph X.D (F.erase A)) X.V w p≤∑v∈X.V,w v ∧
          (∃T∈F,∃H∈F,T≠A ∧ H≠A ∧ T≠H ∧ p∈T ∧ y∉T ∧ y∈H ∧ p∉H ∧
            Exit X F w A T ∧ Exit X F w A H) := by
  classical
  obtain ⟨F,sub,two,yes,no,cuts⟩ := CriticalCycleFamily.simultaneous X hq
  refine ⟨F,sub,two,yes,no,?_⟩
  intro w wp bud strict A af
  obtain ⟨M,mf,ne⟩ := exists_mem_ne (s:=F) (a:=A) (by omega)
  obtain ⟨p,_,y,_,used,lost,eq,bill⟩ := row_bill (cuts A af M mf (Ne.symm ne)) strict
    (fun paid => no _ (erase_ssubset af) ⟨w,wp,bud,paid⟩)
  obtain ⟨C,arc⟩ := active.mp used
  obtain ⟨cf,pc,yc,py⟩ := mem_col.mp arc
  have same : C=A := by
    by_contra diff
    have keep : graph X.D (F.erase A) p y=true := active.mpr
      ⟨C,mem_col.mpr ⟨mem_erase.mpr ⟨diff,cf⟩,pc,yc,py⟩⟩
    rw [keep] at lost
    contradiction
  obtain ⟨T,tf,H,hf,ta,ha,th,pt,yt,yh,ph⟩ := PrivateArcEndpoints.endpoints X hq sub yes af used lost
  exact ⟨p,same ▸ pc,y,same ▸ yc,used,lost,eq,bill,T,tf,H,hf,ta,ha,th,pt,yt,yh,ph,
    exit_any X sub wp bud strict af tf (Ne.symm ta),exit_any X sub wp bud strict af hf (Ne.symm ha)⟩

#print axioms joint
#print axioms exit_any
end LeanCH.BR.Closure.JointCycleFamilyBarrier
