import checkpoints.shen_extension.CycleSquareTensor

namespace LeanCH.BR.Closure.CycleSquareBalance
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor CycleSquareTensor

/-- Sum of a test function over ordered arcs of the current support. -/
def arcSum (D : CH.Digraph) (M : Finset ℕ) (f : ℕ→ℕ→ℤ) : ℤ :=
  ∑x∈M,∑y∈M,if D x y=true then f x y else 0

private theorem trim {D W M q a u b} (c : Cycle D W q M) (am : a∈M) (um : u∈M)
    (bm : b∈M) (au : D a u=true) (ub : D u b=true) (anu : a≠u) (f : ℕ→ℕ→ℤ) :
    arcSum D M f=arcSum D (M.erase u) f+f a u+f u b := by
  classical
  let g := fun x y => if D x y=true then f x y else 0
  have oneOut : (∑y∈M,g u y)=f u b := by
    rw [sum_eq_single b]
    · simp [g,ub]
    · intro y ym ne
      have no : ¬D u y=true := fun uy => ne (card_le_one.mp (c.heads u um).le
        y (mem_outN.mpr ⟨ym,uy⟩) b (mem_outN.mpr ⟨bm,ub⟩))
      simp [g,no]
    · simp [bm]
  have oneIn : (∑x∈M.erase u,g x u)=f a u := by
    rw [sum_eq_single a]
    · simp [g,au]
    · intro x xe ne
      have one : (inN D M u).card=1 := c.incoming u um
      have no : ¬D x u=true := fun xu => ne (card_le_one.mp one.le
        x (mem_inN.mpr ⟨mem_of_mem_erase xe,xu⟩) a (mem_inN.mpr ⟨am,au⟩))
      simp [g,no]
    · simp [am,anu]
  change (∑x∈M,∑y∈M,g x y)=(∑x∈M.erase u,∑y∈M.erase u,g x y)+_+_
  rw [←sum_erase_add M (fun x => ∑y∈M,g x y) um,oneOut,←oneIn,←sum_add_distrib]
  simp only [sum_erase_add _ _ um]

/-- Conservation of ordered arc incidences, simultaneously for every test
function f. Taking the indicator of (x,y) isolates a single matrix entry. -/
theorem change {D W M N q a u v b} (hq : 1≤q) (free : QFree D W q)
    (c : Cycle D W q M) (d : Cycle D W q N) (e : Shift D M N a u v b) (f : ℕ→ℕ→ℤ) :
    arcSum D M f+f a v+f v b = arcSum D N f+f a u+f u b := by
  have anu : a≠u := fun eq => loopfree free hq (c.sub e.uM) (eq ▸ e.before₁)
  have bnu : b≠u := fun eq => loopfree free hq (c.sub e.uM) (eq ▸ e.before₂)
  have anv : a≠v := fun eq => e.exterior (eq ▸ e.aM)
  have an : a∈N := e.labels ▸ mem_insert_of_mem (mem_erase.mpr ⟨anu,e.aM⟩)
  have bn : b∈N := e.labels ▸ mem_insert_of_mem (mem_erase.mpr ⟨bnu,e.bM⟩)
  have vn : v∈N := e.labels ▸ mem_insert_self _ _
  have same : N.erase v=M.erase u := by
    rw [e.labels,erase_insert (fun h => e.exterior (mem_of_mem_erase h))]
  have old := trim c e.aM e.uM e.bM e.before₁ e.before₂ anu f
  have new := trim d an vn bn e.after₁ e.after₂ anv f
  rw [same] at new
  omega

theorem closed_balance {D W q} (hq : 1≤q) (free : QFree D W q) (M : ℕ→Finset ℕ)
    (a u v b : ℕ→ℕ) (l : ℕ) (closed : M l=M 0)
    (cycle : ∀i,Cycle D W q (M i)) (move : ∀i,Shift D (M i) (M (i+1)) (a i) (u i) (v i) (b i))
    (f : ℕ→ℕ→ℤ) :
    (∑i∈range l,(f (a i) (v i)+f (v i) (b i))) =
    ∑i∈range l,(f (a i) (u i)+f (u i) (b i)) := by
  have telescopes (k : ℕ) : arcSum D (M 0) f+(∑i∈range k,(f (a i) (v i)+f (v i) (b i))) =
      arcSum D (M k) f+(∑i∈range k,(f (a i) (u i)+f (u i) (b i))) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have eq := change hq free (cycle k) (cycle (k+1)) (move k) f
      rw [sum_range_succ,sum_range_succ]
      omega
  have eq := telescopes l
  rw [closed] at eq
  omega

#print axioms closed_balance
end LeanCH.BR.Closure.CycleSquareBalance
