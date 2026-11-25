import checkpoints.shen_extension.ShapeClimbAt3

/-!
# A fast evaluation of the shape climb at the true degree

`ShapeClimb.deadAll` and `ShapeClimbDead3.deadAll3` test every split of the inner layers: they
build the whole list `splits r k s` (all `C(s - r + k - 2, k - 2)` compositions), then discard
the splits below the floors (`good`) one by one. At degree eleven and above that list has
billions of entries, which is where the evaluation of `ShapeClimbAt.boundAt` and
`ShapeClimbAt3.boundAt3` spends its time and memory.

Here the same test runs as a depth-first search (`go`) that

* builds a split one width at a time and drops a branch as soon as a prefix sum falls below
  its floor, so only the splits with `good` are ever built;
* skips every next width below `peelCap`: those widths make the peel at the newest slot hold,
  so every extension is dead (`peel_of_cap`);

and the reach rule reads its scores from a table (`mkT`), one score row per cut, slot and
layer, each built once per radius on first use, instead of recomputing the score chains at
every split.

Every fast function is proved *equal* to the original one (`deadAllF_eq`, `dead3F_eq`,
`layers3F_eq`, `boundAt3F_eq`, `layersF_eq`, `boundAtF_eq`), so the soundness theorems
`boundAt3F_sound`, `boundAtF_sound` are those of `ShapeClimbAt3` and `ShapeClimbAt`, and the
values are exactly the law's values. Everything is generic in `q`, `r`, `c`.
-/

namespace LeanCH.BR.ShapeClimbFast
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion RecursivePrefixBudget
open ShapeClimbRoot ShapeClimbDead ShapeClimb ShapeClimbDead2 ShapeClimbDead3 ReachCapacity

/-! ### Floors read one width at a time -/

/-- `goodR fs j σ rest`: after a prefix of `j` widths with sum `σ`, each further prefix of
`rest` keeps its floor. -/
def goodR (fs : List ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | j, σ, a :: t => decide (fs.getD (j + 1) 0 ≤ 1 + σ + a) && goodR fs (j + 1) (σ + a) t

theorem all_congr' {α : Type*} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.all f = l.all g
  | [], _ => rfl
  | a :: l, h => by
    have t := all_congr' (l := l) (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.all_cons, h a List.mem_cons_self, t]

theorem good_range (fs : List ℕ) : ∀ (ws : List ℕ) (j σ : ℕ),
    (List.range (ws.length + 1)).all
        (fun i => decide (fs.getD (j + i) 0 ≤ 1 + σ + (ws.take i).sum)) =
      (decide (fs.getD j 0 ≤ 1 + σ) && goodR fs j σ ws)
  | [], j, σ => by simp [goodR]
  | a :: t, j, σ => by
    rw [List.length_cons, List.range_succ_eq_map, List.all_cons, List.all_map]
    have ih := good_range fs t (j + 1) (σ + a)
    have e : ((fun i => decide (fs.getD (j + i) 0 ≤ 1 + σ + ((a :: t).take i).sum)) ∘
        Nat.succ) = fun i => decide (fs.getD (j + 1 + i) 0 ≤ 1 + (σ + a) + (t.take i).sum) := by
      funext i
      refine decide_eq_decide.mpr ?_
      simp only [List.take_succ_cons, List.sum_cons]
      rw [show j + (i + 1) = j + 1 + i by omega]
      omega
    rw [e, ih]
    simp only [goodR, Nat.add_zero, List.take_zero, List.sum_nil, Nat.add_assoc]
    rfl

theorem good_eq (fs : List ℕ) (ws : List ℕ) :
    good fs ws.length ws = (decide (fs.getD 0 0 ≤ 1) && goodR fs 0 0 ws) := by
  have := good_range fs ws 0 0
  simp only [Nat.zero_add, Nat.add_zero] at this
  exact this

theorem length_of_mem_comps : ∀ {n s : ℕ} {l : List ℕ}, l ∈ comps n s → l.length = n
  | 0, s, l, h => by
    unfold comps at h
    split at h
    · simp at h; simp [h]
    · simp at h
  | n + 1, s, l, h => by
    simp only [comps, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, -, t, ht, rfl⟩ := h
    simp [length_of_mem_comps ht]

/-! ### The depth-first search -/

/-- Every completion `rest` (`n` widths, sum `s`) of the prefix `pre` (`j` widths, sum `σ`)
that keeps its floors satisfies `P (pre ++ rest)`. A prefix with `prune pre` is skipped, and so
is every next width below `sk pre`. -/
def go (fs : List ℕ) (P prune : List ℕ → Bool) (sk : List ℕ → ℕ) :
    ℕ → ℕ → List ℕ → ℕ → ℕ → Bool
  | _, _, pre, 0, s => prune pre || (if s = 0 then P pre else true)
  | j, σ, pre, n + 1, s => prune pre ||
    let lo := sk pre
    (List.range (s + 1)).all (fun a => decide (a < lo) ||
      !decide (fs.getD (j + 1) 0 ≤ 1 + σ + a) || go fs P prune sk (j + 1) (σ + a) (pre ++ [a]) n (s - a))

theorem go_eq (fs : List ℕ) (P prune : List ℕ → Bool) (sk : List ℕ → ℕ)
    (hp : ∀ pre rest, prune pre = true → P (pre ++ rest) = true)
    (hs : ∀ pre a rest, a < sk pre → P (pre ++ a :: rest) = true) :
    ∀ n j σ pre s, go fs P prune sk j σ pre n s =
      (comps n s).all (fun rest => !goodR fs j σ rest || P (pre ++ rest)) := by
  intro n
  induction n with
  | zero =>
    intro j σ pre s
    by_cases hpr : prune pre = true
    · simp only [go, hpr, Bool.true_or]
      exact (List.all_eq_true.mpr (fun rest _ => by simp [hp pre rest hpr])).symm
    · simp only [go, Bool.not_eq_true] at hpr ⊢
      rw [hpr, Bool.false_or]
      unfold comps
      split <;> simp [goodR]
  | succ n ih =>
    intro j σ pre s
    by_cases hpr : prune pre = true
    · simp only [go, hpr, Bool.true_or]
      exact (List.all_eq_true.mpr (fun rest _ => by simp [hp pre rest hpr])).symm
    · simp only [go, Bool.not_eq_true] at hpr ⊢
      rw [hpr, Bool.false_or, comps, List.all_flatMap]
      refine all_congr' (fun a _ => ?_)
      rw [List.all_map]
      by_cases low : a < sk pre
      · simp only [low, decide_true, Bool.true_or]
        exact (List.all_eq_true.mpr (fun rest _ => by simp [Function.comp, hs pre a rest low])).symm
      simp only [low, decide_false, Bool.false_or]
      by_cases cond : fs.getD (j + 1) 0 ≤ 1 + σ + a
      · simp only [cond, decide_true, Bool.not_true, Bool.false_or]
        rw [ih]
        refine all_congr' (fun rest _ => ?_)
        simp only [Function.comp, goodR, cond, decide_true, Bool.true_and, List.append_assoc,
          List.singleton_append]
      · simp only [cond, decide_false, Bool.not_false, Bool.true_or]
        exact (List.all_eq_true.mpr (fun rest _ => by
          simp only [Function.comp, goodR, cond, decide_false, Bool.false_and, Bool.not_false,
            Bool.true_or])).symm

/-- Every admissible split is `P`, by the search. -/
def deadAllF (r : ℕ) (fs : List ℕ) (P prune : List ℕ → Bool) (sk : List ℕ → ℕ) (k s : ℕ) : Bool :=
  match k with
  | 0 => (splits r 0 s).all (fun ws => !good fs 0 ws || P ws)
  | k + 1 =>
    if r ≤ s then
      !(decide (fs.getD 0 0 ≤ 1) && decide (fs.getD 1 0 ≤ 1 + r)) || go fs P prune sk 1 r [r] k (s - r)
    else true

theorem deadAllF_eq (r : ℕ) (fs : List ℕ) (P prune : List ℕ → Bool) (sk : List ℕ → ℕ)
    (hp : ∀ pre rest, prune pre = true → P (pre ++ rest) = true)
    (hs : ∀ pre a rest, a < sk pre → P (pre ++ a :: rest) = true) (k s : ℕ) :
    deadAllF r fs P prune sk k s = (splits r k s).all (fun ws => !good fs k ws || P ws) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [deadAllF, splits]
    split
    · rw [List.all_map, go_eq fs P prune sk hp hs]
      by_cases A : fs.getD 0 0 ≤ 1 ∧ fs.getD 1 0 ≤ 1 + r
      · simp only [A.1, A.2, decide_true, Bool.and_self, Bool.not_true, Bool.false_or]
        refine all_congr' (fun rest hr => ?_)
        have len := length_of_mem_comps hr
        have g := good_eq fs (r :: rest)
        rw [List.length_cons, len] at g
        simp only [Function.comp, g, goodR, A.1, A.2, decide_true, Bool.true_and, Nat.zero_add,
          Nat.add_zero, List.singleton_append]
      · have : (decide (fs.getD 0 0 ≤ 1) && decide (fs.getD 1 0 ≤ 1 + r)) = false := by
          simpa [Bool.and_eq_true] using A
        rw [this, Bool.not_false, Bool.true_or]
        refine (List.all_eq_true.mpr (fun rest hr => ?_)).symm
        have len := length_of_mem_comps hr
        have g := good_eq fs (r :: rest)
        rw [List.length_cons, len] at g
        simp only [Function.comp, g, goodR, Nat.zero_add, Nat.add_zero]
        by_cases a0 : fs.getD 0 0 ≤ 1
        · have a1 : ¬fs.getD 1 0 ≤ 1 + r := fun h => A ⟨a0, h⟩
          simp only [a0, a1, decide_true, decide_false, Bool.true_and, Bool.false_and,
            Bool.not_false, Bool.true_or]
        · simp only [a0, decide_false, Bool.false_and, Bool.not_false, Bool.true_or]
    · rfl

/-! ### Lists with a fixed prefix -/

theorem getD_pre {pre rest : List ℕ} {i : ℕ} (d d' : ℕ) (h : i < pre.length) :
    (pre ++ rest).getD i d = pre.getD i d' := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h, List.getElem?_eq_getElem h,
    Option.getD_some]

/-! ### The reach scores from a table -/

/-- The weight of a row of layer `i + 1` in the reach total at the cut `R`, radius `a`. -/
def wt (q r : ℕ) (degrees fs : List ℕ) (R E i a : ℕ) : ℕ :=
  score q r degrees fs R E (i + 1) a + score q r degrees fs R E (i + 1) (q - a) + 2

/-- The score after `score j = u`. -/
def nextScore (q r : ℕ) (degrees fs : List ℕ) (R E i : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => max (r - E) (ret fs R E i 1)
  | j + 1, u => max (step q (r - E) degrees u) (ret fs R E i (j + 2))

/-- The scores at radii `n, n - 1, …, 0`, one step each. -/
def revScores (q r : ℕ) (degrees fs : List ℕ) (R E i : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => match revScores q r degrees fs R E i n with
    | [] => []
    | h :: t => nextScore q r degrees fs R E i n h :: h :: t

theorem revScores_eq (q r : ℕ) (degrees fs : List ℕ) (R E i : ℕ) : ∀ n,
    revScores q r degrees fs R E i n =
      ((List.range (n + 1)).map (score q r degrees fs R E i)).reverse
  | 0 => by simp [revScores, score]
  | n + 1 => by
    have e1 : ∀ m, ((List.range (m + 1)).map (score q r degrees fs R E i)).reverse =
        score q r degrees fs R E i m :: ((List.range m).map (score q r degrees fs R E i)).reverse := by
      intro m; simp [List.range_succ]
    rw [revScores, revScores_eq q r degrees fs R E i n, e1 n, e1 (n + 1), e1 n]
    dsimp only
    congr 1
    cases n with
    | zero => rfl
    | succ j => rfl

theorem scores_get (q r : ℕ) (degrees fs : List ℕ) (R E i j : ℕ) (hj : j < q + 1) :
    (revScores q r degrees fs R E i q).reverse.toArray[j]? = some (score q r degrees fs R E i j) := by
  rw [revScores_eq, List.reverse_reverse]
  simp [hj]

/-- Per cut `R < RB` and slot `E < EB`, built on first use: the scores of the rows of the layers
`1 … R` at radii `0 … q`. -/
abbrev Tbl := Array (Array (Thunk (Array (Array ℕ))))

def mkT (q r : ℕ) (degrees fs : List ℕ) (RB EB : ℕ) : Tbl :=
  Array.ofFn (n := RB) fun R => Array.ofFn (n := EB) fun E => Thunk.mk fun _ =>
    Array.ofFn (n := R) fun i => (revScores q r degrees fs R E (i + 1) q).reverse.toArray

/-- A weight read from the table, computed directly outside it. -/
def look (T : Tbl) (q r : ℕ) (degrees fs : List ℕ) (R E i a : ℕ) : ℕ :=
  match T[R]? with
  | none => wt q r degrees fs R E i a
  | some TR => match TR[E]? with
    | none => wt q r degrees fs R E i a
    | some TE => match TE.get[i]? with
      | none => wt q r degrees fs R E i a
      | some row => match row[a]?, row[q - a]? with
        | some u, some v => u + v + 2
        | _, _ => wt q r degrees fs R E i a

theorem look_mkT (q r : ℕ) (degrees fs : List ℕ) (RB EB R E i a : ℕ) :
    look (mkT q r degrees fs RB EB) q r degrees fs R E i a = wt q r degrees fs R E i a := by
  by_cases hR : R < RB
  · by_cases hE : E < EB
    · by_cases hi : i < R
      · by_cases ha : a < q + 1
        · simp [look, mkT, Thunk.get, hR, hE, hi, scores_get _ _ _ _ _ _ _ _ ha,
            scores_get _ _ _ _ _ _ _ (q - a) (by omega : q - a < q + 1), wt]
        · simp [look, mkT, Thunk.get, hR, hE, hi, scores_get _ _ _ _ _ _ _ (q - a) (by omega : q - a < q + 1)]
          rw [revScores_eq, List.reverse_reverse]
          simp [ha]
      · simp [look, mkT, Thunk.get, hR, hE, hi]
    · simp [look, mkT, hR, hE]
  · simp [look, mkT, hR]

def ReachCutF (T : Tbl) (q r : ℕ) (degrees fs ws : List ℕ) (last R a : ℕ) : Prop :=
  1 ≤ R ∧ R ≤ ws.length ∧ R + 1 ≤ q ∧ 1 ≤ a ∧ a + a ≤ q ∧
    (ws.take R).sum * ((ws.take R).sum + 1) <
      ∑ i ∈ range R, ws.getD i 0 * look T q r degrees fs R (slot ws last R) i a

instance {T q r degrees fs ws last R a} : Decidable (ReachCutF T q r degrees fs ws last R a) := by
  unfold ReachCutF; infer_instance

def ReachDeadFP (T : Tbl) (q r : ℕ) (degrees fs ws : List ℕ) (last : ℕ) : Prop :=
  ∃ R ∈ range (ws.length + 1), ∃ a ∈ range (q / 2 + 1), ReachCutF T q r degrees fs ws last R a

instance {T q r degrees fs ws last} : Decidable (ReachDeadFP T q r degrees fs ws last) := by
  unfold ReachDeadFP; infer_instance

/-- The cut `R`, radius `a`, with list loops. -/
def cutL (T : Tbl) (q r : ℕ) (degrees fs ws : List ℕ) (last R a : ℕ) : Bool :=
  decide (1 ≤ R ∧ R ≤ ws.length ∧ R + 1 ≤ q ∧ 1 ≤ a ∧ a + a ≤ q) &&
    (let S := (ws.take R).sum
     let E := slot ws last R
     decide (S * (S + 1) < ((List.range R).map (fun i => ws.getD i 0 * look T q r degrees fs R E i a)).sum))

def ReachDeadF (T : Tbl) (q r : ℕ) (degrees fs ws : List ℕ) (last : ℕ) : Bool :=
  (List.range (ws.length + 1)).any fun R => (List.range (q / 2 + 1)).any fun a =>
    cutL T q r degrees fs ws last R a

theorem sum_range_list (n : ℕ) (f : ℕ → ℕ) : ∑ i ∈ range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem cutL_eq (T : Tbl) (q r : ℕ) (degrees fs ws : List ℕ) (last R a : ℕ) :
    cutL T q r degrees fs ws last R a = decide (ReachCutF T q r degrees fs ws last R a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [cutL, ReachCutF, sum_range_list, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem reachDeadF_iff (T : Tbl) (q r : ℕ) (degrees fs ws : List ℕ) (last : ℕ) :
    ReachDeadF T q r degrees fs ws last = true ↔ ReachDeadFP T q r degrees fs ws last := by
  simp only [ReachDeadF, ReachDeadFP, List.any_eq_true, List.mem_range, cutL_eq, decide_eq_true_eq,
    Finset.mem_range]

theorem reachCutF_iff (q r : ℕ) (degrees fs ws : List ℕ) (last RB EB R a : ℕ) :
    ReachCutF (mkT q r degrees fs RB EB) q r degrees fs ws last R a ↔
      ReachCut q r degrees fs ws last R a := by
  simp only [ReachCutF, ReachCut, total, look_mkT, wt]

theorem reachDeadF_eq (q r : ℕ) (degrees fs ws : List ℕ) (last RB EB : ℕ) :
    ReachDeadF (mkT q r degrees fs RB EB) q r degrees fs ws last = ReachDead q r degrees fs ws last := by
  rw [Bool.eq_iff_iff, reachDeadF_iff]
  simp only [ReachDeadFP, ReachDead, ReachDeadP, reachCutF_iff, decide_eq_true_eq]

def Dead3F (T : Tbl) (q r : ℕ) (degrees fs ws : List ℕ) (last : ℕ) : Bool :=
  Dead2 q r degrees ws last || ReachDeadF T q r degrees fs ws last

theorem dead3F_eq (q r : ℕ) (degrees fs ws : List ℕ) (last RB EB : ℕ) :
    Dead3F (mkT q r degrees fs RB EB) q r degrees fs ws last = Dead3 q r degrees fs ws last := by
  simp only [Dead3F, Dead3, reachDeadF_eq]

/-! ### Dead prefixes -/

/-- The peel at `j` reads only the first `j + 2` widths. -/
def PeelAt (q r : ℕ) (degrees pre : List ℕ) (j : ℕ) : Prop :=
  j + 1 < pre.length ∧ ∃ t ∈ degrees, 1 ≤ t ∧ t + pre.getD (j + 1) 0 ≤ r ∧
    0 < (pre.take (j + 1)).sum ∧ (pre.take (j + 1)).sum ≤ q * t ∧ j + 2 ≤ q

instance {q r degrees pre j} : Decidable (PeelAt q r degrees pre j) := by
  unfold PeelAt; infer_instance

theorem peel_of_at {q r : ℕ} {degrees pre : List ℕ} {j : ℕ} (rest : List ℕ) (last : ℕ)
    (h : PeelAt q r degrees pre j) : Peel q r degrees (pre ++ rest) last := by
  obtain ⟨len, t, ht, t1, tr, pos, cap, jq⟩ := h
  have tk : (pre ++ rest).take (j + 1) = pre.take (j + 1) := List.take_append_of_le_length (by omega)
  refine ⟨j, mem_range.mpr (by simp; omega), t, ht, t1, ?_, by rw [tk]; exact pos,
    by rw [tk]; exact cap, jq⟩
  unfold slot
  rw [getD_pre last 0 len]
  exact tr

/-- Every next width below `peelCap pre` makes the peel at the newest slot hold. -/
def peelCap (q r : ℕ) (degrees pre : List ℕ) : ℕ :=
  if 0 < pre.sum ∧ pre.length + 1 ≤ q ∧ 1 ≤ pre.length then
    (degrees.map (fun t => if 1 ≤ t ∧ t ≤ r ∧ pre.sum ≤ q * t then r + 1 - t else 0)).foldr max 0
  else 0

theorem peel_of_cap {q r : ℕ} {degrees pre : List ℕ} {a : ℕ} (h : a < peelCap q r degrees pre) :
    PeelAt q r degrees (pre ++ [a]) (pre.length - 1) := by
  unfold peelCap at h
  split at h
  next cond =>
    obtain ⟨pos, lq, l1⟩ := cond
    rcases foldr_max_cases ((degrees.map (fun t => if 1 ≤ t ∧ t ≤ r ∧ pre.sum ≤ q * t then
      r + 1 - t else 0))) with e | e
    · omega
    · obtain ⟨t, ht, et⟩ := List.mem_map.mp e
      split at et
      next ct =>
        have tk : (pre ++ [a]).take (pre.length - 1 + 1) = pre := by
          rw [Nat.sub_add_cancel l1]; simp
        have gd : (pre ++ [a]).getD (pre.length - 1 + 1) 0 = a := by
          rw [Nat.sub_add_cancel l1]; simp
        refine ⟨by simp; omega, t, ht, ct.1, by rw [gd]; omega, by rw [tk]; exact pos,
          by rw [tk]; exact ct.2.2, by omega⟩
      next => omega
  next => omega

theorem dead3_of_cap (T : Tbl) (q r : ℕ) (degrees fs : List ℕ) (c last : ℕ) (pre : List ℕ)
    (a : ℕ) (rest : List ℕ) (h : a < peelCap q r degrees pre) :
    Dead3F T q r degrees fs ((pre ++ a :: rest) ++ [c]) last = true := by
  have p := peel_of_at (rest ++ [c]) last (peel_of_cap h)
  have e : pre ++ [a] ++ (rest ++ [c]) = (pre ++ a :: rest) ++ [c] := by simp
  rw [e] at p
  have : Dead q r degrees ((pre ++ a :: rest) ++ [c]) last = true :=
    decide_eq_true (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl p)))))))
  simp only [Dead3F, Dead2, this, Bool.true_or]

theorem dead_of_cap (q r : ℕ) (degrees : List ℕ) (c last : ℕ) (pre : List ℕ)
    (a : ℕ) (rest : List ℕ) (h : a < peelCap q r degrees pre) :
    Dead q r degrees ((pre ++ a :: rest) ++ [c]) last = true := by
  have p := peel_of_at (rest ++ [c]) last (peel_of_cap h)
  have e : pre ++ [a] ++ (rest ++ [c]) = (pre ++ a :: rest) ++ [c] := by simp
  rw [e] at p
  exact decide_eq_true (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl p)))))))

/-! ### The reach climb, fast -/

def deadAll3F (T : Tbl) (q r : ℕ) (degrees fs : List ℕ) (k x c F : ℕ) : Bool :=
  deadAllF r fs (fun ws => Dead3F T q r degrees fs (ws ++ [c]) (F - x))
    (fun _ => false) (peelCap q r degrees) k (x - 1 - c)

theorem deadAll3F_eq (q r : ℕ) (degrees fs : List ℕ) (RB EB k x c F : ℕ) :
    deadAll3F (mkT q r degrees fs RB EB) q r degrees fs k x c F = deadAll3 q r degrees fs k x c F := by
  rw [deadAll3F, deadAllF_eq _ _ _ _ _
    (fun _ _ h => by simp at h)
    (fun pre a rest h => dead3_of_cap _ q r degrees fs c (F - x) pre a rest h)]
  unfold deadAll3
  refine all_congr' (fun ws _ => ?_)
  rw [dead3F_eq]

def CanRaise3F (T : Tbl) (q r k : ℕ) (fs : List ℕ) (F : ℕ) (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (fs.getD (k + 1) 0) F, ∀ c ∈ range (x - fs.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAll3F T q r (bank.map Comparison.degree) fs k x c F) = true

instance {T q r k fs F bank} : Decidable (CanRaise3F T q r k fs F bank) := by
  unfold CanRaise3F; infer_instance

theorem canRaise3F_iff (q r k : ℕ) (fs : List ℕ) (F : ℕ) (bank : List Comparison) (RB EB : ℕ) :
    CanRaise3F (mkT q r (bank.map Comparison.degree) fs RB EB) q r k fs F bank ↔
      CanRaise3 q r k fs F bank := by
  simp only [CanRaise3F, CanRaise3, deadAll3F_eq]

def climb3F (T : Tbl) (q r k : ℕ) (fs : List ℕ) (bank : List Comparison) (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 =>
    if CanRaise3F T q r k fs value bank then climb3F T q r k fs bank (value + 1) fuel else value

theorem climb3F_eq (q r k : ℕ) (fs : List ℕ) (bank : List Comparison) (RB EB : ℕ) :
    ∀ fuel value, climb3F (mkT q r (bank.map Comparison.degree) fs RB EB) q r k fs bank value fuel =
      climb3 q r k fs bank value fuel := by
  intro fuel
  induction fuel with
  | zero => intro value; rfl
  | succ n ih =>
    intro value
    simp only [climb3F, climb3]
    by_cases h : CanRaise3 q r k fs value bank
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((canRaise3F_iff ..).mpr h)), ite_eq_left_of_eq_true _ _ (eq_true h), ih]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h ((canRaise3F_iff ..).mp h'))),
        ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- The table at radius `k + 2`: cuts and rows up to `k + 1`, slots up to `2 r + 1`. -/
def tableAt (q r : ℕ) (bank : List Comparison) (fs : List ℕ) (k : ℕ) : Tbl :=
  mkT q r (bank.map Comparison.degree) fs (k + 2) (2 * r + 2)

def layers3F (q r : ℕ) (bank : List Comparison) : ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let fs := layers3F q r bank k
    fs ++ [climb3F (tableAt q r bank fs k) q r k fs bank (fs.getD (k + 1) 0) r]

theorem layers3F_eq (q r : ℕ) (bank : List Comparison) :
    ∀ k, layers3F q r bank k = layers3 q r bank k
  | 0 => rfl
  | k + 1 => by
    simp only [layers3F, layers3, tableAt, layers3F_eq q r bank k, climb3F_eq]

theorem layers3_length (q r : ℕ) (bank : List Comparison) :
    ∀ k, (layers3 q r bank k).length = k + 2
  | 0 => rfl
  | k + 1 => by simp [layers3, layers3_length q r bank k]

/-- Earlier floors are kept by later radii. -/
theorem layers3_getD_le (q r : ℕ) (bank : List Comparison) {k K i : ℕ} (kK : k ≤ K)
    (ik : i < k + 2) : (layers3 q r bank K).getD i 0 = (layers3 q r bank k).getD i 0 := by
  induction K, kK using Nat.le_induction with
  | base => rfl
  | succ K kK ih =>
    simp only [layers3]
    rw [List.getD_append _ _ _ _ (by rw [layers3_length]; omega), ih]

/-- `boundAt3`, with the floors computed once. -/
def boundAt3F (q r c : ℕ) : ℕ :=
  let fs := layers3F q r (library q c) (q / 2)
  let left := fs.getD (q / 2) 0
  let right := if q - q / 2 = q / 2 then fs.getD (q / 2) 0 else fs.getD (q / 2 + 1) 0
  left + right + (if 2 * (q / 2 / 2) = q / 2 ∧ left + 2 ≤ 2 * fs.getD (q / 2 / 2) 0 then 1 else 0) - 2

theorem boundAt3F_eq (q r c : ℕ) : boundAt3F q r c = ShapeClimbAt3.boundAt3 q r c := by
  simp only [boundAt3F, ShapeClimbAt3.boundAt3, ShapeClimbAt3.resultAt3, ShapeClimbAt3.middle3,
    ShapeClimbAt3.strictGainAt3, layers3F_eq,
    layers3_getD_le q r (library q c) (Nat.div_le_self (q / 2) 2) (by omega : q / 2 / 2 < q / 2 / 2 + 2)]
  congr

theorem boundAt3F_sound {q r c} (hq : 2 ≤ q) (hr : 0 < r) (cr : c < r)
    (known : ∀ t, t ≤ c → NoHost q t)
    {D V} (free : QFree D V q) (ne : V.Nonempty) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) :
    boundAt3F q r c < V.card := by
  rw [boundAt3F_eq]
  exact ShapeClimbAt3.boundAt3_sound hq hr cr known free ne deg

/-! ### The committed-checker climb (`ShapeClimbAt.boundAt`), fast -/

def deadAllF1 (q r : ℕ) (degrees fs : List ℕ) (k x c F : ℕ) : Bool :=
  deadAllF r fs (fun ws => Dead q r degrees (ws ++ [c]) (F - x)) (fun _ => false)
    (peelCap q r degrees) k (x - 1 - c)

theorem deadAllF1_eq (q r : ℕ) (degrees fs : List ℕ) (k x c F : ℕ) :
    deadAllF1 q r degrees fs k x c F = deadAll q r degrees fs k x c F :=
  deadAllF_eq _ _ _ _ _ (fun _ _ h => by simp at h)
    (fun pre a rest h => dead_of_cap q r degrees c (F - x) pre a rest h) _ _

def CanRaiseF1 (q r k : ℕ) (fs : List ℕ) (F : ℕ) (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (fs.getD (k + 1) 0) F, ∀ c ∈ range (x - fs.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAllF1 q r (bank.map Comparison.degree) fs k x c F) = true

instance {q r k fs F bank} : Decidable (CanRaiseF1 q r k fs F bank) := by
  unfold CanRaiseF1; infer_instance

theorem canRaiseF1_iff (q r k : ℕ) (fs : List ℕ) (F : ℕ) (bank : List Comparison) :
    CanRaiseF1 q r k fs F bank ↔ CanRaise' q r k fs F bank := by
  simp only [CanRaiseF1, CanRaise', deadAllF1_eq]

def climbF1 (q r k : ℕ) (fs : List ℕ) (bank : List Comparison) (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 =>
    if CanRaiseF1 q r k fs value bank then climbF1 q r k fs bank (value + 1) fuel else value

theorem climbF1_eq (q r k : ℕ) (fs : List ℕ) (bank : List Comparison) :
    ∀ fuel value, climbF1 q r k fs bank value fuel = climb' q r k fs bank value fuel := by
  intro fuel
  induction fuel with
  | zero => intro value; rfl
  | succ n ih =>
    intro value
    simp only [climbF1, climb']
    by_cases h : CanRaise' q r k fs value bank
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((canRaiseF1_iff ..).mpr h)), ite_eq_left_of_eq_true _ _ (eq_true h), ih]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h ((canRaiseF1_iff ..).mp h'))),
        ite_eq_right_of_eq_false _ _ (eq_false h)]

def layersF1 (q r : ℕ) (bank : List Comparison) : ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let fs := layersF1 q r bank k
    fs ++ [climbF1 q r k fs bank (fs.getD (k + 1) 0) r]

theorem layersF1_eq (q r : ℕ) (bank : List Comparison) :
    ∀ k, layersF1 q r bank k = layers' q r bank k
  | 0 => rfl
  | k + 1 => by
    simp only [layersF1, layers', layersF1_eq q r bank k, climbF1_eq]

theorem layers'_length (q r : ℕ) (bank : List Comparison) :
    ∀ k, (layers' q r bank k).length = k + 2
  | 0 => rfl
  | k + 1 => by simp [layers', layers'_length q r bank k]

theorem layers'_getD_le (q r : ℕ) (bank : List Comparison) {k K i : ℕ} (kK : k ≤ K)
    (ik : i < k + 2) : (layers' q r bank K).getD i 0 = (layers' q r bank k).getD i 0 := by
  induction K, kK using Nat.le_induction with
  | base => rfl
  | succ K kK ih =>
    simp only [layers']
    rw [List.getD_append _ _ _ _ (by rw [layers'_length]; omega), ih]

/-- `ShapeClimbAt.boundAt`, with the floors computed once. -/
def boundAtF (q r c : ℕ) : ℕ :=
  let fs := layersF1 q r (library q c) (q / 2)
  let left := fs.getD (q / 2) 0
  let right := if q - q / 2 = q / 2 then fs.getD (q / 2) 0 else fs.getD (q / 2 + 1) 0
  left + right + (if 2 * (q / 2 / 2) = q / 2 ∧ left + 2 ≤ 2 * fs.getD (q / 2 / 2) 0 then 1 else 0) - 2

theorem boundAtF_eq (q r c : ℕ) : boundAtF q r c = ShapeClimbAt.boundAt q r c := by
  simp only [boundAtF, ShapeClimbAt.boundAt, ShapeClimbAt.resultAt, middle',
    ShapeClimbAt.strictGainAt, layersF1_eq,
    layers'_getD_le q r (library q c) (Nat.div_le_self (q / 2) 2) (by omega : q / 2 / 2 < q / 2 / 2 + 2)]
  congr

theorem boundAtF_sound {q r c} (hq : 2 ≤ q) (hr : 0 < r) (cr : c < r)
    (known : ∀ t, t ≤ c → NoHost q t)
    {D V} (free : QFree D V q) (ne : V.Nonempty) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) :
    boundAtF q r c < V.card := by
  rw [boundAtF_eq]
  exact ShapeClimbAt.boundAt_sound hq hr cr known free ne deg

/-! ### The guarded bounds of the coverage map -/

def guardedBoundAt3F (q r limit span : ℕ) : ℕ :=
  if r ≤ limit + span then boundAt3F q r (min (r - 1) (limit - 1)) else 0

theorem guardedBoundAt3F_eq (q r limit span : ℕ) :
    guardedBoundAt3F q r limit span = ShapeClimbAt3.guardedBoundAt3 q r limit span := by
  simp only [guardedBoundAt3F, ShapeClimbAt3.guardedBoundAt3, boundAt3F_eq]

def guardedBoundAtF (q r limit span : ℕ) : ℕ :=
  if r ≤ limit + span then boundAtF q r (min (r - 1) (limit - 1)) else 0

theorem guardedBoundAtF_eq (q r limit span : ℕ) :
    guardedBoundAtF q r limit span = ShapeClimbAt.guardedBoundAt q r limit span := by
  simp only [guardedBoundAtF, ShapeClimbAt.guardedBoundAt, boundAtF_eq]

#print axioms deadAllF_eq
#print axioms boundAt3F_eq
#print axioms boundAt3F_sound
#print axioms boundAtF_eq
#print axioms boundAtF_sound
#print axioms guardedBoundAt3F_eq
#print axioms guardedBoundAtF_eq

end LeanCH.BR.ShapeClimbFast
