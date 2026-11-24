import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1669_641
    (hSibling : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (hNonmonotone : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      ¬ (∀ (x y : Fin 9 → Bool) (b c : Bool), x ≤ y → b ≤ c →
        D.eval (List.ofFn x ++ [b]) ≤ D.eval (List.ofFn y ++ [c])) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 && x 3]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      15 ≤ D.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C basis first computes
  obtain ⟨gs, out⟩ := C
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have kept (l : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
      (hi : i < w.length) : (l.foldl step w).getD i false = w.getD i false := by
    induction l generalizing w with
    | nil => rfl
    | cons g l ih =>
      change (l.foldl step (step w g)).getD i false = _
      rw [ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  cases gs with
  | nil =>
    have bad := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at bad
    rw [List.getD_eq_default _ _ (by simp)] at bad
    contradiction
  | cons a tail =>
    have firstValue (x : Fin 9 → Bool) :
        step (List.ofFn x) a = List.ofFn x ++ [x 0 && x 3] := by
      have h := first x
      change (tail.foldl step (step (List.ofFn x) a)).getD 9 false = _ at h
      rw [kept tail _ 9 (by simp [step])] at h
      simp only [step, List.getD_append_right _ _ _ _ (by simp : (List.ofFn x).length ≤ 9),
        List.length_ofFn, Nat.sub_self] at h
      change _ ++ [_] = _ ++ [_]
      have val : a.op.eval (a.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 3) := h
      rw [val]
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨tail, out⟩
    let T (x : Fin 9 → Bool) (b : Bool) := D.eval (List.ofFn x ++ [b])
    let F : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    have tailBasis : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      exact basis g (List.mem_cons_of_mem _ hg)
    have tailComputes (x : Fin 9 → Bool) : T x (x 0 && x 3) = F x := by
      have h := congrFun computes x
      change (tail.foldl step (step (List.ofFn x) a)).getD out false = _ at h
      rw [firstValue] at h
      exact h
    by_cases mono : ∀ (x y : Fin 9 → Bool) (b c : Bool),
        x ≤ y → b ≤ c → T x b ≤ T y c
    · let E : PEqualNP.CircuitLowerBounds.Gate := ⟨.and, [0, 4]⟩
      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨E :: tail, out⟩
      have firstEdge (x : Fin 9 → Bool) :
          step (List.ofFn x) E = List.ofFn x ++ [x 0 && x 4] := by
        simp [step, E, PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD]
      have cfBasis : PEqualNP.MetaComplexity.FanInTwo C' := by
        intro g hg
        change g ∈ E :: tail at hg
        rcases List.mem_cons.mp hg with rfl | hg
        · simp [E]
        · exact tailBasis g hg
      have cfWire (x : Fin 9 → Bool) :
          (C'.wires (List.ofFn x)).getD 9 false = (x 0 && x 4) := by
        change (tail.foldl step (step (List.ofFn x) E)).getD 9 false = _
        rw [firstEdge, kept tail _ 9 (by simp)]
        simp
      have minterm (x : Fin 9 → Bool) (i j : Fin 9) (hi : x i = true) (hj : x j = true)
          (hm : F (fun k => decide (k = i ∨ k = j)) = true)
          (hp : (decide ((0 : Fin 9) = i ∨ (0 : Fin 9) = j) &&
            decide ((3 : Fin 9) = i ∨ (3 : Fin 9) = j)) = false) :
          T x (x 0 && x 4) = true := by
        let y : Fin 9 → Bool := fun k => decide (k = i ∨ k = j)
        have hy : y ≤ x := by
          intro k
          by_cases h : k = i ∨ k = j
          · rcases h with rfl | rfl <;> simp [hi, hj]
          · push_neg at h
            simp [y, h.1, h.2]
        have hv := tailComputes y
        change (y 0 && y 3) = false at hp
        change F y = true at hm
        rw [hp, hm] at hv
        have ineq := mono y x false (x 0 && x 4) hy (by simp)
        rw [hv] at ineq
        cases ht : T x (x 0 && x 4) with
        | false => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa only [ht] using ineq))
        | true => rfl
      have cfComputes : PEqualNP.MetaComplexity.circuitFun 9 C' = F := by
        funext x
        change (tail.foldl step (step (List.ofFn x) E)).getD out false = F x
        rw [firstEdge]
        change T x (x 0 && x 4) = F x
        cases h : F x with
        | false =>
          have hq : (x 0 && x 4) = false := by
            cases hq : (x 0 && x 4)
            · rfl
            · have hr : (x 4 && x 0) = true := by simpa [Bool.and_comm] using hq
              simp [F, hr] at h
          rw [hq]
          have ineq := mono x x false (x 0 && x 3) le_rfl (by simp)
          rw [tailComputes, h] at ineq
          cases ht : T x false with
          | false => rfl
          | true => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa only [ht] using ineq))
        | true =>
          simp only [F, Bool.or_eq_true, Bool.and_eq_true, or_assoc] at h
          rcases h with h | h | h | h | h | h | h | h | h | h | h | h
          · exact minterm x 0 1 h.1 h.2 (by decide) (by decide)
          · exact minterm x 1 2 h.1 h.2 (by decide) (by decide)
          · exact minterm x 2 3 h.1 h.2 (by decide) (by decide)
          · exact minterm x 3 4 h.1 h.2 (by decide) (by decide)
          · exact minterm x 4 0 h.1 h.2 (by decide) (by decide)
          · exact minterm x 0 5 h.1 h.2 (by decide) (by decide)
          · exact minterm x 1 6 h.1 h.2 (by decide) (by decide)
          · exact minterm x 2 7 h.1 h.2 (by decide) (by decide)
          · exact minterm x 3 8 h.1 h.2 (by decide) (by decide)
          · exact minterm x 5 7 h.1 h.2 (by decide) (by decide)
          · exact minterm x 6 8 h.1 h.2 (by decide) (by decide)
          · exact minterm x 8 5 h.1 h.2 (by decide) (by decide)
      exact hSibling C' cfBasis cfWire cfComputes
    · have bound := hNonmonotone D tailBasis mono tailComputes
      change 15 ≤ tail.length at bound
      change 16 ≤ (a :: tail).length
      simp only [List.length_cons]
      omega
