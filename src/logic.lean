
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  intro np,
  apply np hp,
end

theorem doubleneg_elim : -- "manchado" pela RAA (Redução ao absurdo)
  ¬¬P → P  :=
begin
  intro nnp,
  by_contradiction pboom,
  apply nnp pboom,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
    -- parte ¬¬P → P:
    apply doubleneg_elim P,
    -- parte P → ¬¬P:
    apply doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p_ou_q,
  cases p_ou_q with hp hq,
    -- caso P:
    right,
    exact hp,
    -- caso Q:
    left,
    exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro p_e_q,
  cases p_e_q with hp hq,
  split,
    -- parte q:
    exact hq,
    -- parte P:
    exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro np_ou_q,
  intro hp,
  cases np_ou_q with np hq,

    -- caso ¬P: 
    have boom : false := np hp,
    exfalso,
    exact boom,

    -- caso Q:
    exact hq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro p_ou_q,
  intro np,
  cases p_ou_q with hp hq,
    -- caso P:
    contradiction,

    -- caso Q:
    exact hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro p_implies_q,
  intro nq,
  intro hp,
  have hq : Q := p_implies_q hp,
  contradiction,   
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro nq_implies_np,
  intro hp,
  by_contradiction nq,
  have np : ¬P := nq_implies_np nq,
  contradiction, 
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
    -- parte (P → Q) → ¬Q → ¬P:
    exact impl_as_contrapositive P Q,

    -- parte (¬Q → ¬P) → P → Q:
    exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro nn_p_ou_np,
  apply nn_p_ou_np,
  right,
  intro hp,
  apply nn_p_ou_np,
  left,
  exact hp,
end

------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro hi,
  intro np,
  apply np,
  apply hi,
  intro hp,
  contradiction,
end

------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro p_ou_q,
  intro n_np_e_nq,
  cases n_np_e_nq with np nq,
  cases p_ou_q with hp hq,
    -- caso P:
    contradiction,

    -- caso Q:
    contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro p_e_q,
  cases p_e_q with hp hq,
  intro np_ou_nq,
  cases np_ou_nq with np nq,
    -- caso ¬P:
    contradiction,

    -- caso ¬Q:
    contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro n_p_ou_q,
  split,
    -- parte ¬P:
    intro hp,
    have p_ou_q : (P∨Q),
      left,
      exact hp,
    have boom : false := n_p_ou_q p_ou_q,
    exact boom,  

    -- parte ¬Q:
    intro hq,
    have p_ou_q: (P∨Q),
      right,
      exact hq, 
    have boom : false := n_p_ou_q p_ou_q,
    exact boom,   
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro np_e_nq,
  cases np_e_nq with np nq,
  intro p_ou_q,
  cases p_ou_q with hp hq,
    -- caso P:
      have boom : false := np hp,
      exact boom,

    -- caso Q:
      have boom : false := nq hq,
      exact boom,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro n_p_e_q,
  by_cases hq : Q,
    -- caso Q:
    right,
    intro hp,
    have p_e_q : (P∧Q),
      split,
      -- parte P:
      exact hp,

      -- parte Q:
      exact hq,
    have boom : false := n_p_e_q p_e_q,
    exact boom,

    -- caso ¬Q:
    left,
    exact hq,
end


theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nq_ou_np,
  intro p_e_q,
  cases p_e_q with hp hq, -- uso do ∧ 
  cases nq_ou_np with nq np, -- uso do ∨
    -- caso ¬Q:
    contradiction,

    -- caso ¬P:
    contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
    -- parte ¬(P ∧ Q) → ¬Q ∨ ¬P:
    exact demorgan_conj P Q,

    -- parte ¬Q ∨ ¬P → ¬(P ∧ Q):
    exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
    -- parte ¬(P ∨ Q) → ¬P ∧ ¬Q:
    exact demorgan_disj P Q,

    -- parte ¬P ∧ ¬Q → ¬(P ∨ Q):
    exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro p_e_qour,
  cases p_e_qour with hp q_ou_r, -- Uso da conjunção (Extrair)
  cases q_ou_r with hq hr,
    -- caso Q:
    left,
    split, -- P∧Q: 
      -- parte P:
      exact hp,
      -- parte Q:
      exact hq,
    
    -- caso R:
    right,
    split, -- P∧R:
      -- parte P:
      exact hp,
      -- parte R:
      exact hr,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pEq_ou_pEr,
  cases pEq_ou_pEr with p_e_q p_e_r,
    -- caso P∧Q:
    cases p_e_q with hp hq,
    split,
      -- parte P:
      exact hp,
      -- parte Q∨R:
      left,
      exact hq,
    
    -- caso P∧R:
    cases p_e_r with hp hr,
    split,
      -- parte P:
      exact hp,
      -- parte Q∨R:
      right,
      exact hr,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro p_ou_qEr,
  cases p_ou_qEr with hp q_e_r,
    -- caso P:
    split,
      -- parte P∨Q:
      left,
      exact hp,
      -- parte P∨R:
      left,
      exact hp,

    -- caso Q∧R:
    cases q_e_r with hq hr,
    split, 
      -- parte P∨Q:
      right,
      exact hq,
      -- parte P∨R:
      right,
      exact hr, 
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pOUq_e_pOUr,
  cases pOUq_e_pOUr with p_ou_q p_ou_r,
  cases p_ou_q with hp hq,
    -- caso P:
    cases p_ou_r with hp hr,
      -- caso P:
      left,
      exact hp,
      -- caso R:
      left,
      exact hp,
    -- caso Q:
    cases p_ou_r with hp hr,
      -- caso P:
      left,
      exact hp,
      -- caso R:
      right,
      split,
        -- parte Q:
        exact hq,
        -- parte R:
        exact hr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pEq_implies_r,
  intro hp,
  intro hq,
  have p_e_q : (P∧Q),
    split,
      -- parte P:
      exact hp,
      -- parte Q:
      exact hq, 
  apply pEq_implies_r p_e_q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro h1,
  intro p_e_q,
  cases p_e_q with hp hq,
  apply h1 hp hq,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  exact hp,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  exact hq,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro p_e_q,
  cases p_e_q with hp hq,
  exact hp,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro p_e_q,
  cases p_e_q with hp hq,
  exact hq,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
    -- parte P ∧ P → P:
    intro p_e_p,
    cases p_e_p with hp hp,
    exact hp,
    
    -- parte P → P ∧ P:
    intro hp,
    split,
      -- parte P:
      exact hp,
      -- parte P:
      exact hp,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
    -- parte P ∨ P → P:
    intro p_ou_p,
    cases p_ou_p with hp hp,
      -- caso P:
      exact hp,
      -- caso P:
      exact hp,
      
    -- parte P → P ∨ P:
    intro hp,
    left,
    exact hp,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h1,
  intro x,
  intro px,
  apply h1,
  existsi x,
  exact px,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h1,
  intro h2,
  cases h2 with x px,
  apply h1 x px,  
end

theorem demorgan_forall : -- Manchado (RAA)
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h1,
  by_contradiction h2,
  apply h1,
  intro x,
  by_contradiction npx,
  apply h2,
  existsi x,
  exact npx,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h1,
  intro h2,
  cases h1 with x npx,
  have px : P x := h2 x,
  apply npx px,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
    -- parte :
    apply demorgan_forall U P,
    -- parte :
    apply demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
    -- parte (¬∃ (x : U), P x) → ∀ (x : U), ¬P x:
    apply demorgan_exists U P,
    -- parte (∀ (x : U), ¬P x) → (¬∃ (x : U), P x):
    apply demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro h1,
  intro h2,
  cases h1 with x px,
  apply h2 x px,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro h1, 
  intro h2,
  cases h2 with x npx,
  have px : P x := h1 x,
  have boom: false := npx px,
  exact boom,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h1,
  intro x,
  by_contradiction npx,
  apply h1,
  existsi x,
  exact npx,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h1,
  by_contradiction h2,
  apply h1,
  intro x,
  intro px,
  apply h2,
  existsi x,
  exact px,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
    -- parte :
    apply forall_as_neg_exists U P,
    -- parte :
    apply forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
    -- parte :
    apply exists_as_neg_forall U P,
    -- parte :
    apply exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h1,
  cases h1 with x pqx,
  cases pqx with px qx,
  split,
    -- parte (∃x, P x):
    existsi x,
    exact px,
    -- parte (∃x, Q x):
    existsi x,
    exact qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h1,
  cases h1 with x pxOUqx,
  cases pxOUqx with px qx,
    -- caso P x:
    left,
    existsi x,
    exact px,
    -- caso Q x:
    right,
    existsi x,
    exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h1,
  cases h1 with epx eqx,
    -- caso ∃x, P x:
    cases epx with x px,
    existsi x,
    left,
    exact px, 
    -- caso ∃x, Q x:
    cases eqx with x qx,
    existsi x,
    right,
    exact qx, 
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h1,
  split,
    -- parte ∀x, P x:
    intro x,
    have pxEqx : P x ∧ Q x := h1 x,
    cases pxEqx with px qx,
    exact px,
    -- parte ∀x, Q x:
    intro x,
    have pxEqx : P x ∧ Q x := h1 x,
    cases pxEqx with px qx,
    exact qx,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h1,
  cases h1 with apx aqx,
  intro x,
  split,
    -- parte ∀x, P x:
    have px : P x := apx x,
    exact px,
    -- parte ∀x, Q x:
    have qx : Q x := aqx x,
    exact qx,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h1,
  cases h1 with apx aqx,
    -- caso ∀x, P x:
    intro x,
    left,
    have px : P x := apx x,
    exact px,
    -- caso ∀x, Q x:
    intro x,
    right,
    have qx : Q x := aqx x,
    exact qx,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
