(** * ImpCEvalFun: An Evaluation Function for Imp *)

(** We saw in the [Imp] chapter how a naive approach to defining a
    function representing evaluation for Imp runs into difficulties.
    There, we adopted the solution of changing from a functional to a
    relational definition of evaluation.  In this optional chapter, we
    consider strategies for getting the functional approach to
    work. *)

(* ################################################################# *)
(** * A Broken Evaluator *)

From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import Imp Maps.

(** Here was our first try at an evaluation function for commands,
    omitting [while]. *)

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ l := a1 }> =>
        (l !-> aeval st a1 ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | <{ if b then c1 else c2 end }> =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | <{ while b1 do c1 end }> =>
        st  (* bogus *)
  end.

(** As we remarked in chapter [Imp], in a traditional functional
    programming language like ML or Haskell we could write the while
    case as follows:

    | while b1 do c1 end =>
        if (beval st b1) then
          ceval_step1 st <{ c1; while b1 do c1 end }>
        else st

    Coq doesn't accept such a definition ([Error: Cannot guess
    decreasing argument of fix]) because the function we want to
    define is not guaranteed to terminate. Indeed, the changed
    [ceval_step1] function applied to the [loop] program from [Imp.v]
    would never terminate. Since Coq is not just a functional
    programming language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is an
    invalid(!) Coq program showing what would go wrong if Coq allowed
    non-terminating recursive functions:

     Fixpoint loop_false (n : nat) : False := loop_false n.

    That is, propositions like [False] would become
    provable (e.g., [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_step1] cannot be written in Coq -- at least not without
    one additional trick... *)

(* ################################################################# *)
(** * A Step-Indexed Evaluator *)

(** The trick we need is to pass an _additional_ parameter to the
    evaluation function that tells it how long to run.  Informally, we
    start the evaluator with a certain amount of "gas" in its tank,
    and we allow it to run until either it terminates in the usual way
    _or_ it runs out of gas, at which point we simply stop evaluating
    and say that the final result is the empty memory.  (We could also
    say that the result is the current state at the point where the
    evaluator runs out of gas -- it doesn't really matter because the
    result is going to be wrong in either case!) *)

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | <{ skip }> =>
          st
      | <{ l := a1 }> =>
          (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

(** _Note_: It is tempting to think that the index [i] here is
    counting the "number of steps of evaluation."  But if you look
    closely you'll see that this is not the case: for example, in the
    rule for sequencing, the same [i] is passed to both recursive
    calls.  Understanding the exact way that [i] is treated will be
    important in the proof of [ceval__ceval_step], which is given as
    an exercise below.

    One thing that is not so nice about this evaluator is that we
    can't tell, from its result, whether it stopped because the
    program terminated normally or because it ran out of gas.  Our
    next version returns an [option state] instead of just a [state],
    so that we can distinguish between normal and abnormal
    termination. *)

Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, standard, optional (pup_to_n)

    Write an Imp program that sums the numbers from [1] to
   [X] (inclusive -- i.e., [1 + 2 + ... + X]) in the variable [Y].  Make
   sure your solution satisfies the test that follows. *)

Definition pup_to_n : com :=
<{
  Y := 0;
  Z := X;
  while 1 <= Z do
    Y := Y + Z;
    Z := Z - 1;
    X := X - 1
  end}>.

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (peven)

    Write an [Imp] program that sets [Z] to [0] if [X] is even and
    sets [Z] to [1] otherwise.  Use [test_ceval] to test your
    program. *)

(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(** As for arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation would actually
    amount to the same thing in the end.  This section shows that this
    is the case. *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  - (* i = 0 -- contradictory *)
    intros c st st' H. discriminate H.

  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* skip *) apply E_Skip.
      + (* := *) apply E_Asgn. reflexivity.

      + (* ; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. assumption.
        * (* Otherwise -- contradiction *)
          discriminate H1.

      + (* if *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* while *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1 as H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. Qed.

(** **** Exercise: 4 stars, advanced (ceval_step__ceval_inf)

    Write an informal proof of [ceval_step__ceval], following the
    usual template.  (The template for case analysis on an inductively
    defined value should look the same as for induction, except that
    there is no induction hypothesis.)  Make your proof communicate
    the main ideas to a human reader; do not simply transcribe the
    steps of the formal proof. 


Theorem: For any command c, initial state st, and final state st', 
 if there exists a step-bound i such that the small-step evaluator ceval_step terminates (ceval_step st c i = Some st'), 
 then the big-step evaluator => also terminates with the same result (st =[ c ]=> st').

Proof: We proof it by induction on the step-bound i.

1. Base Case: i = 0
Analysis: By the definition of ceval_step, when i is 0, it always returns None.
Conclusion: The premise None = Some st' is a contradiction. So it holds vacuously.

2. Inductive Step: i = S i' 
Inductive Hypothesis (IH): 
  for any c_sub, st_a, st_b, if ceval_step st_a c_sub i' = Some st_b, then st_a =[ c_sub ]=> st_b.

To show this, we perform a case analysis on the structure of the command c:

2.1 Case: c = skip, the definition of ceval_step for skip is to immediately return Some st. 
Thus, our premise implies st' = st. This directly corresponds to the big-step rule E_Skip, 
which states st =[ skip ]=> st.

2.2 Case: c = x := a, The definition of ceval_step for assignment is to immediately return Some (x !-> aeval st a; st). 
Thus, our premise implies st' = (x !-> aeval st a; st). This directly corresponds to the big-step rule E_Asgn, 
which states st =[ x := a ]=> (x !-> aeval st a; st).

2.3 Case: c = c1 ; c2 (Sequence), For ceval_step to successfully evaluate c1 ; c2 in S i' steps, it must:
 (1)ceval_step st c1 i' = Some s for some intermediate state s and 
 (2)ceval_step s c2 i' = Some st'

By applying our Inductive Hypothesis (IH) to both (1) and (2), we get:
From (1): st =[ c1 ]=> s
From (2): s =[ c2 ]=> st'
The big-step rule E_Seq uses these two premises to conclude st =[ c1 ; c2 ]=> st'.

2.4 Case: c = if b then c1 else c2, ceval_step first evaluates the boolean b.
If beval st b = true: 
  The ceval_step definition simplifies, requiring ceval_step st c1 i' = Some st'. 
  By the IH, this implies st =[ c1 ]=> st'. This is exactly the premise needed for the E_IfTrue 
  rule to conclude st =[ if b then c1 else c2  ]=> st'.
If beval st b = false: 
  The ceval_step definition simplifies, requiring ceval_step st c2 i' = Some st'. 
  By the IH, this implies st =[ c2 ]=> st'. This is exactly the premise needed for the E_IfFalse 
  rule to conclude st =[ if b then c1 else c2 ]=> st'.

2.5 Case: c = while b do c_body, ceval_step first evaluates the boolean b.
If beval st b = false: ceval_step immediately terminates, returning Some st. 
Thus, our premise implies st' = st. This corresponds perfectly to the E_WhileFalse rule.

If beval st b = true: This is the key recursive case. 

For ceval_step to terminate, it must:
Successfully evaluate the loop body c_body from st within i' steps, 
  yielding an intermediate state s. (i.e., ceval_step st c_body i' = Some s)
Successfully evaluate the entire while loop again from s within i' steps, 
  yielding the final state st'. (i.e., ceval_step s (while b do c_body) i' = Some st')

By applying our Inductive Hypothesis (IH) to both (1) and (2), we get:
From (1): st =[ c_body ]=> s
From (2): s =[ while b do c_body ]=> st'
These are exactly the three premises required by the E_WhileTrue rule to conclude 
st =[ while... ]=> st'.

*)

(* Do not modify the following line: *)
Definition manual_grade_for_ceval_step__ceval_inf : option (nat*string) := None.
(** [] *)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    + (* skip *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* := *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.

    + (* if *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.

    + (* while *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval.  Qed.

(** **** Exercise: 3 stars, standard, especially useful (ceval__ceval_step)

    Finish the following proof.  You'll need [ceval_step_more] in a
    few places, as well as some basic facts about [<=] and [plus]. *)

Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  - (* E_Skip *)
    exists 1. simpl. reflexivity.
  - exists 1. simpl. rewrite -> H. reflexivity.
  - (* E_Seq *)
    destruct IHHce1 as [i1 Hi1].
    destruct IHHce2 as [i2 Hi2].
    exists (1 + i1 + i2).
    apply ceval_step_more with (i2 := i1 + i2) in Hi1; try lia.
    apply ceval_step_more with (i2 := i1 + i2) in Hi2; try lia.
    simpl. rewrite -> Hi1. apply Hi2.
  - destruct IHHce as [i Hi].
    exists (1 + i).
    simpl. rewrite -> H. apply Hi.
  - destruct IHHce as [i Hi].
    exists (1 + i). simpl. rewrite -> H. apply Hi.
  - exists 1. simpl. rewrite -> H. reflexivity.
  - destruct IHHce1 as [i1 Hi1].
    destruct IHHce2 as [i2 Hi2].
    exists (1 + i1 + i2).
    simpl. rewrite -> H.
    apply ceval_step_more with (i2 := i1 + i2) in Hi1; try lia.
    rewrite -> Hi1. 
    apply ceval_step_more with (i2 := i1 + i2) in Hi2; try lia.
    apply Hi2.
Qed. 

(** [] *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ################################################################# *)
(** * Determinism of Evaluation Again *)

(** Using the fact that the relational and step-indexed definition of
    evaluation are the same, we can give a slicker proof that the
    evaluation _relation_ is deterministic. *)

Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  lia. lia.  Qed.

(* 2024-08-25 11:11 *)
