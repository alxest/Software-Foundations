(** * ImpCEvalFun: Evaluation Function for Imp *)

(* $Date: 2013-07-01 18:48:47 -0400 (Mon, 01 Jul 2013) $ *)

(* #################################### *)
(** ** Evaluation Function *)

Require Import Imp.

(** Here's a first try at an evaluation function for commands,
    omitting [WHILE]. *)

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with 
    | SKIP => 
        st
    | l ::= a1 => 
        update st l (aeval st a1)
    | c1 ;; c2 => 
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI => 
        if (beval st b) 
          then ceval_step1 st c1 
          else ceval_step1 st c2
    | WHILE b1 DO c1 END => 
        st  (* bogus *)
  end.

(** In a traditional functional programming language like ML or
    Haskell we could write the WHILE case as follows:
<<
    | WHILE b1 DO c1 END => 
        if (beval st b1) 
          then ceval_step1 st (c1;; WHILE b1 DO c1 END)
          else st 
>>
    Coq doesn't accept such a definition ([Error: Cannot guess
    decreasing argument of fix]) because the function we want to
    define is not guaranteed to terminate. Indeed, the changed
    [ceval_step1] function applied to the [loop] program from [Imp.v] would
    never terminate. Since Coq is not just a functional programming
    language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is an
    invalid(!) Coq program showing what would go wrong if Coq allowed
    non-terminating recursive functions:
<<
     Fixpoint loop_false (n : nat) : False := loop_false n.
>>
    That is, propositions like [False] would become
    provable (e.g. [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_step1] cannot be written in Coq -- at least not
    without one additional trick... *)


(** Second try, using an extra numeric argument as a "step index" to
    ensure that evaluation always terminates. *)

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with 
  | O => empty_state
  | S i' =>
    match c with 
      | SKIP => 
          st
      | l ::= a1 => 
          update st l (aeval st a1)
      | c1 ;; c2 => 
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i' 
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) 
            then ceval_step2 st c1 i' 
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END => 
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
    an exercise below. *)

(** Third try, returning an [option state] instead of just a [state]
    so that we can distinguish between normal and abnormal
    termination. *)

Module ifTest.
Inductive ab : Set :=
  a : ab
| b : ab.
Check if (a) then 0 else 1.
Eval compute in if (a) then 0 else 1.
Eval compute in if (b) then 0 else 1.
(* Check if (b) then 0 else a. *)
(* QQQQQQQQQQQQQQQQQQQQ type check error, why? *)
Inductive abc : Set :=
  a_ : abc
| b_ : abc
| c_ : abc.
(* Eval compute in if (a_) then 0 else 1. *)
(* Toplevel input, characters 16-37: *)
(* > Eval compute in if (a_) then 0 else 1. *)
(* >                 ^^^^^^^^^^^^^^^^^^^^^ *)
(* Error: If is only for inductive types with two constructors. *)
End ifTest.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) 
                    : option state :=
  match i with 
  | O => None
  | S i' =>
    match c with 
      | SKIP => 
          Some st
      | l ::= a1 => 
          Some (update st l (aeval st a1))
      | c1 ;; c2 => 
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) 
            then ceval_step3 st c1 i' 
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1)           
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

(** We can improve the readability of this definition by introducing a
    bit of auxiliary notation to hide the "plumbing" involved in
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
      | SKIP => 
          Some st
      | l ::= a1 => 
          Some (update st l (aeval st a1))
      | c1 ;; c2 => 
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) 
            then ceval_step st c1 i' 
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END => 
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

Eval compute in 
     (test_ceval empty_state 
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3 
            ELSE Z ::= ANum 4
          FI)).

(* Eval compute in 
     (test_ceval empty_state 
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3 
            ELSE Z ::= ANum 4
          FI)).
   ====>
      Some (2, 0, 4)   *)

(** **** Exercise: 2 stars (pup_to_n) *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Make sure
   your solution satisfies the test that follows. *)

Definition pup_to_n : com :=
  (* Z ::= ANum 1;; *)
  (* WHILE BLe (AId Z) (AId X) *)
  (* DO *)
  (* Y ::= APlus (AId Z) (AId Y);; *)
  (* Z ::= APlus (AId Z) (ANum 1) *)
  (* END ;; *)
  (* X ::= ANum 0;; *)
  (* Z ::= ANum 0 *)
  WHILE BNot (BEq (AId X) (ANum 0))
        DO
        Y ::= APlus (AId X) (AId Y);;
        X ::= AMinus (AId X) (ANum 1)
        END
.

Eval compute in test_ceval (update empty_state X 5) pup_to_n.

Example pup_to_n_1 : 
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (peven) *)
(** Write a [While] program that sets [Z] to [0] if [X] is even and
    sets [Z] to [1] otherwise.  Use [ceval_test] to test your
    program. *)

Definition peven_fail : com :=
  WHILE (BLe (ANum 0) (AId X)) DO
        X ::= AMinus (AId X) (ANum 2)
  END ;;
  IFB (BEq (ANum 0) (AId X))
  THEN Z ::= (ANum 0)
  ELSE Z ::= (ANum 1)
  FI
.
(* X cannot go lower than 0 !!! inf loop -> None ! *)

Definition peven : com :=
  WHILE (BAnd (BNot (BEq (ANum 0) (AId X))) (BNot (BEq (ANum 1) (AId X)))) DO
        X ::= AMinus (AId X) (ANum 2)
  END ;;
  IFB (BEq (ANum 0) (AId X))
  THEN Z ::= (ANum 0)
  ELSE Z ::= (ANum 1)
  FI
.

(** [] *)
Check ex_intro.
Print ex.

(* Theorem tmpp : 1 + 1 = 2. *)
(* Definition tmp := test_ceval (update empty_state X 77) peven. *)
(* Definition tmp_ := test_ceval (update empty_state X 77) peven = Some (0, 0, 1). *)
(* Definition tmp__ : test_ceval (update empty_state X 77) peven = Some (0, 0, 1). *)

(* QQQQQQQQQQQQQQQQQQQQ *)
(* Compute just few steps? *)
(* normalize, normalize1 tactic in SF final exam 08? *)
(* cannot find tactic and cannot use it here *)
(* also, in 08 file, normalize tactic can be used inside theorem proof but not in the form of "eval compute in blah *)
Eval compute in test_ceval (update empty_state X 77) peven.

Lemma peven_test1 :
  exists x, test_ceval (update empty_state X 77) peven = Some (x, 0, 1).
Proof. exists 1. reflexivity. Qed.

(* ################################################################ *)
(** ** Equivalence of Relational and Step-Indexed Evaluation *)

(** As with arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation actually boil down
    to the same thing.  This section shows that this is the case.
    Make sure you understand the statements of the theorems and can
    follow the structure of the proofs. *)

Lemma some_implies_non_zero : forall i c st st2, ceval_step st c i = Some st2 -> i <> O.
Proof.
  intros. destruct i. inversion H. auto.
Qed.


Lemma lem : forall i c st st2, ceval_step st c i = Some st2 -> ceval_step st c (S i) = Some st2.
  intros i c.
  generalize dependent i.
  induction c; intros; auto; assert(G := H); apply some_implies_non_zero in G.
  - destruct i.
  destruct G; auto.
  simpl in H; auto.
  - destruct i0.
  destruct G; auto.
  simpl in H; auto.
  - destruct i.
  destruct G; auto.
  simpl in H; auto. destruct (ceval_step st c1 i) eqn:T.
  apply IHc1 in T.
  apply IHc2 in H.
  rewrite <- H.
  remember (S i) as j.
  simpl. rewrite T. auto.
  inversion H.
  - destruct i.
  destruct G; auto.
  simpl in H; auto.
  remember (S i) as j.
  simpl.
  destruct (beval st b) eqn:T.
  apply IHc1 in H. rewrite <- H. auto.
  apply IHc2 in H. rewrite <- H. auto.
  -
    generalize dependent st2.
    generalize dependent st.
    generalize dependent c.
    generalize dependent b.
    
  induction i.
  destruct G; auto. clear G.
  (* destruct i. *)
  (* destruct G; auto. clear G. *)
  (* ---------------------------------------------------- *)

  intros.

  (*   Heqx : ceval_step st c i = Some s *)
  (* H : ceval_step s (WHILE b DO c END) i = Some st2 *)
  (* H0 : beval st b = true *)
  (* TT : ceval_step st c (S i) = Some s *)
  (* ============================ *)
  (*  ceval_step s (WHILE b DO c END) (S i) = ceval_step s (WHILE b DO c END) i *)


  (* ---------------------------------------------------------- *)

  remember (S i) as j.
  destruct (beval st b) eqn:H0.
  (* assert(beval st b = true) by admit. *)
  
  simpl. rewrite H0.
  rewrite Heqj in H. simpl in H. rewrite H0 in H.
  remember (ceval_step st c i) as x.
  destruct x.
  symmetry in Heqx.
  assert(TT:=Heqx).
  apply IHc in TT.
  rewrite <- Heqj in TT.
  rewrite TT.
  (* rewrite <- H. *)
  subst.

  apply IHi.
  apply some_implies_non_zero in Heqx. auto.
  intros; auto. apply H.
  inversion H.
    (* ----------------------------------------------------- *)
  simpl. rewrite H0. subst. simpl in H. rewrite H0 in H. auto.
Qed.
  (*   inversion H. *)


  (* remember (S i) as j. simpl. destruct (beval st b) eqn:T. *)
  (* remember (ceval_step st c i) as x. *)
  (* symmetry in Heqx. *)
  (* assert(K := Heqx). *)
  (* destruct x. *)
  (* apply IHc in K. *)
  (* rewrite <- Heqj in K. *)
  (* rewrite K. rewrite <- H. *)
  (* assert(L := K). *)
  (* apply IHc in L. *)
  (* rewrite <- K in L. *)
  (* subst. simpl. *)
  (* rewrite T. *)
  (* rewrite Heqx. *)
  (* destruct (beval s b) eqn:TT. *)
  
  (* simpl in H; auto. *)
  (* rewrite <- H. *)
  
  (* destruct (beval st b) eqn:T. *)
  (* * destruct i. simpl in H. inversion H. *)
  (*   remember (ceval_step st c (S i)) as M. *)
  (*   destruct M. *)
  (*   simpl in H. destruct (beval s b); auto. *)
  (*   symmetry in HeqM. apply IHc in HeqM. apply IHc in HeqM. *)
    
  (* * simpl; rewrite T; subst; auto. *)
  (* * destruct (ceval_step st c i) eqn:T2. *)
  (* simpl. rewrite T. *)





(* Lemma lem_ : forall i c st st2, ceval_step st c i = Some st2 -> ceval_step st c (S i) = Some st2. *)
(*   induction i. *)
(*   intros. inversion H. *)
(*   intros. *)
(*   remember (ceval_step st c i) as v. *)
(*   destruct v. *)
(*   * *)
(*   symmetry in Heqv. *)
(*   assert(Heqv2 := Heqv). *)
(*   apply IHi in Heqv. *)
(*   rewrite H in Heqv. *)
(*   inversion Heqv. subst. clear Heqv. *)
(*   assert(H2 := H). *)
(*   rename H into js. *)
(*   rename Heqv2 into is. *)
(*   simpl in js. *)
(*   remember (S i) as j. *)
(*   simpl. *)
(*   rewrite <- js. *)
(*   rewrite <- is in H2. *)
(*   destruct c; try rewrite <- H2; auto. *)
(*   - admit. *)
(*     (* destruct (ceval_step st c1 i) eqn:iT. destruct (ceval_step st c1 j) eqn:jT. *) *)
(*     (* subst. *) *)
(*     (* rewrite js. *) *)
(*     (* rewrite <- is. *) *)
(*   - assert(G: i <> 0). apply some_implies_non_zero in is. auto. *)
(*     destruct i. destruct G; auto. *)
(*     clear G. *)
(*     destruct (beval st b) eqn:T; auto. *)
(*     simpl in is. rewrite T in is. *)
(*     simpl in H2. rewrite T in H2. *)
    
(*   reflexivity. *)
(*   rewrite H2. *)





(* Lemma lem2 : forall i c st st2, ceval_step st c i = Some st2 -> ceval_step st c (S i) = Some st2 -> ceval_step st c (S (S i)) = Some st2. *)
(* Lemma lem3 : forall i c st, ceval_step st c i = ceval_step st c (S i) -> ceval_step st c (S i) = ceval_step st c (S (S i)). *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st || st'.
Proof.
  intros.
  destruct H.
  generalize dependent st'.
  generalize dependent st. (* third case ! st -> st', st -> st' *)
  induction c; intros; simpl; auto.
  -
  destruct x; simpl in H; inversion H.
  constructor.
  -
  destruct x; simpl in H; inversion H.
  constructor; auto.
  -
  destruct x; simpl in H; inversion H.
  remember (ceval_step st c1 x) as t.
  destruct t.
  (* QQQQQQQQQQQQQQQQQQQQQQ inversion here does not work! *)
  apply E_Seq with (st':=s).
  apply IHc1. apply lem. auto.
  apply IHc2. apply lem. auto.
  inversion H.
  -
  destruct x; simpl in H; inversion H.
  destruct (beval st b) eqn:T.
  apply E_IfTrue; auto. apply IHc1. apply lem. auto.
  apply E_IfFalse; auto. apply IHc2. apply lem. auto.
  -
  (* destruct x; simpl in H; inversion H. *)
  (* destruct (beval st b) eqn:T. *)
  (* Abort All.  *)

    (* generalize dependent st. *)
    (* generalize dependent st'. *)
    (* generalize dependent x. *)
    (* induction (WHILE b DO c END). admit. admit. admit. admit. *)
    (* intros. *)
    (* destruct (beval st b0) eqn:T. *)
    (* eapply E_WhileLoop; auto. *)
    (* Abort All. *)

    generalize dependent st.
    generalize dependent st'.
    generalize dependent b.
    generalize dependent c.
    
    induction x; intros. + simpl in H; inversion H.
    + apply IHx.
      * intros. simpl in H.
      apply lem in H0.
      apply IHc in H0. auto.
      * rewrite <- H. simpl.
        destruct (beval st b) eqn:Tb.
          simpl in H. rewrite Tb in H.
          remember (ceval_step st c x) as m.
          destruct m. symmetry in Heqm. 
        destruct (ceval_step st c x) eqn:Tc.
      

      
      destruct x.
      * inversion H.
        destruct (beval st b) eqn:T. inversion H1. inversion H1; subst. apply E_WhileEnd; auto.
      * apply IHx. intros.
      
    simpl in H. rewrite T in *; subst. apply 
    apply IHx.
    intros.
  (* apply E_WhileLoop with (st':=st'); auto. apply IHc. apply lem. *)
    
  (* constructor; auto. *)
   
  (* unfold ceval_step in H. *)
  (* simpl in H. *)
  (* compute in H. *)







  







(* QQQQQQQQQQQQQQQQQQQQQQQQ Why Seq i-1, i-1? not i-1, i-2 ? *)

    
Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st || st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  Case "i = 0 -- contradictory".
    intros c st st' H. inversion H.

  Case "i = S i'".
    intros c st st' H.
    com_cases (destruct c) SCase; 
           simpl in H; inversion H; subst; clear H. 
      SCase "SKIP". apply E_Skip.
      SCase "::=". apply E_Ass. reflexivity.

      SCase ";;".
        destruct (ceval_step st c1 i') eqn:Heqr1. 
        SSCase "Evaluation of r1 terminates normally".
          apply E_Seq with s. 
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        SSCase "Otherwise -- contradiction".
          inversion H1.

      SCase "IFB". 
        destruct (beval st b) eqn:Heqr.
        SSCase "r = true".
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        SSCase "r = false".
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      SCase "WHILE". destruct (beval st b) eqn :Heqr.
        SSCase "r = true". 
         destruct (ceval_step st c i') eqn:Heqr1.
          SSSCase "r1 = Some s".
            apply E_WhileLoop with s. rewrite Heqr. reflexivity.
            apply IHi'. rewrite Heqr1. reflexivity. 
            apply IHi'. simpl in H1. assumption.
          SSSCase "r1 = None".
            inversion H1.
        SSCase "r = false".
          inversion H1. 
          apply E_WhileEnd. 
          rewrite <- Heqr. subst. reflexivity.  Qed.

(** **** Exercise: 4 stars (ceval_step__ceval_inf) *)
(** Write an informal proof of [ceval_step__ceval], following the
    usual template.  (The template for case analysis on an inductively
    defined value should look the same as for induction, except that
    there is no induction hypothesis.)  Make your proof communicate
    the main ideas to a human reader; do not simply transcribe the
    steps of the formal proof.

(* FILL IN HERE *)
[]
*)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 -> 
  ceval_step st c i1 = Some st' -> 
  ceval_step st c i2 = Some st'.
Proof. 
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  Case "i1 = 0".
    simpl in Hceval. inversion Hceval.
  Case "i1 = S i1'".
    destruct i2 as [|i2']. inversion Hle. 
    assert (Hle': i1' <= i2') by omega.
    com_cases (destruct c) SCase.
    SCase "SKIP".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase "::=".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase ";;".
      simpl in Hceval. simpl. 
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      SSCase "st1'o = Some".
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "st1'o = None".
        inversion Hceval.

    SCase "IFB".
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval; assumption.
    
    SCase "WHILE".
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption. 
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      SSCase "st1'o = Some".
        apply (IHi1' i2') in Heqst1'o; try assumption. 
        rewrite -> Heqst1'o. simpl. simpl in Hceval. 
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "i1'o = None".
        simpl in Hceval. inversion Hceval.  Qed.

(** **** Exercise: 3 stars (ceval__ceval_step) *)
(** Finish the following proof.  You'll need [ceval_step_more] in a
    few places, as well as some basic facts about [<=] and [plus]. *)

Theorem ceval__ceval_step: forall c st st',
      c / st || st' ->
      exists i, ceval_step st c i = Some st'.
Proof. 
  intros c st st' Hce.
  ceval_cases (induction Hce) Case.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      c / st || st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ####################################################### *)
(** ** Determinism of Evaluation (Simpler Proof) *)

(** Here's a slicker proof showing that the evaluation relation is
    deterministic, using the fact that the relational and step-indexed
    definition of evaluation are the same. *)

Theorem ceval_deterministic' : forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
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
  omega. omega.  Qed.
