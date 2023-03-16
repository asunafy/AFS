Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Array.PArray.



Require Import Uint63.

Import ListNotations.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update.  rewrite <- eqb_string_refl.
  reflexivity.
Qed.

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVars (x : string) (* Var *)
  | ACH (x : string) (* Cache *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).


Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition F : string := "0x21d36e0".
Definition M1 : string := "M1".
Definition M2 : string := "M2".
Definition M : string := "M".

Definition I : string := "instance".
Definition H : string := "host".

Coercion AVars : string >-> aexp. 
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Notation "x + y" := (APlus x y) (at level 50, left associativity).
Notation "x - y" := (AMinus x y) (at level 50, left associativity).
Notation "x * y" := (AMult x y) (at level 40, left associativity).
Notation "x / y" := (ADiv x y) (at level 40, left associativity).
Notation "x <= y" := (BLe x y) (at level 70, no associativity).
Notation "x = y" := (BEq x y) (at level 70, no associativity).
Notation "x && y" := (BAnd x y) (at level 40, left associativity).
Notation "'~' b" := (BNot b) (at level 75, right associativity).

Fixpoint acal (st_v : state) (st_c : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AVars x => if (prefix "0x" x) then st_c x else st_v x
  | ACH x => if (prefix "0x" x) then st_c x else st_v x
  | APlus a1 a2 => (acal st_v st_c a1) + (acal st_v st_c a2)
  | AMinus a1 a2  => (acal st_v st_c a1) - (acal st_v st_c a2)
  | AMult a1 a2 => (acal st_v st_c a1) * (acal st_v st_c a2)
  | ADiv a1 a2 => (acal st_v st_c a1) / (acal st_v st_c a2)
  end.

Fixpoint bcal (st_v : state) (st_c : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (acal st_v st_c a1) =? (acal st_v st_c a2)
  | BLe a1 a2   => (acal st_v st_c a1) <=? (acal st_v st_c a2)
  | BNot b1     => negb (bcal st_v st_c b1)
  | BAnd b1 b2  => andb (bcal st_v st_c b1) (bcal st_v st_c b2)
  end.

Definition empty_st := (_ !-> 0).

Definition clear_cache (st: state) : state :=
  match st with
  | _ => empty_st
 end.

Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Inductive channel : Set := 
| CH : nat -> channel.

Inductive act : Type :=
  | CSkip
  | CStop
  | CSleep (t : int)
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : act)
  | CIf (b : bexp) (c1 c2 : act)
  | CWhile (b : bexp) (c : act)
  | CSend (ch : channel) (ad : string) (a : aexp)
  | CRecv (ch : channel) (ad x : string) 
  | CMovep (i : int)
  | CMovei (h : int)
  | CPar (c1 c2 : act).


Notation "'SKIP'" :=
   CSkip.
Notation "'STOP'" :=
   CStop.
Notation "'SLEEP' t" :=
  (CSleep t) (at level 60).
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 65, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'END'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "ch '#' ad '!' a" :=
  (CSend ch ad a) (at level 80, right associativity).
Notation "ch '#' ad '?' x" :=
  (CRecv ch ad x) (at level 80, right associativity).
Notation "'MOVEp' ( i )" :=
  (CMovep i) (at level 80, right associativity).
Notation "'MOVEi' ( h ) " :=
  (CMovei h) (at level 80, right associativity).
Notation "c1 '//' c2" :=
  (CPar c1 c2) (at level 70, right associativity).

Inductive config : Type :=
  | Config (st_v st_c: state) (ins hos :int).

Definition get_st_v (cf : config) : state :=
  match cf with
  | Config st_v st_c ins hos => st_v
  end.

Definition get_st_c (cf : config) : state :=
  match cf with
  | Config st_v st_c ins hos => st_c
  end.

Definition get_ins (cf : config) : int :=
  match cf with
  | Config st_v st_c ins hos => ins
  end.

Definition get_hos (cf : config) : int :=
  match cf with
  | Config st_v st_c ins hos => hos
  end.

Definition Empty_cf : config := Config empty_st empty_st 1 1.
Definition Error_cf : config := Config empty_st empty_st 0 0.


Definition IsErrorCf (cf : config): bool :=
  match cf with
  | Config st_v st_c ins hos => eqb ins 0
  end. 

Fixpoint actcal (cf : config) (c : act) (h i : int) (s : nat): config :=
  match s with
   | O => cf
   | S s1 =>
     if IsErrorCf cf then Error_cf
     else match c with
      | x ::= a => match prefix "0x" x with 
         | true => Config (get_st_v cf) (x !-> acal (get_st_v cf) (get_st_c cf) a ; get_st_c cf) h i
         | false => Config (x !-> acal (get_st_v cf) (get_st_c cf) a ; get_st_v cf) (get_st_c cf) h i
                           end
      | c1;; c2 => let cf1 := actcal cf c1 h i s1 in actcal cf1 c2 h i s1
      | SKIP => cf
      | STOP => Config (get_st_v cf) empty_st h i
      | MOVEp(i1) => Config (get_st_v cf) (get_st_c cf) h i1
      | MOVEi(h1) => Config (get_st_v cf) (get_st_c cf) h1 i
      | SLEEP t => cf
      | IFB b THEN c1 ELSE c2 END => match bcal (get_st_v cf) (get_st_c cf) b with 
                                      | true => actcal cf c1 h i s1
                                      | false => actcal cf c2 h i s1
                                     end
      | ch#ad! a => Config (get_st_v cf) (ad !-> acal (get_st_v cf) (get_st_c cf) a ; get_st_c cf) h i
      | ch#ad? x => match acal (get_st_v cf) (get_st_c cf) (ACH ad) with
                       | 0 => Error_cf 
                       | _ => Config (x !-> acal (get_st_v cf) (get_st_c cf) (ACH ad) ; get_st_v cf) (get_st_c cf) h i
                      end
      | WHILE b DO c1 END => match bcal (get_st_v cf) (get_st_c cf) b with 
                        | true => let cf1 := actcal cf c1 h i s1 in 
                                  actcal cf1 c h i s1
                        | false => cf
                        end
      | c1//c2 => let cf1 := actcal cf c1 h i s1 in actcal cf1 c2 h i s1
 end
end.

Definition MaxStep : nat := 20.

Notation " '[' cf ']' 'H' ( h ) ':' 'I' ( i ) ':' ( c ) " :=
  (actcal cf c h i MaxStep) (at level 90, right associativity).

Notation eqb := eqb (only parsing).

Definition eq_bool (h1 h2: int) : bool :=
  if (eqb h1 h2) then true else false.

Definition eq_host_cf (h1 h2 i2: int) (cf : config) : config :=
  match IsErrorCf cf with
  | true => Error_cf 
  | false => if (eq_bool h1 h2) then (Config empty_st (get_st_c cf) h2 i2) else (Config empty_st empty_st h2 i2)
  end.

Notation " '[' cf ']' 'H' ( h1 ) ':' 'I' ( i1 ) ':' ( c1 ) '//' 'H' ( h2 ) ':' 'I' ( i2 ) ':' ( c2 )" :=
  (actcal (eq_host_cf h1 h2 i2 (actcal cf c1 h1 i1 MaxStep)) c2 h2 i2 MaxStep)  (at level 90, right associativity).

Fixpoint repeat_assign (st : state)(x : string) (v n: nat): state :=
  match n with
   | O => st
   | S n' => let st1 := (x !-> v ; st) in
                repeat_assign st1 x v n'           
  end.

Fixpoint check_process_no_rec (cf : config) (c : act) : bool :=
    match c with
  | a#c_ad? x => match acal (get_st_v cf) (get_st_c cf) (ACH c_ad) with
                | 0 => false
                | _ => true
                end
  | c1;; c2 => check_process_no_rec cf c1 && check_process_no_rec cf c2
  | IFB b THEN c1 ELSE c2 END => check_process_no_rec cf c1 && check_process_no_rec cf c2
  | WHILE b DO c END => check_process_no_rec cf c
  | c1//c2 => check_process_no_rec cf c1 && check_process_no_rec cf c2
  | _ => true
end.


Axiom Cpar_eq1 : forall (c1 c2 : act),
(c1 // c2) = (c2 // c1).

Axiom Cpar_eq2 : forall (c1 c2 c3: act),
(c1 // c2 // c3) = (c2 // c1 // c3).


(* Only the right side has a receiving action in parallel processes_1 *)
Axiom Cpar_right_yes_1 : forall (p q q1 : act) (cf cf1: config) (i h :int)  (a : channel) (c_ad x : string),
  check_process_no_rec cf p = true ->
  check_process_no_rec cf q = true ->
  [cf]H (i): I (h): ( p // q ) = cf1 -> 
  [cf]H (i): I (h): ( p // q;; (a#c_ad? x);; q1 ) =
  ([cf1] H (i): I (h): ( (a#c_ad? x) ;; q1 )).

(* Only the right side has a receiving action in parallel processes_2 *)
Axiom Cpar_right_yes_2 : forall (p q' : act) (cf cf': config) (i h :int) (a : channel) (c_ad x : string),
  check_process_no_rec cf p = true ->
  [cf]H (i): I (h): ( p ) = cf' ->
  [cf]H (i): I (h): ( p//(a#c_ad? x) ;; q' ) = 
  ([cf']H (i): I (h): ( (a#c_ad? x) ;; q' )). 

(* Both sides have receiving actions in parallel processes_1 *)
Axiom Cpar_both_yes_1 : forall (p p' q q' : act) (cf cf': config) (i h :int) (a1 a2 : channel) (c_ad1 x1 c_ad2 x2: string),
  check_process_no_rec cf p = true ->
  check_process_no_rec cf q = true ->
  [cf]H (i): I (h): ( p // q ) = cf' -> 
  [cf]H (i): I (h): ( p;; (a1#c_ad1? x1);; p'//q;; (a2#c_ad2? x2);; q' ) =
  ([cf'] H (i): I (h): ( (a1#c_ad1? x1);; p'//(a2#c_ad2? x2);; q' )).

(* Both sides have receiving actions in parallel processes_2 *)
Axiom Cpar_both_yes_2 : forall (p p' q' : act) (cf cf': config) (i h :int) (a1 a2 : channel) (c_ad1 x1 c_ad2 x2: string),
  check_process_no_rec cf p = true ->
  [cf]H (i): I (h): ( p ) = cf' ->
  [cf]H (i): I (h): ( p;; (a1#c_ad1? x1);; p'//(a2#c_ad2? x2);; q' ) =
  ([cf'] H (i): I (h): ( (a1#c_ad1? x1);; p'//(a2#c_ad2? x2);; q' )).

(* Perform parallel processes step by step *)
Axiom Cpar_step : forall (p q: act) (cf cf': config) (i h :int) ,
  check_process_no_rec cf p = true ->
  [cf]H (i): I (h): ( p ) = cf' ->
  [cf]H (i): I (h): ( p // q ) =
  ([cf'] H (i): I (h): ( q )).

(* Perform parallel processes of different instances under the same host *)
Axiom Cpar_Dif_Ins : forall (p: act) (cf cf': config) (h i1 i2 :int) ,
   cf'= Config empty_st (get_st_c cf) h i2 ->
  [cf]H (h): I (i1): ( SKIP ) // H (h): I (i2): ( p ) =
  ([cf'] H (h): I (i2): ( p )).





(* Test Examples *)

Example test_example_1:
 ([Empty_cf] H (1): I (5): ( X ::= 0;; "0x21d36e0" ::= 1;; Z ::= 2)) = 
  Config (Z !-> 2 ; X !-> 0) ("0x21d36e0" !-> 1) 1 5.
Proof. 
  reflexivity. Qed.

Example test_example_2:
 ([Empty_cf] H (1): I (5): (X ::= 4/2 ;; SKIP // Z ::= 2)) = 
  Config (Z !-> 2 ; X !-> 2) empty_st 1 5.
Proof. 
  reflexivity. Qed.

Example test_example_3:
 ([Empty_cf] H (1): I (5): ( SLEEP 1 ;; X ::= 0;; "0x21d36e0" ::= 1)) = 
  Config (X !-> 0) ("0x21d36e0" !-> 1) 1 5.
Proof.
  reflexivity. Qed.

Example test_example_4:
 ([Empty_cf] H (1): I (5): ( Z ::= 3;;
    IFB Z = 1 THEN X ::= 0;; "0x21d36e0" ::= 1 ELSE Z ::= 2 END)) = 
  Config (Z !-> 2; Z !-> 3) empty_st 1 5.
Proof. 
  reflexivity. Qed.

Example test_example_5:
 ([Empty_cf] H (1): I (5): ( X ::= 1;; Z ::= 2;; (CH 0#"0x21d36e0" ! Z + X))) = 
  Config (Z !-> 2 ; X !-> 1) ("0x21d36e0" !-> 3) 1 5.
Proof. 
  reflexivity. Qed.

Example test_example_6:
 ([Empty_cf]H (1): I (5): ( "0x21d36e0" ::= 3;; (CH 0#"0x21d36e0" ? Y))) = 
  Config (Y !-> 3) ("0x21d36e0" !-> 3) 1 5.
Proof. 
  reflexivity. Qed.

Definition while_test : act :=
  (Z ::= 2;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END).

Example test_example_7:
 ([Empty_cf]H (1): I (5): (while_test)) = 
  Config (Z !-> 0 ; Y !-> 2 ; Z !-> 1 ; Y !-> 2 ; Y !-> 1 ; Z !-> 2) empty_st 1 5.
Proof. 
  reflexivity. Qed.


Definition R' : act :=
  (WHILE true DO
    X ::= 1
  END).

Example test_example_8:
  
 ([Empty_cf]H (1): I (5): (R')) = 
  Config (repeat_assign empty_st X 1 (MaxStep-1)) empty_st 1 5.
Proof.

  reflexivity. Qed.


(* Paper Examples *)

Definition P : act :=
  (X ::= 1;;
  (CH 0#"0x21d36e0" ! X)).

Definition P1 : act :=
  (CH 1#"0x21d3fff" ? M2).

Definition P2 : act :=
  ( M ::= X + M2;;
  SKIP).

Definition Q : act :=
  (CH 0#"0x21d36e0" ? Y).

Definition Q1 : act :=
  M1 ::= Y;;
  (CH 1#"0x21d3fff" ! M1);;
  SKIP.

Definition R : act :=
  (WHILE true DO
    Z ::= "0x21d36e0"%string
  END).


Definition cf_e1 : config := Config empty_st empty_st 1 5.

Example test_example1_err:
 ([cf_e1]H (1): I (5): (P;;P1;;P2 // Q;;Q1)// 
              H (1): I (6): (R)) = 
  Error_cf.
Proof.
  reflexivity. Qed.

Example test_example1:
 ([cf_e1]H (1): I (5): (P//Q)) = 
  Config (Y !-> 1; X !-> 1) ("0x21d36e0" !-> 1) 1 5.
Proof.
  reflexivity. Qed.

Example paper_new_example_1_err:
  [cf_e1]H (1): I (5): (P;;P1;;P2//Q;;Q1) =
  Error_cf.
Proof.
  reflexivity. Qed.

Definition mid_cf_1 := Config (X !-> 1) ("0x21d36e0" !-> 1) 1 5.
Definition mid_cf_2 := Config (M1 !-> 1; Y !-> 1; X !-> 1) ("0x21d3fff" !-> 1; "0x21d36e0" !-> 1) 1 5.
Definition mid_cf_3 := Config (M !-> 2;  M2 !-> 1; M1 !-> 1; Y !-> 1; X !-> 1) ("0x21d3fff" !-> 1; "0x21d36e0" !-> 1) 1 5.
Definition mid_cf_4 := Config empty_st ("0x21d3fff" !-> 1; "0x21d36e0" !-> 1) 1 6.
Example paper_new_example_1:
  [cf_e1]H (1): I (5): (P;;P1;;P2//Q;;Q1) =
  Config (M !-> 2;  M2 !-> 1; M1 !-> 1; Y !-> 1; X !-> 1) ("0x21d3fff" !-> 1; "0x21d36e0" !-> 1) 1 5.
Proof.
  assert (HM1 : [cf_e1]H (1): I (5): (P;;P1;;P2//Q;;Q1) = 
  ([mid_cf_1]H (1): I (5): (P1;;P2//Q;;Q1))).
  { apply Cpar_both_yes_2; reflexivity. }
  rewrite HM1.
  assert (HM2: (P1;;P2//Q;;Q1) = (Q;;Q1//P1;;P2)).
  { apply Cpar_eq1. }
  rewrite HM2.
  assert (HM3: [mid_cf_1]H (1): I (5): (Q;;Q1//P1;;P2) = 
  ([mid_cf_2]H (1): I (5): (P1;;P2))).
  { apply Cpar_right_yes_2; reflexivity. }
  rewrite HM3.
  reflexivity. Qed.

Example paper_new_example_1'_err:
  [cf_e1]H (1): I (5): (P;;P1;;P2//Q;;Q1//R) =
  Error_cf.
Proof.
  reflexivity. Qed.

Example paper_new_example_1':
  [cf_e1]H (1): I (5): (P;;P1;;P2//Q;;Q1//R) =
  Config (repeat_assign (M !-> 2; M2 !-> 1; M1 !-> 1; Y !-> 1; X !-> 1) Z 1 (MaxStep-1)) ("0x21d3fff" !-> 1; "0x21d36e0" !-> 1) 1 5.
Proof.
  assert (HM1 : [cf_e1]H (1): I (5): (P;;P1;;P2//Q;;Q1//R) = 
  ([mid_cf_1]H (1): I (5): (P1;;P2//Q;;Q1//R))).
  { apply (@Cpar_both_yes_2 P P2 (Q1//R) cf_e1 mid_cf_1 1 5 (CH 1) (CH 0) "0x21d3fff" M2 "0x21d36e0" Y); reflexivity. }
  rewrite HM1.
  assert (HM2: (P1;;P2//Q;;Q1//R) = (Q;;Q1//P1;;P2//R)).
  { apply (@Cpar_eq2 (P1;;P2) (Q;;Q1) R). }
  rewrite HM2.
   assert (HM3: [mid_cf_1]H (1): I (5): (Q;; Q1 // P1;; P2 // R) = 
  ([mid_cf_2]H (1): I (5): (P1;; P2 // R))).
  { apply (@Cpar_step (Q;; Q1) (P1;; P2 // R) mid_cf_1 mid_cf_2 1 5 );reflexivity.  }
  rewrite HM3.
   assert (HM4: [mid_cf_2]H (1): I (5): (P1;; P2 // R) = 
  ([mid_cf_3]H (1): I (5): (R))).
  { apply (@Cpar_step (P1;; P2) R mid_cf_2 mid_cf_3 1 5 );reflexivity.  }
  rewrite HM4.  
  reflexivity. Qed.


Example paper_new_example_1''_err:
  [cf_e1]H (1): I (5): (P;;P1;;P2//Q;;Q1) // 
              H (1): I (6): (R) =
  Error_cf.
Proof.
  reflexivity. Qed.

Example paper_new_example_1'':
  [cf_e1]H (1): I (5): (P;;P1;;P2//Q;;Q1) // 
              H (1): I (6): (R) =
  Config (repeat_assign empty_st Z 1 (MaxStep-1)) ("0x21d3fff" !-> 1; "0x21d36e0" !-> 1) 1 6.
Proof.
 assert (HM1 : [cf_e1]H (1): I (5): (P;;P1;;P2//Q;;Q1) = 
  ([mid_cf_1]H (1): I (5): (P1;;P2//Q;;Q1))).
  { apply Cpar_both_yes_2; reflexivity. }
  rewrite HM1.
  assert (HM2: (P1;;P2//Q;;Q1) = (Q;;Q1//P1;;P2)).
  { apply Cpar_eq1. }
  rewrite HM2.
  assert (HM3: [mid_cf_1]H (1): I (5): (Q;;Q1//P1;;P2) = 
  ([mid_cf_2]H (1): I (5): (P1;;P2))).
  { apply Cpar_right_yes_2; reflexivity. }
  rewrite HM3.
  assert (HM4: [mid_cf_2]H (1): I (5): (P1;; P2) = 
  ([mid_cf_3]H (1): I (5): (SKIP))).
  { reflexivity.  }
  rewrite HM4.
  assert (HM5: ([mid_cf_3]H (1): I (5): (SKIP)//H (1): I (6): (R)) = 
  ([mid_cf_4]H (1): I (6): (R))).
  { apply Cpar_Dif_Ins;reflexivity.  }
  rewrite HM5.
  reflexivity. Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end. 

Definition cf_e2_1 : config := Config empty_st ("0x21d36e0" !-> 4) 1 5.
Definition cf_e2_2 : config := Config empty_st ("0x21d36e0" !-> 3) 1 5.

Definition P_2 : act :=
   (CH 0#"0x21d36e0" ? X).

Definition P_2'_sub (cf : config) : act :=
   IFB (evenb ((get_st_v ([cf]H (get_hos cf): I (get_ins cf): (P_2))) X))  
   THEN Y ::= 1 
   ELSE Y ::= 0 END;; STOP.

Definition P_2'_1 : act :=
  P_2'_sub cf_e2_1.

Definition P_2'_2 : act :=
  P_2'_sub cf_e2_2.

Definition R_2 : act :=
   (CH 1#"0x33d36e1" ! Y);; STOP.

Example paper_new_example_2:
 ([cf_e2_1]H (1): I (5): (P_2;; P_2'_1// R_2))  = 
  (Config (Y !-> 1; X !-> 4) empty_st 1 5).
Proof.
  reflexivity. Qed.

Example paper_new_example_2':
 ([cf_e2_2]H (1): I (5): (P_2;; P_2'_2// R_2))  = 
  (Config (Y !-> 0; X !-> 3) empty_st 1 5).
Proof.
  reflexivity. Qed.
