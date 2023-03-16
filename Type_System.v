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

Definition Error : string := "Error".

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
  | CMovep (i i' : string)
  | CMovei (h i h' i' : string)
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
Notation "'MOVEp' ( i ) 'to' ( i' )" :=
  (CMovep i i') (at level 80, right associativity).
Notation "'MOVEi' ( h ) ( i ) 'to' ( h' ) ( i' )" :=
  (CMovei h i h' i') (at level 80, right associativity).
Notation "c1 '//' c2" :=
  (CPar c1 c2) (at level 70, right associativity).




Inductive ty : Type :=
  | Low : ty
  | High : ty
  | Medium : ty
  | None : ty.

Inductive ins_ty : Type :=
  | ins_none : ins_ty
  | ins_0 : ins_ty
  | ins_1 : ins_ty
  | ins_2 : ins_ty.

Inductive hos_ty : Type :=
  | hos_none : hos_ty
  | hos_0 : hos_ty
  | hos_1 : hos_ty
  | hos_2 : hos_ty.

Definition vc_level := total_map ty.
Definition i_level := total_map ins_ty.
Definition h_level := total_map hos_ty.
Definition c_ins := total_map string.

Definition t_update_ty (m : total_map ty)
                    (x : string) (v : ty) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition t_update_ins_ty (m : total_map ins_ty)
                    (x : string) (v : ins_ty) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition t_update_hos_ty (m : total_map hos_ty)
                    (x : string) (v : hos_ty) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition t_update_c_ins (m : total_map string)
                    (x : string) (v : string) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition empty_ty := (_ !-> None).
Definition empty_ins_ty := (_ !-> ins_none).
Definition empty_host_ty := (_ !-> hos_none).
Definition empty_c_i := (_ !-> "NoInstance"%string).
Notation "x '|->' v" := (t_update_ty empty_ty x v) (at level 100). 
Notation "x '|i|->' v" := (t_update_ins_ty empty_ins_ty x v) (at level 100). 
Notation "x '|h|->' v" := (t_update_hos_ty empty_host_ty x v) (at level 100). 
Notation "x '|=>' v" := (t_update_c_ins empty_c_i x v) (at level 100). 

Notation "x '|->' v ';' m" := (t_update_ty m x v)
                              (at level 100, v at next level, right associativity).
Notation "x '|i|->' v ';' m" := (t_update_ins_ty m x v)
                              (at level 100, v at next level, right associativity).
Notation "x '|h|->' v ';' m" := (t_update_hos_ty m x v)
                              (at level 100, v at next level, right associativity).
Notation "x '|=>' v ';' m" := (t_update_c_ins m x v)
                              (at level 100, v at next level, right associativity).

Inductive env : Type :=
  | Env (v_ty c_ty : vc_level)(v_l c_l : list string)(c_i : c_ins)
        (i_ty : i_level)(h_ty : h_level)(i_l h_l : list string)(st_v st_c: state).

Inductive jud : Type :=
  | Jud (tau : vc_level)(omegaI : i_level)(omegaH : h_level).

Definition get_st_v (ev : env) : state :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => st_v
  end.

Definition get_st_c (ev : env) : state :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => st_c
  end.

Definition get_v_ty (ev : env) : vc_level :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => v_ty
  end.

Definition get_c_ty (ev : env) : vc_level :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => c_ty
  end.

Definition get_c_i (ev : env) : c_ins :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => c_i
  end.

Definition get_v_l (ev : env) : list string :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => v_l
  end.

Definition get_i_l (ev : env) : list string :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => i_l
  end.

Definition get_h_l (ev : env) : list string :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => h_l
  end.

Definition get_c_l (ev : env) : list string :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => c_l
  end.

Definition get_i_ty (ev : env) : i_level :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => i_ty
  end.

Definition get_h_ty (ev : env) : h_level :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i i_ty h_ty i_l h_l st_v st_c => h_ty
  end.

Definition get_tau (ju : jud) : vc_level :=
  match ju with
  | Jud tau omegaI omegaH => tau
  end.

Definition get_omegaI (ju : jud) : i_level :=
  match ju with
  | Jud tau omegaI omegaH => omegaI
  end.

Definition get_omegaH (ju : jud) : h_level :=
  match ju with
  | Jud tau omegaI omegaH => omegaH
  end.

Definition get_high_level (a b : ty) : ty :=
   match a with
      | High => High
      | Medium => match b with
                | High => High
                | _ => Medium
                end
      | _ => match b with
                | High => High
                | Medium => Medium
                | _ => Low
                end
end.

Fixpoint atype (a : aexp) (v_ty c_ty : vc_level) : ty :=
  match a with
  | ANum n => Low
  | AVars x | ACH x => match v_ty x with
               | None => match c_ty x with
                         | None => Low
                         | _ => c_ty x
                         end
               | _ => v_ty x               
               end
  | APlus a1 a2 | AMinus a1 a2 | AMult a1 a2 | ADiv a1 a2 
    => get_high_level (atype a1 v_ty c_ty) (atype a2 v_ty c_ty)
  end.

Fixpoint btype (b : bexp) (v_ty c_ty : vc_level) : ty :=
  match b with
  | BTrue | BFalse     => Low
  | BEq a1 a2 | BLe a1 a2  
   => get_high_level (atype a1 v_ty c_ty) (atype a2 v_ty c_ty)
  | BNot b1     => btype b1 v_ty c_ty
  | BAnd b1 b2  => get_high_level (btype b1 v_ty c_ty) (btype b2 v_ty c_ty)
  end.

Definition update_type_sub (lv v_ty c_ty tau: vc_level) (c : act) : vc_level :=
   match c with
   | x ::= a => match lv x with
                | High => lv
                | Medium => match tau x with
                        | High => x |-> High; lv
                        | _ => match atype a v_ty c_ty with
                              | High => x |-> High; lv
                              | _ => lv
                              end
                         end
                | Low => match tau x with
                        | High => x |-> High; lv
                        | Medium => match atype a v_ty c_ty with
                              | High => x |-> High; lv
                              | _ => x |-> Medium; lv
                              end
                        | _ => match atype a v_ty c_ty with
                              | High => x |-> High; lv
                              | Medium => x |-> Medium; lv
                              | _ => lv
                              end
                         end
                | _ => match tau x with
                        | High => x |-> High; lv
                        | Medium => match atype a v_ty c_ty with
                              | High => x |-> High; lv
                              | _ => x |-> Medium; lv
                              end
                        | _ => match atype a v_ty c_ty with
                              | High => x |-> High; lv
                              | Medium => x |-> Medium; lv
                              | _ => x |-> Low; lv
                              end
                         end
               end
   | _ => lv
  end.

Definition update_type' (v_ty c_ty tau: vc_level) (c : act) : vc_level :=
  match c with
   | x ::= a =>  match prefix "0x" x with 
               | true => update_type_sub c_ty v_ty c_ty tau c 
               | false => update_type_sub v_ty v_ty c_ty tau c 
               end
   | a#c_ad! w => match tau c_ad with
                | High => match c_ty c_ad with
                        | High => c_ty
                        | _ => c_ad |-> High; c_ty                  
                         end
                | _ => match c_ty c_ad with
                        | High => c_ty
                        | Medium => match atype w v_ty c_ty with
                                 | High => c_ad |-> High; c_ty
                                 | _ => c_ty
                                 end
                        | _ =>  match atype w v_ty c_ty with
                                 | High => c_ad |-> High; c_ty
                                 | Medium => c_ad |-> Medium; c_ty
                                 | _ => match c_ty c_ad with
                                        | Low => match tau c_ad with
                                                 | Medium => c_ad |-> Medium; c_ty
                                                 | _ => c_ty
                                                 end
                                        | _ => match tau c_ad with
                                                 | Medium => c_ad |-> Medium; c_ty
                                                 | _ => c_ad |-> Low; c_ty
                                                 end
                                        end
                                 end
                        end             
               end
   | a#c_ad? x => match tau x with
                | High => match v_ty x with
                        | High => v_ty
                        | _ => x |-> High; v_ty
                        end
                | _ => match v_ty x with
                        | High => v_ty
                        | Medium => match c_ty c_ad with
                                 | High => x |-> High; v_ty
                                 | _ => v_ty
                                 end
                        | _ => match c_ty c_ad with
                                 | High => x |-> High; v_ty
                                 | Medium => x |-> Medium; v_ty
                                 | _ => match v_ty x with
                                        | Low => match tau x with
                                                 | Medium => x |-> Medium; v_ty
                                                 | _ => v_ty
                                                 end
                                        | _ => match tau x with
                                                 | Medium => x |-> Medium; v_ty
                                                 | _ => x |-> Low; v_ty
                                                 end
                                        end
                                 end
                        end  
               end            
   | _ => empty_ty
  end.

Definition update_type (ev : env) (ju : jud) (c : act) : vc_level :=
  update_type'(get_v_ty ev) (get_c_ty ev) (get_tau ju) c.

Fixpoint In (a:string) (l:list string) : bool :=
    match l with
      | [] => false
      | b :: m => if (eqb_string a b) then true else (In a m)
    end.

Definition update_v_l' (v_l: list string) (c : act): list string :=
  match c with
   | x ::= a => if (In x v_l) then v_l else x::v_l
   | a#c_ad? x => if (In x v_l) then v_l else x::v_l
   | _ => nil
  end.

Definition update_c_l' (c_l: list string) (c : act): list string :=
  match c with
   | x ::= a => if (In x c_l) then c_l else x::c_l
   | a#c_ad! w => if (In c_ad c_l) then c_l else c_ad::c_l
   | _ => nil
  end.

Definition update_v_l (ev : env) (c : act) : list string :=
  update_v_l' (get_v_l ev) c.

Definition update_c_l (ev : env) (c : act) : list string :=
  update_c_l' (get_c_l ev) c.

Definition update_i_h_l' (l: list string) (i i' : string): list string :=
  match In i l with
  | true => if In i' l then l else i'::l
  | false => if In i' l then i::l else i::i'::l
  end.

Definition update_i_l (ev : env) (c : act): list string :=
  match c with 
  | MOVEp(i)to(i') =>  update_i_h_l' (get_i_l ev) i i'
  | MOVEi(h)(i)to(h')(i') => update_i_h_l' (get_i_l ev) i i'
  | _ => get_i_l ev
 end.

Definition update_h_l (ev : env) (c : act): list string :=
  match c with 
  | MOVEi(h)(i)to(h')(i') => update_i_h_l' (get_h_l ev) h h'
  | _ => get_h_l ev
 end.

Fixpoint acal_l (a : aexp) (lv : vc_level) : list string :=
  match a with
  | ANum n => nil
  | AVars x => match lv x with
              | None => nil
              | _ => [x]
              end
  | ACH x => match lv x with
              | None => nil
              | _ => [x]
              end
  | APlus a1 a2 => (acal_l a1 lv) ++ (acal_l a2 lv)
  | AMinus a1 a2  => (acal_l a1 lv) ++ (acal_l a2 lv)
  | AMult a1 a2 => (acal_l a1 lv) ++ (acal_l a2 lv)
  | ADiv a1 a2 => (acal_l a1 lv) ++ (acal_l a2 lv)
  end.

Fixpoint bcal_l (b : bexp) (lv : vc_level) : list string :=
  match b with
  | BEq a1 a2   => (acal_l a1 lv) ++ (acal_l a2 lv)
  | BLe a1 a2   => (acal_l a1 lv) ++ (acal_l a2 lv)
  | BNot b1     => (bcal_l b1 lv)
  | BAnd b1 b2  => (bcal_l b1 lv) ++ (bcal_l b2 lv) 
  | _ => nil
  end.

Fixpoint update_tau' (v_ty c_ty tau : vc_level) (l:list string): vc_level :=
  match l with
    | [] => tau           
    | [a] => match v_ty a with 
            | High => match tau a with
                      | High => tau
                      | _ => a |-> High; tau
                      end
            | Medium => match tau a with
                      | High => tau
                      | Medium => tau
                      | _ => a |-> Medium; tau
                      end
            | Low => match tau a with
                      | None => a |-> Low; tau
                      | _ => tau
                     end
            | _  => match c_ty a with
                      | High => match tau a with
                               | High => tau
                               | _ => a |-> High; tau
                               end
                      | Medium => match tau a with
                               | High => tau
                               | Medium => tau
                               | _ => a |-> Medium; tau
                               end
                      | Low => match tau a with
                               | None => a |-> Low; tau
                               | _ => tau
                               end
                      | _ => tau
                      end
            end
    | a :: l => match v_ty a with 
            | High => match tau a with
                      | High => update_tau' v_ty c_ty tau l
                      | _ => a |-> High; update_tau' v_ty c_ty tau l
                      end
            | Medium => match tau a with
                      | High => update_tau' v_ty c_ty tau l
                      | Medium => update_tau' v_ty c_ty tau l
                      | _ => a |-> Medium; update_tau' v_ty c_ty tau l
                      end
            | Low => match tau a with
                      | None => a |-> Low; update_tau' v_ty c_ty tau l
                      | _ => update_tau' v_ty c_ty tau l
                     end
            | _ => match c_ty a with
                  | High =>  match tau a with
                               | High => update_tau' v_ty c_ty tau l
                               | _ => a |-> High; update_tau' v_ty c_ty tau l
                               end
                  | Medium => match tau a with
                               | High => update_tau' v_ty c_ty tau l
                               | Medium => update_tau' v_ty c_ty tau l
                               | _ => a |-> Medium; update_tau' v_ty c_ty tau l
                               end
                  | Low => match tau a with
                               | None => a |-> Low; update_tau' v_ty c_ty tau l
                               | _ => update_tau' v_ty c_ty tau l
                               end
                  | _ => update_tau' v_ty c_ty tau l
                  end
            end
  end.

Definition update_tau (ev : env) (ju : jud) (l:list string): jud :=
  Jud (update_tau' (get_v_ty ev) (get_c_ty ev) (get_tau ju) l) (get_omegaI ju) (get_omegaH ju).


Definition update_ins_ty' (i_ty omegaI : i_level) (i i' : string) : i_level :=
  match omegaI i with 
    | ins_1 => match i_ty i' with
              | ins_0 => match i_ty i with
                         | ins_1 => i_ty
                         | ins_2 => i |i|-> ins_2; i_ty
                         | _ => i |i|-> ins_1; i_ty
                         end                                 
              | ins_1 => match i_ty i with
                         | ins_1 => i_ty
                         | ins_2 => i |i|-> ins_2; i_ty
                         | _ => i |i|-> ins_1; i_ty
                         end
              | ins_2 => match i_ty i with 
                         | ins_2 => i_ty
                         | _ => i |i|-> ins_2; i_ty   
                         end
              | _ => match i_ty i with
                         | ins_0 => i |i|-> ins_1; i_ty  
                         | ins_none => i |i|-> ins_1; i_ty  
                         | _ => i_ty
                         end 
               end
    | ins_2 => match i_ty i with
              | ins_2 => i_ty
              | _ => i |i|-> ins_2; i_ty
              end        
    | _ => match i_ty i' with
              | ins_0 => match i_ty i with
                         | ins_0 => i_ty
                         | ins_1 => i |i|-> ins_1; i_ty
                         | ins_2 => i |i|-> ins_2; i_ty
                         | _ => i |i|-> ins_0; i_ty  
                         end                                 
              | ins_1 => match i_ty i with 
                         | ins_1 => i_ty
                         | ins_2 => i |i|-> ins_2; i_ty
                         | _ => i |i|-> ins_1; i_ty  
                         end
              | ins_2 => match i_ty i with 
                         | ins_2 => i_ty
                         | _ => i |i|-> ins_2; i_ty   
                         end
              | _ => match i_ty i with
                         | ins_none => i |i|-> ins_0; i_ty  
                         | _ => i_ty
                         end 
             end
  end.

Definition update_ins_ty (ev : env) (ju : jud) (c : act) : i_level :=
  match c with
   | MOVEp(i)to(i') =>  update_ins_ty' (get_i_ty ev) (get_omegaI ju) i i'
   | MOVEi(h)(i)to(h')(i') => update_ins_ty' (get_i_ty ev) (get_omegaI ju) i i'
   | _ => get_i_ty ev
  end. 

Definition update_hos_ty' (h_ty omegaH : h_level) (h h' : string) : h_level :=
  match omegaH h with 
    | hos_1 => match h_ty h' with
              | hos_0 => match h_ty h with
                         | hos_1 => h_ty
                         | hos_2 => h |h|-> hos_2; h_ty
                         | _ => h |h|-> hos_1; h_ty
                         end                                 
              | hos_1 => match h_ty h with
                         | hos_1 => h_ty
                         | hos_2 => h |h|-> hos_2; h_ty
                         | _ => h |h|-> hos_1; h_ty
                         end
              | hos_2 => match h_ty h with 
                         | hos_2 => h_ty
                         | _ => h |h|-> hos_2; h_ty   
                         end
              | _ => match h_ty h with
                         | hos_0 => h |h|-> hos_1; h_ty  
                         | hos_none => h |h|-> hos_1; h_ty  
                         | _ => h_ty
                         end 
               end
    | hos_2 => match h_ty h with
              | hos_2 => h_ty
              | _ => h |h|-> hos_2; h_ty
              end        
    | _ => match h_ty h' with
              | hos_0 => match h_ty h with
                         | hos_0 => h_ty
                         | hos_1 => h |h|-> hos_1; h_ty
                         | hos_2 => h |h|-> hos_2; h_ty
                         | _ => h |h|-> hos_0; h_ty  
                         end                                 
              | hos_1 => match h_ty h with 
                         | hos_1 => h_ty
                         | hos_2 => h |h|-> hos_2; h_ty
                         | _ => h |h|-> hos_1; h_ty  
                         end
              | hos_2 => match h_ty h with 
                         | hos_2 => h_ty
                         | _ => h |h|-> hos_2; h_ty   
                         end
              | _ => match h_ty h with
                         | hos_none => h |h|-> hos_0; h_ty  
                         | _ => h_ty
                         end 
             end
  end.

Definition update_hos_ty (ev : env) (ju : jud) (c : act) : h_level :=
  match c with
   | MOVEi(h)(i)to(h')(i') => update_hos_ty' (get_h_ty ev) (get_omegaH ju) h h'
   | _ => (get_h_ty ev)
  end. 

Definition update_c_i' (c_i : c_ins) (ins_id : string) (x : string) : c_ins :=
  match prefix "0x" x with 
  | true => if eqb_string ins_id (c_i x) then c_i else x |=> ins_id; c_i
  | false => c_i
  end.

Definition update_c_i (ev : env) (ins_id : string) (c : act) : c_ins :=
   match c with
   | x ::= a => update_c_i' (get_c_i ev) ins_id x 
   | a#c_ad! w => update_c_i' (get_c_i ev) ins_id c_ad 
   | _ => get_c_i ev
   end.

Fixpoint update_type_all (lv tau : vc_level) (list : list string): vc_level :=
  match list with
    | [] => empty_ty          
    | [a] => match lv a with 
            | High => lv
            | Medium => match tau a with
                      | High => a |-> High; lv
                      | _ => lv
                     end
            | _ => match tau a with
                      | High => a |-> High; lv
                      | Medium => a |-> Medium; lv
                      | _ => match lv a with
                             | Low => lv
                             | _ => a |-> Low; lv
                             end
                     end
            end
    | a :: l => match lv a with 
            | High => update_type_all lv tau l
            | Medium => match tau a with
                      | High => a |-> High; update_type_all lv tau l
                      | _ => update_type_all lv tau l
                     end
            | _ => match tau a with
                      | High => a |-> High; update_type_all lv tau l
                      | Medium => a |-> Medium; update_type_all lv tau l
                      | _ => match lv a with
                             | Low => update_type_all lv tau l
                             | _ => a |-> Low; update_type_all lv tau l
                             end
                     end           
            end
  end.

Definition update_type_all_s (ev : env) (ju : jud) : vc_level :=
  update_type_all (get_v_ty ev) (get_tau ju) (get_v_l ev).

Definition update_type_all_c (ev : env) (ju : jud) : vc_level :=
  update_type_all (get_c_ty ev) (get_tau ju) (get_c_l ev).

Fixpoint update_type_stop' (c_l : list string): vc_level :=
  match c_l with
    | [] => empty_ty          
    | [a] => a |-> Low          
    | a :: l => a |-> Low; update_type_stop' l        
  end.

Definition update_type_stop (ev : env) : vc_level :=
  update_type_stop' (get_c_l ev).

Fixpoint update_c_i_all' (c_i : c_ins) (c_l : list string) (ins_id : string): c_ins :=
  match c_l with
    | [] => empty_c_i         
    | [a] => a |=> ins_id
    | a :: l => a |=> ins_id; update_c_i_all' c_i l ins_id 
  end.

Definition update_c_i_all (ev : env) (ins_id : string) : c_ins :=
  update_c_i_all' (get_c_i ev) (get_c_l ev) ins_id.


Definition update_st (st st_v st_c : state) (x : string) (a : aexp): state :=
  (x !-> acal st_v st_c a ; st).

Definition update_st_v (ev : env) (x : string) (a : aexp) : state :=
   update_st (get_st_v ev) (get_st_v ev) (get_st_c ev) x a.

Definition update_st_c (ev : env) (x : string) (a : aexp) : state :=
   update_st (get_st_c ev) (get_st_v ev) (get_st_c ev) x a.

Definition Ins1 : string := "Instance_id_1".
Definition Ins2 : string := "Instance_id_2".

Definition Host1 : string := "Host_id_1".
Definition Host2 : string := "Host_id_2".

Definition Error_ev := 
  Env empty_ty empty_ty [Error] [Error] empty_c_i empty_ins_ty empty_host_ty [Error] [Error] empty_st empty_st.

Definition IsErrorEv (ev : env): bool :=
  match ev with
  | Env v_ty c_ty v_l c_l c_i 
        i_ty h_ty i_l h_l st_v st_c => match v_l with
                                            | [a] => eqb_string a Error
                                            | _ => false
                                            end
  end. 

Fixpoint acttype (ev : env) (ins_id : string) (c : act) (ju : jud) (s : nat): env :=
match s with
   | O => ev
   | S s1 => 
     if IsErrorEv ev then Error_ev
     else match c with
     | x ::= a =>  match prefix "0x" x with 
               | true => Env (get_v_ty ev) (update_type ev ju c) (get_v_l ev) (update_c_l ev c) (update_c_i ev ins_id c) 
                             (get_i_ty ev) (get_h_ty ev) (get_i_l ev) (get_h_l ev) 
                             (get_st_v ev) (update_st_c ev x a) 
               | false => Env (update_type ev ju c) (get_c_ty ev) (update_v_l ev c) (get_c_l ev)  (get_c_i ev) 
                              (get_i_ty ev) (get_h_ty ev) (get_i_l ev) (get_h_l ev)
                              (update_st_v ev x a) (get_st_c ev)
               end
     | c1;; c2 => let ev1 := acttype ev ins_id c1 ju s1 in acttype ev1 ins_id c2 ju s1
     | SKIP => ev
     | STOP =>  Env (get_v_ty ev) (update_type_stop ev) (get_v_l ev) (get_c_l ev) (get_c_i ev) 
                (get_i_ty ev) (get_h_ty ev) (get_i_l ev) (get_h_l ev) 
                (get_st_v ev) empty_st
     | MOVEp(i)to(i') => Env (update_type_all_s ev ju) (update_type_all_c ev ju) (get_v_l ev) (get_c_l ev) (update_c_i_all ev i') 
                          (update_ins_ty ev ju c) (get_h_ty ev) (update_i_l ev c) (get_h_l ev) 
                          (get_st_v ev) (get_st_c ev)
     | MOVEi(h)(i)to(h')(i') => Env (update_type_all_s ev ju) (update_type_all_c ev ju) (get_v_l ev) (get_c_l ev) (update_c_i_all ev i') 
                                 (update_ins_ty ev ju c)  (update_hos_ty ev ju c) (update_i_l ev c) (update_h_l ev c) 
                                 (get_st_v ev) (get_st_c ev)
     | SLEEP t => ev  
     | IFB b THEN c1 ELSE c2 END => match bcal (get_st_v ev) (get_st_c ev) b with 
                                | true => acttype ev ins_id c1 (update_tau ev ju (bcal_l b (get_v_ty ev) ++ bcal_l b (get_c_ty ev))) s1
                                | false => acttype ev ins_id c2 (update_tau ev ju (bcal_l b (get_v_ty ev) ++ bcal_l b (get_c_ty ev))) s1
                                end
     | ch#ad! a => Env (get_v_ty ev) (update_type ev ju c) (get_v_l ev) (update_c_l ev c) (update_c_i ev ins_id c) 
                     (get_i_ty ev) (get_h_ty ev) (get_i_l ev) (get_h_l ev)
                     (get_st_v ev) (update_st_c ev ad a) 
     | ch#ad? x => match acal (get_st_v ev) (get_st_c ev) (ACH ad) with
                | 0 => Error_ev 
                | _ => Env (update_type ev ju c) (get_c_ty ev) (update_v_l ev c) (get_c_l ev) (get_c_i ev)
                           (get_i_ty ev) (get_h_ty ev)(get_i_l ev) (get_h_l ev) 
                           (update_st_v ev x (ACH ad)) (get_st_c ev) 
                end
     | WHILE b DO c1 END => match bcal (get_st_v ev) (get_st_c ev) b with 
                        | true => let ev1 := acttype ev ins_id c1 (update_tau ev ju (bcal_l b (get_v_ty ev) ++ bcal_l b (get_c_ty ev))) s1 in 
                                  acttype ev1 ins_id c (update_tau ev ju (bcal_l b (get_v_ty ev) ++ bcal_l b (get_c_ty ev))) s1 
                        | false => ev
                        end  
     | c1//c2 => let ev1 := acttype ev ins_id c1 ju s1 in acttype ev1 ins_id c2 ju s1
end
 end.  

Definition MaxStep : nat := 20.

Notation " '|-' ( ev ) ':' '[' ins_id ']' ( c ) '\IN' ( ju )" :=
   (acttype ev ins_id c ju MaxStep) (at level 90, right associativity).

Axiom Cpar_eq1 : forall (c1 c2 : act),
(c1 // c2) = (c2 // c1).

Axiom Cpar_eq2 : forall (c1 c2 c3: act),
(c1 // c2 // c3) = (c2 // c1 // c3).

Definition eqb_ty (a b : ty) : bool :=
   match a with
      | High => match b with
                | High => true
                | _ => false
                end
      | Medium => match b with
                | Medium => true
                | _ => false
                end
      | Low => match b with
                | Low => true
                | _ => false
                end
      | None => match b with
                | None => true
                | _ => false
                end
end.

Fixpoint check_ty (lv tau : vc_level) (list : list string) : bool :=
  match list with
    | [] => true         
    | [a] => eqb_ty (lv a) (tau a)            
    | a :: l => match eqb_ty (lv a) (tau a) with
                | true => check_ty lv tau l
                | false => false
                end
  end.

Definition eqb_ins_ty (a b : ins_ty) : bool :=
   match a with
      | ins_0 => match b with
                | ins_0 => true
                | _ => false
                end
      | ins_1 => match b with
                | ins_1 => true
                | _ => false
                end
      | ins_2 => match b with
                | ins_2 => true
                | _ => false
                end
      | ins_none => match b with
                | ins_none => true
                | _ => false
                end
end.

Fixpoint check_ins_ty (i_ty omegal: i_level) (list : list string) : bool :=
  match list with
    | [] => true         
    | [a] => eqb_ins_ty (i_ty a) (omegal a)            
    | a :: l => match eqb_ins_ty (i_ty a) (omegal a) with
                | true => check_ins_ty i_ty omegal l
                | false => false
                end
  end.

Definition eqb_hos_ty (a b : hos_ty) : bool :=
   match a with
      | hos_0 => match b with
                | hos_0 => true
                | _ => false
                end
      | hos_1 => match b with
                | hos_1 => true
                | _ => false
                end
      | hos_2 => match b with
                | hos_2 => true
                | _ => false
                end
      | hos_none => match b with
                | hos_none => true
                | _ => false
                end
end.

Fixpoint check_hos_ty (h_ty omegaH: h_level) (list : list string) : bool :=
  match list with
    | [] => true         
    | [a] => eqb_hos_ty (h_ty a) (omegaH a)            
    | a :: l => match eqb_hos_ty (h_ty a) (omegaH a) with
                | true => check_hos_ty h_ty omegaH l
                | false => false
                end
  end.

Fixpoint repeat_assign (st : state)(x : string) (v n: nat): state :=
  match n with
   | O => st
   | S n' => let st1 := (x !-> v ; st) in
                repeat_assign st1 x v n'           
  end.

Definition Check_type_judgement (ev : env) (ju : jud) : bool :=
  check_ty (get_v_ty ev) (get_tau ju) (get_v_l ev) && check_ty (get_c_ty ev) (get_tau ju) (get_c_l ev)
  && check_ins_ty (get_i_ty ev)(get_omegaI ju) (get_i_l ev)
  && check_hos_ty (get_h_ty ev)(get_omegaH ju) (get_h_l ev).

Fixpoint check_process_no_rec (ev : env) (c : act) : bool :=
    match c with
  | a#c_ad? x => match acal (get_st_v ev) (get_st_c ev) (ACH c_ad) with
                | 0 => false
                | _ => true
                end
  | c1;; c2 => check_process_no_rec ev c1 && check_process_no_rec ev c2
  | IFB b THEN c1 ELSE c2 END => check_process_no_rec ev c1 && check_process_no_rec ev c2
  | WHILE b DO c END => check_process_no_rec ev c
  | c1//c2 => check_process_no_rec ev c1 && check_process_no_rec ev c2
  | _ => true
end.


(* Only the right side has a receiving action in parallel processes_1 *)
Axiom Cpar_right_yes_1 : forall (p q q' : act) (ev ev': env)  (ins : string) (ju : jud) (a : channel) (c_ad x : string),
  check_process_no_rec ev p = true ->
  check_process_no_rec ev q = true ->
  |- ( ev ) : [ ins ] ( p//q ) \IN ( ju ) = ev' ->
  |- ( ev ) : [ ins ] ( p//q;; (a#c_ad? x) ;; q' ) \IN ( ju ) =
    |- ( ev' ) : [ ins ] ( (a#c_ad? x) ;; q' ) \IN ( ju ).

(* Only the right side has a receiving action in parallel processes_2 *)
Axiom Cpar_right_yes_2 : forall (p q' : act) (ev ev': env)  (ins : string) (ju : jud) (a : channel) (c_ad x : string),
  check_process_no_rec ev p = true ->
  |- ( ev ) : [ ins ] ( p ) \IN ( ju ) = ev' ->
  |- ( ev ) : [ ins ] ( p//(a#c_ad? x) ;; q' ) \IN ( ju ) =
    |- ( ev' ) : [ ins ] ( (a#c_ad? x) ;; q' ) \IN ( ju ).

(* Both sides have receiving actions in parallel processes_1 *)
Axiom Cpar_both_yes_1 : forall (p p' q q' : act) (ev ev': env)  (ins : string) (ju : jud) (a1 a2 : channel) (c_ad1 x1 c_ad2 x2: string),
  check_process_no_rec ev p = true ->
  check_process_no_rec ev q = true ->
  |- ( ev ) : [ ins ] ( p//q ) \IN ( ju ) = ev' ->
  |- ( ev ) : [ ins ] ( p;; (a1#c_ad1? x1);; p'//q;; (a2#c_ad2? x2);; q' ) \IN ( ju ) =
    |- ( ev' ) : [ ins ] ( (a1#c_ad1? x1);; p'//(a2#c_ad2? x2);; q' ) \IN ( ju ).

(* Both sides have receiving actions in parallel processes_2 *)
Axiom Cpar_both_yes_2 : forall (p p' q' : act) (ev ev': env)  (ins : string) (ju : jud) (a1 a2 : channel) (c_ad1 x1 c_ad2 x2: string),
  check_process_no_rec ev p = true ->
  |- ( ev ) : [ ins ] ( p ) \IN ( ju ) = ev' ->
  |- ( ev ) : [ ins ] ( p;; (a1#c_ad1? x1);; p'//(a2#c_ad2? x2);; q' ) \IN ( ju ) =
    |- ( ev' ) : [ ins ] ( (a1#c_ad1? x1);; p'//(a2#c_ad2? x2);; q' ) \IN ( ju ).

(* Perform parallel processes step by step *)
Axiom Cpar_step : forall (p q: act) (ev ev': env) (ins : string) (ju : jud) ,
  check_process_no_rec ev p = true ->
  |- ( ev ) : [ ins ] ( p ) \IN ( ju ) = ev' ->
  |- ( ev ) : [ ins ] ( p // q ) \IN ( ju ) =
    |- ( ev' ) : [ ins ] ( q ) \IN ( ju ).


(* Test Examples *)


Definition empty_ev := 
  Env empty_ty empty_ty nil nil empty_c_i (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] empty_st empty_st.

Definition empty_ev' := 
  Env empty_ty empty_ty nil nil empty_c_i 
      (Ins1 |i|-> ins_0; Ins2 |i|-> ins_1) (Host1 |h|-> hos_0; Host2 |h|-> hos_1) 
      [Ins1;Ins2] [Host1;Host2]  empty_st empty_st.

Definition tau' := Y |-> Low; Z |-> Low; X |-> High; "0x21d36e0"%string |-> High.
Definition ju' := Jud tau' empty_ins_ty empty_host_ty.
Definition omegaI' := Ins1 |i|-> ins_2.
Definition omegaH' := Host1 |h|-> hos_2.
Definition ju := Jud tau' omegaI' omegaH'.

Definition list' := [Z;Y;"0x21d36e0"%string].
Definition v_ty' := Y |-> High; X |-> Low; Z |-> Low.
Definition c_ty' := "0x21d36e0" |-> High.
Definition tao' := Z |-> High.

Definition i_ty := Ins1 |i|-> ins_0; Ins2 |i|-> ins_1.
Definition i_id' := "0x21d36e0" |=> Ins1.

Example test_example_0:
  |- (empty_ev) : [Ins1](X ::= 0 ;; SKIP // Z ::= 2) \IN (ju') = 
  Env (Z |-> Low; X |-> High) empty_ty [ Z ; X ] nil empty_c_i 
      (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (Z !-> 2; X !-> 0) empty_st.
Proof.
  unfold acttype. simpl. 
  reflexivity. Qed.

Example test_example_1:
  |- (empty_ev) : [Ins1](X ::= 0;; "0x21d36e0" ::= 1;; Y ::= X) \IN (ju') = 
  Env (Y |-> High; X |-> High) ("0x21d36e0" |-> High) [ Y ; X ] ["0x21d36e0"%string] ("0x21d36e0" |=> Ins1) 
      (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (Y !-> 0 ; X !-> 0) ("0x21d36e0" !-> 1).
Proof. 
  reflexivity. Qed.

Example test_example_2:
  |- (empty_ev) : [Ins1](SLEEP 1 ;; X ::= 0;; "0x21d36e0" ::= 1) \IN (ju') = 
  Env (X |-> High) ("0x21d36e0" |-> High) [ X ] ["0x21d36e0"%string] ("0x21d36e0" |=> Ins1)
      (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (X !-> 0) ("0x21d36e0" !-> 1).
Proof. 
   reflexivity. Qed.

Example test_example_3:
  |- (empty_ev) : [Ins1](X ::= 3;; IFB X = 1 THEN Z ::= 0;; "0x21d36e0" ::= 1 ELSE Z ::= 2 END) \IN (ju') = 
  Env (Z |-> Low; X |-> High) empty_ty [ Z; X ] nil empty_c_i
       (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (Z !-> 2 ; X !-> 3) empty_st.
Proof.
  reflexivity. Qed.

Example test_example_4:
  |- (empty_ev) : [Ins1](X ::= 1;; Z ::= 2;; (CH 0#"0x21d36e0" ! Z + X)) \IN (ju') = 
  Env  (Z |-> Low; X |-> High) ("0x21d36e0" |-> High) [ Z; X ] ["0x21d36e0"%string] ("0x21d36e0" |=> Ins1) 
       (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (Z !-> 2 ; X !-> 1) ("0x21d36e0" !-> 3).
Proof.
  reflexivity. Qed.

Example test_example_5:
  |- (empty_ev) : [Ins1]("0x21d36e0" ::= 3;; (CH 0#"0x21d36e0" ? Y)) \IN (ju') = 
  Env  (Y |-> High) ("0x21d36e0" |-> High) [ Y ] ["0x21d36e0"%string] ("0x21d36e0" |=> Ins1)
       (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (Y !-> 3) ("0x21d36e0" !-> 3).
Proof.
  reflexivity. Qed.

Example test_example_6:
  |- (empty_ev) : [Ins1]((CH 0#"0x21d36e0" ? Y);; SKIP// X ::= 1;; (CH 0#"0x21d36e0" ! X)) \IN (ju') = 
  Env (Y |-> High; X |-> High) ("0x21d36e0" |-> High) [ Y; X ] ["0x21d36e0"%string] ("0x21d36e0" |=> Ins1)
     (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (Y !-> 1 ; X !-> 1) ("0x21d36e0" !-> 1).
Proof.
  rewrite Cpar_eq1. reflexivity. Qed.

Definition while_test : act :=
  (X ::= 1;;
  Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END).

Example test_example_7:
  |- (empty_ev) : [Ins1](while_test) \IN (ju') = 
  Env (Y |-> High; Y |-> Low; Z |-> High; X |-> High) empty_ty [ Y; Z; X ] nil empty_c_i 
      (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (Z !-> 0; Y !-> 1; Y !-> 1; Z !-> 1; X !-> 1) empty_st.
Proof.
  reflexivity. 
Qed.




Definition R' : act :=
  (WHILE true DO
    X ::= 1
  END).

Example test_example_8:
 |- (empty_ev) : [Ins1](R') \IN (ju') =  
 Env (X |-> High) empty_ty [ X ] nil empty_c_i 
      (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (repeat_assign empty_st X 1 (MaxStep-1)) empty_st.
Proof.

  reflexivity. Qed.



Definition v_ty'' := Y |-> Low; X |-> Low; Z |-> Low.
Definition c_ty'' := "0x21d36e0" |-> Low; "0x21d3fff"%string |-> Low.
Definition list_v'' := [ Y; X ].
Definition list_c'' := ["0x21d36e0"%string; "0x21d3fff"%string].

Definition empty_ev'' := 
  Env v_ty'' c_ty'' list_v'' list_c''  ("0x21d36e0"%string |=> Ins1;"0x21d3fff"%string |=> Ins1)
      (Ins1 |i|-> ins_0; Ins2 |i|-> ins_1) (Host1 |h|-> hos_0; Host2 |h|-> hos_1) [Ins1;Ins2] [Host1;Host2] empty_st empty_st.

Example test_example_9:
  |- (empty_ev'') : [Ins1](MOVEp(Ins1)to(Ins2)) \IN (ju) = 
  Env (X |-> High;v_ty'') ("0x21d36e0" |-> High;c_ty'') list_v'' list_c'' ("0x21d36e0"%string |=> Ins2;"0x21d3fff"%string |=> Ins2) 
      (Ins1 |i|-> ins_2; Ins1 |i|-> ins_0; Ins2 |i|-> ins_1) (Host1 |h|-> hos_0; Host2 |h|-> hos_1) [Ins1;Ins2] [Host1;Host2] empty_st empty_st.
Proof.
  reflexivity. Qed.
Definition ev_1 := |- (empty_ev'') : [Ins1](SKIP) \IN (ju).

Example test_example_10:
  |- (empty_ev'') : [Ins1](MOVEi(Host1)(Ins1)to(Host2)(Ins2)) \IN (ju) = 
  Env (X |-> High;v_ty'') ("0x21d36e0" |-> High;c_ty'') list_v'' list_c'' ("0x21d36e0"%string |=> Ins2;"0x21d3fff"%string |=> Ins2) 
      (Ins1 |i|-> ins_2; Ins1 |i|-> ins_0; Ins2 |i|-> ins_1) (Host1 |h|-> hos_2; Host1 |h|-> hos_0; Host2 |h|-> hos_1) [Ins1;Ins2] [Host1;Host2] empty_st empty_st.
Proof.
    reflexivity. Qed.

Example test_example_11:
  |- (empty_ev) : [Ins1](Y ::= 1;; (CH 0#"0x21d3fff" ! Y);; SKIP//X ::= 2;; Y ::= X;; (CH 0#"0x21d3fff" ! Y);; SKIP) \IN (ju') = 
  Env (Y |-> High; X |-> High; Y |-> Low) ("0x21d3fff" |-> High; "0x21d3fff" |-> Low) [ X; Y ] ["0x21d3fff"%string] ("0x21d3fff" |=> Ins1) 
      (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] (Y !-> 2; X !-> 2; Y !-> 1) ("0x21d3fff" !-> 2; "0x21d3fff" !-> 1).
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

Definition tau_1 := X |-> High; Y |-> High; M1 |-> Medium; M2 |-> Medium; Z |-> Low; "0x21d36e0"%string |-> High; "0x21d3fff"%string |-> Medium.
Definition ju_1 := Jud tau_1 (Ins1 |i|-> ins_0; Ins2 |i|-> ins_0) (Host1 |h|-> hos_0).

Example paper_example_0:
  Check_type_judgement (|- (empty_ev) : [Ins1](P;;Q) \IN (ju_1)) ju_1 = true.
Proof.
   reflexivity.
Qed.

Example paper_example_1:
  Check_type_judgement (|- (empty_ev) : [Ins1](P;;R;;Q;;Q1;;P1;;P2) \IN (ju_1)) ju_1 = false.
Proof.
  reflexivity.
Qed.

Example paper_new_example_1_err:
  |- (empty_ev) : [Ins1]((P;;P1;;P2)//
                         (Q;;Q1)) \IN (ju_1) =
  Error_ev.
Proof.
  unfold acttype. simpl.
  reflexivity. Qed.

Definition mid_ev_1 := Env (X |-> High) ("0x21d36e0" |-> High) [X] ["0x21d36e0"%string] ("0x21d36e0" |=> Ins1) (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1] 
  (X !-> 1) ("0x21d36e0" !-> 1).
Definition mid_ev_2 := Env (M1 |-> High; Y |-> High; X |-> High) ("0x21d3fff" |-> High; "0x21d36e0" |-> High) [M1; Y; X] ["0x21d3fff"%string; "0x21d36e0"%string]
  ("0x21d3fff" |=> Ins1; "0x21d36e0" |=> Ins1) (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1]
  (M1 !-> 1; Y !-> 1; X !-> 1)
  ("0x21d3fff" !->1; "0x21d36e0" !-> 1).
Definition mid_ev_3 := Env (M |-> High; M2 |-> High; M1 |-> High; Y |-> High; X |-> High) ("0x21d3fff" |-> High; "0x21d36e0" |-> High) [M; M2; M1; Y; X] ["0x21d3fff"%string; "0x21d36e0"%string]
  ("0x21d3fff" |=> Ins1; "0x21d36e0" |=> Ins1) (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1]
  (M !-> 2; M2 !-> 1; M1 !-> 1; Y !-> 1; X !-> 1)
  ("0x21d3fff" !->1; "0x21d36e0" !-> 1).



Example paper_new_example_1:
  |- (empty_ev) : [Ins1]((P;;P1;;P2)//
                         (Q;;Q1)) \IN (ju_1) =
  Env (M |-> High; M2 |-> High; M1 |-> High; Y |-> High; X |-> High) ("0x21d3fff" |-> High; "0x21d36e0" |-> High) [M; M2; M1; Y; X]
  ["0x21d3fff"%string; "0x21d36e0"%string] ("0x21d3fff" |=> Ins1; "0x21d36e0" |=> Ins1) (Ins1 |i|-> ins_0) (Host1 |h|-> hos_0) [Ins1] [Host1]
  (M !->2; M2 !-> 1; M1 !-> 1; Y !-> 1; X !-> 1) ("0x21d3fff" !-> 1; "0x21d36e0" !-> 1).
Proof.
  assert (HM1: |- (empty_ev) : [Ins1]((P;;P1;;P2)//(Q;;Q1)) \IN (ju_1) =
   |- (mid_ev_1) : [Ins1]((P1;;P2)//(Q;;Q1)) \IN (ju_1)).
  { apply Cpar_both_yes_2; reflexivity. }
  rewrite HM1. rewrite Cpar_eq1.
  assert (HM2: |- (mid_ev_1) : [Ins1]((Q;;Q1)//(P1;;P2)) \IN (ju_1) =
    |- (mid_ev_2) : [Ins1](P1;;P2) \IN (ju_1)).
  { apply Cpar_right_yes_2; reflexivity. }
  rewrite HM2. reflexivity. Qed.

Example paper_new_example_1'_err:
  |- (empty_ev) : [Ins1]((P;;P1;;P2)//
                         (Q;;Q1)//R) \IN (ju_1) =
  Error_ev.
Proof.
  reflexivity. Qed.

Example paper_new_example_1':
  |- (empty_ev) : [Ins1]((P;;P1;;P2)//
                         (Q;;Q1)//R) \IN (ju_1) =
  Env (Z |-> High; M |-> High; M2 |-> High; M1 |-> High; Y |-> High; X |-> High) ("0x21d3fff" |-> High; "0x21d36e0" |-> High) 
  [Z; M; M2; M1; Y; X] ["0x21d3fff"%string; "0x21d36e0"%string] ("0x21d3fff" |=> Ins1; "0x21d36e0" |=> Ins1) (Ins1 |i|-> ins_0) 
  (Host1 |h|-> hos_0) [Ins1] [Host1]
  (repeat_assign (M !-> 2; M2 !-> 1; M1 !-> 1; Y !-> 1; X !-> 1) Z 1 (MaxStep-1)) ("0x21d3fff" !-> 1; "0x21d36e0" !-> 1).
Proof.
  assert (HM1: |- (empty_ev) : [Ins1]((P;;P1;;P2)//(Q;;Q1)//R) \IN (ju_1) =
   |- (mid_ev_1) : [Ins1]((P1;;P2)//(Q;;Q1)//R) \IN (ju_1)).
  { apply (@Cpar_both_yes_2 P P2 (Q1//R) empty_ev mid_ev_1 Ins1 ju_1 (CH 1) (CH 0) "0x21d3fff" M2 "0x21d36e0" Y); reflexivity. }
  rewrite HM1. 
  assert (HM2: ((P1;;P2)//(Q;;Q1)//R) = (Q;;Q1//P1;;P2//R)).
  { apply Cpar_eq2. }
  rewrite HM2.
  assert (HM3: |- (mid_ev_1) : [Ins1]((Q;;Q1)//(P1;;P2)//R) \IN (ju_1) =
    |- (mid_ev_2) : [Ins1]((P1;;P2)//R) \IN (ju_1)).
    { apply Cpar_step;reflexivity. }
  rewrite HM3.
  assert (HM4: |- (mid_ev_2) : [Ins1]((P1;;P2)//R) \IN (ju_1) = 
  |- (mid_ev_3) : [Ins1](R) \IN (ju_1)).
  { apply Cpar_step;reflexivity.  }
  rewrite HM4.  
  reflexivity. Qed.

Definition final_ev := Env (Z |-> High; M |-> High; M2 |-> High; M1 |-> High; Y |-> High; X |-> High) ("0x21d3fff" |-> High; "0x21d36e0" |-> High) 
  [Z; M; M2; M1; Y; X] ["0x21d3fff"%string; "0x21d36e0"%string] ("0x21d3fff" |=> Ins1; "0x21d36e0" |=> Ins1) (Ins1 |i|-> ins_0) 
  (Host1 |h|-> hos_0) [Ins1] [Host1]
  (repeat_assign (M !-> 2; M2 !-> 1; M1 !-> 1; Y !-> 1; X !-> 1) Z 1 (MaxStep-1)) ("0x21d3fff" !-> 1; "0x21d36e0" !-> 1).

Example check_paper_new_example_1':
  Check_type_judgement final_ev ju_1 = false.
Proof.
  reflexivity.
Qed.
