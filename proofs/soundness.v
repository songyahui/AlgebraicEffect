Module AST.

Require Import FunInd.
From Coq Require Import Arith Bool Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Plus.

Definition numEvent := 10.


Inductive contEff : Type :=
| bot
| emp
| underline
| event      (s:string) (arg:nat)
| notEvent   (s:string) (arg:nat)
| placeHolder(s:string) (arg:nat)
| cons       (es1: contEff) (es2: contEff)
| disj       (es1: contEff) (es2: contEff)
| kleene     (es: contEff).

Inductive expression : Type :=
| nothingE
| pauseE
| emitE     (s:string)
| localDelE (s:string)  (e:expression)
| seqE      (e1:expression) (e2:expression)
| parE      (e1:expression) (e2:expression)
| ifElseE   (s:string) (e1:expression) (e2:expression)
| loopE     (e:expression)
(*| suspendE  (e:expression) (s:string)*)
| asyncE    (e:expression) (s:string)
| awaitE    (s:string)
| raiseE    (n:nat)
| trycatchE (e:expression) (handler:expression)
.
(*

differnce: sync - presnet valid for one time cycle 
           async- manuelly turn off the present signals.
*)


(* last argument is the completion code true -> normal, flase -> not completed*)
Definition state : Type := (syncEff * (option instance) * nat).

Definition states : Type := list state.


Notation "'_|_'" := bot (at level 0, right associativity).

Notation "'ϵ'" := emp (at level 0, right associativity).

Notation "+ A" := (A, one) (at level 0, right associativity).

Notation "! A" := (A, zero) (at level 0, right associativity).

Notation "'{{' Eff '}}'" := (singleton Eff) (at level 100, right associativity).

Notation " I1  @  I2 " := (cons I1 I2) (at level 100, right associativity).

Notation " I1  'or'  I2 " := (disj I1 I2) (at level 100, right associativity).

Notation " I1  '//'  I2 " := (parEff I1 I2) (at level 100, right associativity).

Notation "'star' I" := (kleene I) (at level 200, right associativity).



Notation "'nothing'" := nothingE (at level 200, right associativity).

Notation "'pause'" := pauseE (at level 200, right associativity).

Notation "'emit' A" := (emitE A) (at level 200, right associativity).

Notation "'signal' A 'in' E" := (localDelE A E)  (at level 200, right associativity).

Notation "E1 ; E2" := (seqE E1 E2)  (at level 200, right associativity).

Notation "'fork' E1 'par' E2" := (parE E1 E2)  (at level 80, right associativity).

Notation "'present' A 'then' E1 'else' E2" := (ifElseE A E1 E2)  (at level 200, right associativity).
Notation "'loop' E" := (loopE E) (at level 200, right associativity).

(*
Notation "'suspend' E 'when' S" := (suspendE E S) (at level 200, right associativity).
*)

Notation "'async' E 'with' S" := (asyncE E S) (at level 200, right associativity).

Notation "'await' S" := (awaitE S) (at level 200, right associativity).

Notation "'raise' N" := (raiseE N) (at level 200, right associativity).

Notation "'trap' E1 'catchwith' E2" := (trycatchE E1 E2) (at level 200, right associativity).